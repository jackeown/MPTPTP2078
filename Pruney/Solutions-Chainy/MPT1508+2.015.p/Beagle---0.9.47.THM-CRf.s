%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 254 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   37
%              Number of atoms          :  310 (1102 expanded)
%              Number of equality atoms :   23 ( 100 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r3_lattice3(A,B,C) )
               => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_99,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_61,axiom,(
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

tff(f_43,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r4_lattice3(A,B,C) )
             => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    k16_lattice3('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    ! [A_51,B_63,C_69] :
      ( r3_lattice3(A_51,'#skF_4'(A_51,B_63,C_69),C_69)
      | k16_lattice3(A_51,C_69) = B_63
      | ~ r3_lattice3(A_51,B_63,C_69)
      | ~ m1_subset_1(B_63,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v4_lattice3(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_51,B_63,C_69] :
      ( m1_subset_1('#skF_4'(A_51,B_63,C_69),u1_struct_0(A_51))
      | k16_lattice3(A_51,C_69) = B_63
      | ~ r3_lattice3(A_51,B_63,C_69)
      | ~ m1_subset_1(B_63,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v4_lattice3(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [D_50,B_46,C_47] :
      ( r2_hidden(D_50,a_2_1_lattice3(B_46,C_47))
      | ~ r3_lattice3(B_46,D_50,C_47)
      | ~ m1_subset_1(D_50,u1_struct_0(B_46))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_97,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_2'(A_109,B_110,C_111),C_111)
      | r4_lattice3(A_109,B_110,C_111)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l3_lattices(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_45,B_46,C_47] :
      ( '#skF_3'(A_45,B_46,C_47) = A_45
      | ~ r2_hidden(A_45,a_2_1_lattice3(B_46,C_47))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_467,plain,(
    ! [A_199,B_200,B_201,C_202] :
      ( '#skF_3'('#skF_2'(A_199,B_200,a_2_1_lattice3(B_201,C_202)),B_201,C_202) = '#skF_2'(A_199,B_200,a_2_1_lattice3(B_201,C_202))
      | ~ l3_lattices(B_201)
      | v2_struct_0(B_201)
      | r4_lattice3(A_199,B_200,a_2_1_lattice3(B_201,C_202))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l3_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_97,c_22])).

tff(c_20,plain,(
    ! [B_46,A_45,C_47] :
      ( r3_lattice3(B_46,'#skF_3'(A_45,B_46,C_47),C_47)
      | ~ r2_hidden(A_45,a_2_1_lattice3(B_46,C_47))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1('#skF_3'(A_45,B_46,C_47),u1_struct_0(B_46))
      | ~ r2_hidden(A_45,a_2_1_lattice3(B_46,C_47))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_168,plain,(
    ! [A_148,B_149,D_150,C_151] :
      ( r1_lattices(A_148,B_149,D_150)
      | ~ r2_hidden(D_150,C_151)
      | ~ m1_subset_1(D_150,u1_struct_0(A_148))
      | ~ r3_lattice3(A_148,B_149,C_151)
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l3_lattices(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    ! [A_152,B_153] :
      ( r1_lattices(A_152,B_153,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_152))
      | ~ r3_lattice3(A_152,B_153,'#skF_7')
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l3_lattices(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_46,c_168])).

tff(c_183,plain,(
    ! [B_153] :
      ( r1_lattices('#skF_5',B_153,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_153,'#skF_7')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_181])).

tff(c_186,plain,(
    ! [B_153] :
      ( r1_lattices('#skF_5',B_153,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_153,'#skF_7')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_183])).

tff(c_188,plain,(
    ! [B_154] :
      ( r1_lattices('#skF_5',B_154,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_154,'#skF_7')
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_186])).

tff(c_200,plain,(
    ! [A_45,C_47] :
      ( r1_lattices('#skF_5','#skF_3'(A_45,'#skF_5',C_47),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_45,'#skF_5',C_47),'#skF_7')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_5',C_47))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_188])).

tff(c_214,plain,(
    ! [A_45,C_47] :
      ( r1_lattices('#skF_5','#skF_3'(A_45,'#skF_5',C_47),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_45,'#skF_5',C_47),'#skF_7')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_5',C_47))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_225,plain,(
    ! [A_158,C_159] :
      ( r1_lattices('#skF_5','#skF_3'(A_158,'#skF_5',C_159),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_158,'#skF_5',C_159),'#skF_7')
      | ~ r2_hidden(A_158,a_2_1_lattice3('#skF_5',C_159)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_214])).

tff(c_232,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_5','#skF_3'(A_45,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_225])).

tff(c_237,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_5','#skF_3'(A_45,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_232])).

tff(c_238,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_5','#skF_3'(A_45,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_237])).

tff(c_474,plain,(
    ! [A_199,B_200] :
      ( r1_lattices('#skF_5','#skF_2'(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l3_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_238])).

tff(c_494,plain,(
    ! [A_199,B_200] :
      ( r1_lattices('#skF_5','#skF_2'(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_199,B_200,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l3_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_474])).

tff(c_517,plain,(
    ! [A_207,B_208] :
      ( r1_lattices('#skF_5','#skF_2'(A_207,B_208,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_207,B_208,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_207,B_208,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l3_lattices(A_207)
      | v2_struct_0(A_207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_494])).

tff(c_530,plain,(
    ! [A_209,B_210] :
      ( r1_lattices('#skF_5','#skF_2'(A_209,B_210,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_209,B_210,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l3_lattices(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_14,c_517])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_534,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_530,c_12])).

tff(c_537,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_534])).

tff(c_538,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_537])).

tff(c_40,plain,(
    ! [A_80,C_86,B_84] :
      ( k15_lattice3(A_80,C_86) = B_84
      | ~ r4_lattice3(A_80,B_84,C_86)
      | ~ r2_hidden(B_84,C_86)
      | ~ m1_subset_1(B_84,u1_struct_0(A_80))
      | ~ l3_lattices(A_80)
      | ~ v4_lattice3(A_80)
      | ~ v10_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_540,plain,
    ( k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_538,c_40])).

tff(c_543,plain,
    ( k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_540])).

tff(c_544,plain,
    ( k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_543])).

tff(c_545,plain,(
    ~ r2_hidden('#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_567,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_545])).

tff(c_570,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_567])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_570])).

tff(c_573,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_38,plain,(
    ! [A_73,B_77,C_79] :
      ( r3_lattices(A_73,B_77,k15_lattice3(A_73,C_79))
      | ~ r2_hidden(B_77,C_79)
      | ~ m1_subset_1(B_77,u1_struct_0(A_73))
      | ~ l3_lattices(A_73)
      | ~ v4_lattice3(A_73)
      | ~ v10_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_597,plain,(
    ! [B_77] :
      ( r3_lattices('#skF_5',B_77,'#skF_6')
      | ~ r2_hidden(B_77,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_38])).

tff(c_601,plain,(
    ! [B_77] :
      ( r3_lattices('#skF_5',B_77,'#skF_6')
      | ~ r2_hidden(B_77,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_597])).

tff(c_604,plain,(
    ! [B_216] :
      ( r3_lattices('#skF_5',B_216,'#skF_6')
      | ~ r2_hidden(B_216,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_601])).

tff(c_619,plain,(
    ! [D_50] :
      ( r3_lattices('#skF_5',D_50,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_50,'#skF_7')
      | ~ m1_subset_1(D_50,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_604])).

tff(c_627,plain,(
    ! [D_50] :
      ( r3_lattices('#skF_5',D_50,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_50,'#skF_7')
      | ~ m1_subset_1(D_50,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_619])).

tff(c_629,plain,(
    ! [D_217] :
      ( r3_lattices('#skF_5',D_217,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_217,'#skF_7')
      | ~ m1_subset_1(D_217,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_627])).

tff(c_633,plain,(
    ! [B_63,C_69] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_63,C_69),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_63,C_69),'#skF_7')
      | k16_lattice3('#skF_5',C_69) = B_63
      | ~ r3_lattice3('#skF_5',B_63,C_69)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_629])).

tff(c_651,plain,(
    ! [B_63,C_69] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_63,C_69),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_63,C_69),'#skF_7')
      | k16_lattice3('#skF_5',C_69) = B_63
      | ~ r3_lattice3('#skF_5',B_63,C_69)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_633])).

tff(c_739,plain,(
    ! [B_236,C_237] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_236,C_237),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_236,C_237),'#skF_7')
      | k16_lattice3('#skF_5',C_237) = B_236
      | ~ r3_lattice3('#skF_5',B_236,C_237)
      | ~ m1_subset_1(B_236,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_651])).

tff(c_30,plain,(
    ! [A_51,B_63,C_69] :
      ( ~ r3_lattices(A_51,'#skF_4'(A_51,B_63,C_69),B_63)
      | k16_lattice3(A_51,C_69) = B_63
      | ~ r3_lattice3(A_51,B_63,C_69)
      | ~ m1_subset_1(B_63,u1_struct_0(A_51))
      | ~ l3_lattices(A_51)
      | ~ v4_lattice3(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_743,plain,(
    ! [C_237] :
      ( ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_237),'#skF_7')
      | k16_lattice3('#skF_5',C_237) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_237)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_739,c_30])).

tff(c_746,plain,(
    ! [C_237] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_237),'#skF_7')
      | k16_lattice3('#skF_5',C_237) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_52,c_50,c_743])).

tff(c_748,plain,(
    ! [C_238] :
      ( ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_238),'#skF_7')
      | k16_lattice3('#skF_5',C_238) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_746])).

tff(c_752,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_748])).

tff(c_755,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_44,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_42,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:28:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.55  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.32/1.55  
% 3.32/1.55  %Foreground sorts:
% 3.32/1.55  
% 3.32/1.55  
% 3.32/1.55  %Background operators:
% 3.32/1.55  
% 3.32/1.55  
% 3.32/1.55  %Foreground operators:
% 3.32/1.55  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.32/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.55  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.55  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.32/1.55  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.32/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.32/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.55  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.32/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.55  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 3.32/1.55  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.32/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.55  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.32/1.55  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.55  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.32/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.55  
% 3.32/1.57  tff(f_157, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 3.32/1.57  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 3.32/1.57  tff(f_75, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 3.32/1.57  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 3.32/1.57  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 3.32/1.57  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattice3)).
% 3.32/1.57  tff(f_118, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.32/1.57  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_42, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_54, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_52, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_50, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_44, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_32, plain, (![A_51, B_63, C_69]: (r3_lattice3(A_51, '#skF_4'(A_51, B_63, C_69), C_69) | k16_lattice3(A_51, C_69)=B_63 | ~r3_lattice3(A_51, B_63, C_69) | ~m1_subset_1(B_63, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v4_lattice3(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.32/1.57  tff(c_34, plain, (![A_51, B_63, C_69]: (m1_subset_1('#skF_4'(A_51, B_63, C_69), u1_struct_0(A_51)) | k16_lattice3(A_51, C_69)=B_63 | ~r3_lattice3(A_51, B_63, C_69) | ~m1_subset_1(B_63, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v4_lattice3(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.32/1.57  tff(c_18, plain, (![D_50, B_46, C_47]: (r2_hidden(D_50, a_2_1_lattice3(B_46, C_47)) | ~r3_lattice3(B_46, D_50, C_47) | ~m1_subset_1(D_50, u1_struct_0(B_46)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.57  tff(c_97, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_2'(A_109, B_110, C_111), C_111) | r4_lattice3(A_109, B_110, C_111) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l3_lattices(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.57  tff(c_22, plain, (![A_45, B_46, C_47]: ('#skF_3'(A_45, B_46, C_47)=A_45 | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_467, plain, (![A_199, B_200, B_201, C_202]: ('#skF_3'('#skF_2'(A_199, B_200, a_2_1_lattice3(B_201, C_202)), B_201, C_202)='#skF_2'(A_199, B_200, a_2_1_lattice3(B_201, C_202)) | ~l3_lattices(B_201) | v2_struct_0(B_201) | r4_lattice3(A_199, B_200, a_2_1_lattice3(B_201, C_202)) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l3_lattices(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_97, c_22])).
% 3.32/1.57  tff(c_20, plain, (![B_46, A_45, C_47]: (r3_lattice3(B_46, '#skF_3'(A_45, B_46, C_47), C_47) | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_24, plain, (![A_45, B_46, C_47]: (m1_subset_1('#skF_3'(A_45, B_46, C_47), u1_struct_0(B_46)) | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.32/1.57  tff(c_168, plain, (![A_148, B_149, D_150, C_151]: (r1_lattices(A_148, B_149, D_150) | ~r2_hidden(D_150, C_151) | ~m1_subset_1(D_150, u1_struct_0(A_148)) | ~r3_lattice3(A_148, B_149, C_151) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l3_lattices(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.57  tff(c_181, plain, (![A_152, B_153]: (r1_lattices(A_152, B_153, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_152)) | ~r3_lattice3(A_152, B_153, '#skF_7') | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l3_lattices(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_46, c_168])).
% 3.32/1.57  tff(c_183, plain, (![B_153]: (r1_lattices('#skF_5', B_153, '#skF_6') | ~r3_lattice3('#skF_5', B_153, '#skF_7') | ~m1_subset_1(B_153, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_181])).
% 3.32/1.57  tff(c_186, plain, (![B_153]: (r1_lattices('#skF_5', B_153, '#skF_6') | ~r3_lattice3('#skF_5', B_153, '#skF_7') | ~m1_subset_1(B_153, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_183])).
% 3.32/1.57  tff(c_188, plain, (![B_154]: (r1_lattices('#skF_5', B_154, '#skF_6') | ~r3_lattice3('#skF_5', B_154, '#skF_7') | ~m1_subset_1(B_154, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_186])).
% 3.32/1.57  tff(c_200, plain, (![A_45, C_47]: (r1_lattices('#skF_5', '#skF_3'(A_45, '#skF_5', C_47), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_45, '#skF_5', C_47), '#skF_7') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_5', C_47)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_188])).
% 3.32/1.57  tff(c_214, plain, (![A_45, C_47]: (r1_lattices('#skF_5', '#skF_3'(A_45, '#skF_5', C_47), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_45, '#skF_5', C_47), '#skF_7') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_5', C_47)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_200])).
% 3.32/1.57  tff(c_225, plain, (![A_158, C_159]: (r1_lattices('#skF_5', '#skF_3'(A_158, '#skF_5', C_159), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_158, '#skF_5', C_159), '#skF_7') | ~r2_hidden(A_158, a_2_1_lattice3('#skF_5', C_159)))), inference(negUnitSimplification, [status(thm)], [c_56, c_214])).
% 3.32/1.57  tff(c_232, plain, (![A_45]: (r1_lattices('#skF_5', '#skF_3'(A_45, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_225])).
% 3.32/1.57  tff(c_237, plain, (![A_45]: (r1_lattices('#skF_5', '#skF_3'(A_45, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_232])).
% 3.32/1.57  tff(c_238, plain, (![A_45]: (r1_lattices('#skF_5', '#skF_3'(A_45, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_56, c_237])).
% 3.32/1.57  tff(c_474, plain, (![A_199, B_200]: (r1_lattices('#skF_5', '#skF_2'(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l3_lattices(A_199) | v2_struct_0(A_199))), inference(superposition, [status(thm), theory('equality')], [c_467, c_238])).
% 3.32/1.57  tff(c_494, plain, (![A_199, B_200]: (r1_lattices('#skF_5', '#skF_2'(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_199, B_200, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l3_lattices(A_199) | v2_struct_0(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_474])).
% 3.32/1.57  tff(c_517, plain, (![A_207, B_208]: (r1_lattices('#skF_5', '#skF_2'(A_207, B_208, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_207, B_208, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_207, B_208, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l3_lattices(A_207) | v2_struct_0(A_207))), inference(negUnitSimplification, [status(thm)], [c_56, c_494])).
% 3.32/1.57  tff(c_530, plain, (![A_209, B_210]: (r1_lattices('#skF_5', '#skF_2'(A_209, B_210, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_209, B_210, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l3_lattices(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_14, c_517])).
% 3.32/1.57  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.57  tff(c_534, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_530, c_12])).
% 3.32/1.57  tff(c_537, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_534])).
% 3.32/1.57  tff(c_538, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_537])).
% 3.32/1.57  tff(c_40, plain, (![A_80, C_86, B_84]: (k15_lattice3(A_80, C_86)=B_84 | ~r4_lattice3(A_80, B_84, C_86) | ~r2_hidden(B_84, C_86) | ~m1_subset_1(B_84, u1_struct_0(A_80)) | ~l3_lattices(A_80) | ~v4_lattice3(A_80) | ~v10_lattices(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.32/1.57  tff(c_540, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_538, c_40])).
% 3.32/1.57  tff(c_543, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_540])).
% 3.32/1.57  tff(c_544, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_543])).
% 3.32/1.57  tff(c_545, plain, (~r2_hidden('#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_544])).
% 3.32/1.57  tff(c_567, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_545])).
% 3.32/1.57  tff(c_570, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_567])).
% 3.32/1.57  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_570])).
% 3.32/1.57  tff(c_573, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_544])).
% 3.32/1.57  tff(c_38, plain, (![A_73, B_77, C_79]: (r3_lattices(A_73, B_77, k15_lattice3(A_73, C_79)) | ~r2_hidden(B_77, C_79) | ~m1_subset_1(B_77, u1_struct_0(A_73)) | ~l3_lattices(A_73) | ~v4_lattice3(A_73) | ~v10_lattices(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.32/1.57  tff(c_597, plain, (![B_77]: (r3_lattices('#skF_5', B_77, '#skF_6') | ~r2_hidden(B_77, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_77, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_38])).
% 3.32/1.57  tff(c_601, plain, (![B_77]: (r3_lattices('#skF_5', B_77, '#skF_6') | ~r2_hidden(B_77, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_77, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_597])).
% 3.32/1.57  tff(c_604, plain, (![B_216]: (r3_lattices('#skF_5', B_216, '#skF_6') | ~r2_hidden(B_216, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_216, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_601])).
% 3.32/1.57  tff(c_619, plain, (![D_50]: (r3_lattices('#skF_5', D_50, '#skF_6') | ~r3_lattice3('#skF_5', D_50, '#skF_7') | ~m1_subset_1(D_50, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_604])).
% 3.32/1.57  tff(c_627, plain, (![D_50]: (r3_lattices('#skF_5', D_50, '#skF_6') | ~r3_lattice3('#skF_5', D_50, '#skF_7') | ~m1_subset_1(D_50, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_619])).
% 3.32/1.57  tff(c_629, plain, (![D_217]: (r3_lattices('#skF_5', D_217, '#skF_6') | ~r3_lattice3('#skF_5', D_217, '#skF_7') | ~m1_subset_1(D_217, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_627])).
% 3.32/1.57  tff(c_633, plain, (![B_63, C_69]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_63, C_69), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_63, C_69), '#skF_7') | k16_lattice3('#skF_5', C_69)=B_63 | ~r3_lattice3('#skF_5', B_63, C_69) | ~m1_subset_1(B_63, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_629])).
% 3.32/1.57  tff(c_651, plain, (![B_63, C_69]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_63, C_69), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_63, C_69), '#skF_7') | k16_lattice3('#skF_5', C_69)=B_63 | ~r3_lattice3('#skF_5', B_63, C_69) | ~m1_subset_1(B_63, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_633])).
% 3.32/1.57  tff(c_739, plain, (![B_236, C_237]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_236, C_237), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_236, C_237), '#skF_7') | k16_lattice3('#skF_5', C_237)=B_236 | ~r3_lattice3('#skF_5', B_236, C_237) | ~m1_subset_1(B_236, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_651])).
% 3.32/1.57  tff(c_30, plain, (![A_51, B_63, C_69]: (~r3_lattices(A_51, '#skF_4'(A_51, B_63, C_69), B_63) | k16_lattice3(A_51, C_69)=B_63 | ~r3_lattice3(A_51, B_63, C_69) | ~m1_subset_1(B_63, u1_struct_0(A_51)) | ~l3_lattices(A_51) | ~v4_lattice3(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.32/1.57  tff(c_743, plain, (![C_237]: (~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_237), '#skF_7') | k16_lattice3('#skF_5', C_237)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_237) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_739, c_30])).
% 3.32/1.57  tff(c_746, plain, (![C_237]: (v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_237), '#skF_7') | k16_lattice3('#skF_5', C_237)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_237))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_52, c_50, c_743])).
% 3.32/1.57  tff(c_748, plain, (![C_238]: (~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_238), '#skF_7') | k16_lattice3('#skF_5', C_238)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_238))), inference(negUnitSimplification, [status(thm)], [c_56, c_746])).
% 3.32/1.57  tff(c_752, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_748])).
% 3.32/1.57  tff(c_755, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_44, c_752])).
% 3.32/1.57  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_42, c_755])).
% 3.32/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  Inference rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Ref     : 0
% 3.32/1.57  #Sup     : 123
% 3.32/1.57  #Fact    : 0
% 3.32/1.57  #Define  : 0
% 3.32/1.57  #Split   : 2
% 3.32/1.57  #Chain   : 0
% 3.32/1.57  #Close   : 0
% 3.32/1.57  
% 3.32/1.57  Ordering : KBO
% 3.32/1.57  
% 3.32/1.57  Simplification rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Subsume      : 10
% 3.32/1.57  #Demod        : 133
% 3.32/1.57  #Tautology    : 29
% 3.32/1.57  #SimpNegUnit  : 50
% 3.32/1.57  #BackRed      : 0
% 3.32/1.57  
% 3.32/1.57  #Partial instantiations: 0
% 3.32/1.57  #Strategies tried      : 1
% 3.32/1.57  
% 3.32/1.57  Timing (in seconds)
% 3.32/1.57  ----------------------
% 3.32/1.57  Preprocessing        : 0.35
% 3.32/1.57  Parsing              : 0.19
% 3.32/1.57  CNF conversion       : 0.03
% 3.32/1.57  Main loop            : 0.42
% 3.32/1.57  Inferencing          : 0.17
% 3.32/1.58  Reduction            : 0.11
% 3.32/1.58  Demodulation         : 0.08
% 3.32/1.58  BG Simplification    : 0.03
% 3.32/1.58  Subsumption          : 0.08
% 3.32/1.58  Abstraction          : 0.02
% 3.32/1.58  MUC search           : 0.00
% 3.32/1.58  Cooper               : 0.00
% 3.32/1.58  Total                : 0.81
% 3.32/1.58  Index Insertion      : 0.00
% 3.32/1.58  Index Deletion       : 0.00
% 3.32/1.58  Index Matching       : 0.00
% 3.32/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
