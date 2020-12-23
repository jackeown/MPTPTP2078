%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  154 (1691 expanded)
%              Number of leaves         :   34 ( 613 expanded)
%              Depth                    :   34
%              Number of atoms          :  594 (8061 expanded)
%              Number of equality atoms :   47 ( 869 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_168,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_117,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_148,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_48,plain,(
    k16_lattice3('#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    r3_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    ! [A_57,B_69,C_75] :
      ( r3_lattice3(A_57,'#skF_5'(A_57,B_69,C_75),C_75)
      | k16_lattice3(A_57,C_75) = B_69
      | ~ r3_lattice3(A_57,B_69,C_75)
      | ~ m1_subset_1(B_69,u1_struct_0(A_57))
      | ~ l3_lattices(A_57)
      | ~ v4_lattice3(A_57)
      | ~ v10_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ! [A_57,B_69,C_75] :
      ( m1_subset_1('#skF_5'(A_57,B_69,C_75),u1_struct_0(A_57))
      | k16_lattice3(A_57,C_75) = B_69
      | ~ r3_lattice3(A_57,B_69,C_75)
      | ~ m1_subset_1(B_69,u1_struct_0(A_57))
      | ~ l3_lattices(A_57)
      | ~ v4_lattice3(A_57)
      | ~ v10_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_18,plain,(
    ! [D_50,B_46,C_47] :
      ( r2_hidden(D_50,a_2_1_lattice3(B_46,C_47))
      | ~ r3_lattice3(B_46,D_50,C_47)
      | ~ m1_subset_1(D_50,u1_struct_0(B_46))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_314,plain,(
    ! [A_183,B_184,C_185] :
      ( r3_lattice3(A_183,'#skF_5'(A_183,B_184,C_185),C_185)
      | k16_lattice3(A_183,C_185) = B_184
      | ~ r3_lattice3(A_183,B_184,C_185)
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l3_lattices(A_183)
      | ~ v4_lattice3(A_183)
      | ~ v10_lattices(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_75,plain,(
    ! [D_104,B_105,C_106] :
      ( r2_hidden(D_104,a_2_1_lattice3(B_105,C_106))
      | ~ r3_lattice3(B_105,D_104,C_106)
      | ~ m1_subset_1(D_104,u1_struct_0(B_105))
      | ~ l3_lattices(B_105)
      | v2_struct_0(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_45,B_46,C_47] :
      ( '#skF_3'(A_45,B_46,C_47) = A_45
      | ~ r2_hidden(A_45,a_2_1_lattice3(B_46,C_47))
      | ~ l3_lattices(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_79,plain,(
    ! [D_104,B_105,C_106] :
      ( '#skF_3'(D_104,B_105,C_106) = D_104
      | ~ r3_lattice3(B_105,D_104,C_106)
      | ~ m1_subset_1(D_104,u1_struct_0(B_105))
      | ~ l3_lattices(B_105)
      | v2_struct_0(B_105) ) ),
    inference(resolution,[status(thm)],[c_75,c_22])).

tff(c_2350,plain,(
    ! [A_406,B_407,C_408] :
      ( '#skF_3'('#skF_5'(A_406,B_407,C_408),A_406,C_408) = '#skF_5'(A_406,B_407,C_408)
      | ~ m1_subset_1('#skF_5'(A_406,B_407,C_408),u1_struct_0(A_406))
      | k16_lattice3(A_406,C_408) = B_407
      | ~ r3_lattice3(A_406,B_407,C_408)
      | ~ m1_subset_1(B_407,u1_struct_0(A_406))
      | ~ l3_lattices(A_406)
      | ~ v4_lattice3(A_406)
      | ~ v10_lattices(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_314,c_79])).

tff(c_2354,plain,(
    ! [A_409,B_410,C_411] :
      ( '#skF_3'('#skF_5'(A_409,B_410,C_411),A_409,C_411) = '#skF_5'(A_409,B_410,C_411)
      | k16_lattice3(A_409,C_411) = B_410
      | ~ r3_lattice3(A_409,B_410,C_411)
      | ~ m1_subset_1(B_410,u1_struct_0(A_409))
      | ~ l3_lattices(A_409)
      | ~ v4_lattice3(A_409)
      | ~ v10_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_42,c_2350])).

tff(c_2366,plain,(
    ! [C_411] :
      ( '#skF_3'('#skF_5'('#skF_6','#skF_7',C_411),'#skF_6',C_411) = '#skF_5'('#skF_6','#skF_7',C_411)
      | k16_lattice3('#skF_6',C_411) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_411)
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_2354])).

tff(c_2374,plain,(
    ! [C_411] :
      ( '#skF_3'('#skF_5'('#skF_6','#skF_7',C_411),'#skF_6',C_411) = '#skF_5'('#skF_6','#skF_7',C_411)
      | k16_lattice3('#skF_6',C_411) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_411)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2366])).

tff(c_2376,plain,(
    ! [C_412] :
      ( '#skF_3'('#skF_5'('#skF_6','#skF_7',C_412),'#skF_6',C_412) = '#skF_5'('#skF_6','#skF_7',C_412)
      | k16_lattice3('#skF_6',C_412) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2374])).

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

tff(c_52,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_147,plain,(
    ! [A_145,B_146,D_147,C_148] :
      ( r1_lattices(A_145,B_146,D_147)
      | ~ r2_hidden(D_147,C_148)
      | ~ m1_subset_1(D_147,u1_struct_0(A_145))
      | ~ r3_lattice3(A_145,B_146,C_148)
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l3_lattices(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_149,B_150] :
      ( r1_lattices(A_149,B_150,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_149))
      | ~ r3_lattice3(A_149,B_150,'#skF_8')
      | ~ m1_subset_1(B_150,u1_struct_0(A_149))
      | ~ l3_lattices(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_52,c_147])).

tff(c_165,plain,(
    ! [B_150] :
      ( r1_lattices('#skF_6',B_150,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_150,'#skF_8')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_163])).

tff(c_168,plain,(
    ! [B_150] :
      ( r1_lattices('#skF_6',B_150,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_150,'#skF_8')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_165])).

tff(c_170,plain,(
    ! [B_151] :
      ( r1_lattices('#skF_6',B_151,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_151,'#skF_8')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_168])).

tff(c_186,plain,(
    ! [A_45,C_47] :
      ( r1_lattices('#skF_6','#skF_3'(A_45,'#skF_6',C_47),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_3'(A_45,'#skF_6',C_47),'#skF_8')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_6',C_47))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_204,plain,(
    ! [A_45,C_47] :
      ( r1_lattices('#skF_6','#skF_3'(A_45,'#skF_6',C_47),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_3'(A_45,'#skF_6',C_47),'#skF_8')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_6',C_47))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_186])).

tff(c_210,plain,(
    ! [A_154,C_155] :
      ( r1_lattices('#skF_6','#skF_3'(A_154,'#skF_6',C_155),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_3'(A_154,'#skF_6',C_155),'#skF_8')
      | ~ r2_hidden(A_154,a_2_1_lattice3('#skF_6',C_155)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_204])).

tff(c_217,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_6','#skF_3'(A_45,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_210])).

tff(c_222,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_6','#skF_3'(A_45,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_6','#skF_8'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_217])).

tff(c_223,plain,(
    ! [A_45] :
      ( r1_lattices('#skF_6','#skF_3'(A_45,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_45,a_2_1_lattice3('#skF_6','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_222])).

tff(c_2406,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2376,c_223])).

tff(c_2430,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | k16_lattice3('#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2406])).

tff(c_2431,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2430])).

tff(c_2439,plain,(
    ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2431])).

tff(c_2442,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_2439])).

tff(c_2445,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2442])).

tff(c_2446,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2445])).

tff(c_2447,plain,(
    ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2446])).

tff(c_2450,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_2447])).

tff(c_2453,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_50,c_2450])).

tff(c_2455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48,c_2453])).

tff(c_2456,plain,(
    ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2446])).

tff(c_2510,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_2456])).

tff(c_2513,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_50,c_2510])).

tff(c_2515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48,c_2513])).

tff(c_2517,plain,(
    r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2431])).

tff(c_2544,plain,
    ( '#skF_3'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2517,c_22])).

tff(c_2553,plain,
    ( '#skF_3'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2544])).

tff(c_2554,plain,(
    '#skF_3'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2553])).

tff(c_2676,plain,
    ( m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2554,c_24])).

tff(c_2706,plain,
    ( m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2517,c_2676])).

tff(c_2707,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2706])).

tff(c_6,plain,(
    ! [A_1,B_13,C_19] :
      ( r2_hidden('#skF_1'(A_1,B_13,C_19),C_19)
      | r3_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_1'(A_113,B_114,C_115),C_115)
      | r3_lattice3(A_113,B_114,C_115)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_51,B_52,C_53] :
      ( '#skF_4'(A_51,B_52,C_53) = A_51
      | ~ r2_hidden(A_51,a_2_2_lattice3(B_52,C_53))
      | ~ l3_lattices(B_52)
      | ~ v4_lattice3(B_52)
      | ~ v10_lattices(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1294,plain,(
    ! [A_292,B_293,B_294,C_295] :
      ( '#skF_4'('#skF_1'(A_292,B_293,a_2_2_lattice3(B_294,C_295)),B_294,C_295) = '#skF_1'(A_292,B_293,a_2_2_lattice3(B_294,C_295))
      | ~ l3_lattices(B_294)
      | ~ v4_lattice3(B_294)
      | ~ v10_lattices(B_294)
      | v2_struct_0(B_294)
      | r3_lattice3(A_292,B_293,a_2_2_lattice3(B_294,C_295))
      | ~ m1_subset_1(B_293,u1_struct_0(A_292))
      | ~ l3_lattices(A_292)
      | v2_struct_0(A_292) ) ),
    inference(resolution,[status(thm)],[c_107,c_30])).

tff(c_32,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1('#skF_4'(A_51,B_52,C_53),u1_struct_0(B_52))
      | ~ r2_hidden(A_51,a_2_2_lattice3(B_52,C_53))
      | ~ l3_lattices(B_52)
      | ~ v4_lattice3(B_52)
      | ~ v10_lattices(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12367,plain,(
    ! [A_1147,B_1148,B_1149,C_1150] :
      ( m1_subset_1('#skF_1'(A_1147,B_1148,a_2_2_lattice3(B_1149,C_1150)),u1_struct_0(B_1149))
      | ~ r2_hidden('#skF_1'(A_1147,B_1148,a_2_2_lattice3(B_1149,C_1150)),a_2_2_lattice3(B_1149,C_1150))
      | ~ l3_lattices(B_1149)
      | ~ v4_lattice3(B_1149)
      | ~ v10_lattices(B_1149)
      | v2_struct_0(B_1149)
      | ~ l3_lattices(B_1149)
      | ~ v4_lattice3(B_1149)
      | ~ v10_lattices(B_1149)
      | v2_struct_0(B_1149)
      | r3_lattice3(A_1147,B_1148,a_2_2_lattice3(B_1149,C_1150))
      | ~ m1_subset_1(B_1148,u1_struct_0(A_1147))
      | ~ l3_lattices(A_1147)
      | v2_struct_0(A_1147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_32])).

tff(c_12377,plain,(
    ! [A_1,B_13,B_1149,C_1150] :
      ( m1_subset_1('#skF_1'(A_1,B_13,a_2_2_lattice3(B_1149,C_1150)),u1_struct_0(B_1149))
      | ~ l3_lattices(B_1149)
      | ~ v4_lattice3(B_1149)
      | ~ v10_lattices(B_1149)
      | v2_struct_0(B_1149)
      | r3_lattice3(A_1,B_13,a_2_2_lattice3(B_1149,C_1150))
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_12367])).

tff(c_28,plain,(
    ! [B_52,A_51,C_53] :
      ( r4_lattice3(B_52,'#skF_4'(A_51,B_52,C_53),C_53)
      | ~ r2_hidden(A_51,a_2_2_lattice3(B_52,C_53))
      | ~ l3_lattices(B_52)
      | ~ v4_lattice3(B_52)
      | ~ v10_lattices(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12985,plain,(
    ! [B_1188,A_1189,B_1190,C_1191] :
      ( r4_lattice3(B_1188,'#skF_1'(A_1189,B_1190,a_2_2_lattice3(B_1188,C_1191)),C_1191)
      | ~ r2_hidden('#skF_1'(A_1189,B_1190,a_2_2_lattice3(B_1188,C_1191)),a_2_2_lattice3(B_1188,C_1191))
      | ~ l3_lattices(B_1188)
      | ~ v4_lattice3(B_1188)
      | ~ v10_lattices(B_1188)
      | v2_struct_0(B_1188)
      | ~ l3_lattices(B_1188)
      | ~ v4_lattice3(B_1188)
      | ~ v10_lattices(B_1188)
      | v2_struct_0(B_1188)
      | r3_lattice3(A_1189,B_1190,a_2_2_lattice3(B_1188,C_1191))
      | ~ m1_subset_1(B_1190,u1_struct_0(A_1189))
      | ~ l3_lattices(A_1189)
      | v2_struct_0(A_1189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_28])).

tff(c_12996,plain,(
    ! [B_1192,A_1193,B_1194,C_1195] :
      ( r4_lattice3(B_1192,'#skF_1'(A_1193,B_1194,a_2_2_lattice3(B_1192,C_1195)),C_1195)
      | ~ l3_lattices(B_1192)
      | ~ v4_lattice3(B_1192)
      | ~ v10_lattices(B_1192)
      | v2_struct_0(B_1192)
      | r3_lattice3(A_1193,B_1194,a_2_2_lattice3(B_1192,C_1195))
      | ~ m1_subset_1(B_1194,u1_struct_0(A_1193))
      | ~ l3_lattices(A_1193)
      | v2_struct_0(A_1193) ) ),
    inference(resolution,[status(thm)],[c_6,c_12985])).

tff(c_10,plain,(
    ! [A_23,D_44,B_35,C_41] :
      ( r1_lattices(A_23,D_44,B_35)
      | ~ r2_hidden(D_44,C_41)
      | ~ m1_subset_1(D_44,u1_struct_0(A_23))
      | ~ r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3151,plain,(
    ! [A_442,B_443] :
      ( r1_lattices(A_442,'#skF_5'('#skF_6','#skF_7','#skF_8'),B_443)
      | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0(A_442))
      | ~ r4_lattice3(A_442,B_443,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_443,u1_struct_0(A_442))
      | ~ l3_lattices(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_2517,c_10])).

tff(c_3156,plain,(
    ! [B_443] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),B_443)
      | ~ r4_lattice3('#skF_6',B_443,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_6'))
      | k16_lattice3('#skF_6','#skF_8') = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_3151])).

tff(c_3163,plain,(
    ! [B_443] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),B_443)
      | ~ r4_lattice3('#skF_6',B_443,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_6'))
      | k16_lattice3('#skF_6','#skF_8') = '#skF_7'
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_50,c_3156])).

tff(c_3164,plain,(
    ! [B_443] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),B_443)
      | ~ r4_lattice3('#skF_6',B_443,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48,c_3163])).

tff(c_13029,plain,(
    ! [A_1193,B_1194] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_1'(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))))
      | ~ m1_subset_1('#skF_1'(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | r3_lattice3(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(B_1194,u1_struct_0(A_1193))
      | ~ l3_lattices(A_1193)
      | v2_struct_0(A_1193) ) ),
    inference(resolution,[status(thm)],[c_12996,c_3164])).

tff(c_13073,plain,(
    ! [A_1193,B_1194] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_1'(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))))
      | ~ m1_subset_1('#skF_1'(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | r3_lattice3(A_1193,B_1194,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(B_1194,u1_struct_0(A_1193))
      | ~ l3_lattices(A_1193)
      | v2_struct_0(A_1193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_13029])).

tff(c_13317,plain,(
    ! [A_1223,B_1224] :
      ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_1'(A_1223,B_1224,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))))
      | ~ m1_subset_1('#skF_1'(A_1223,B_1224,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
      | r3_lattice3(A_1223,B_1224,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(B_1224,u1_struct_0(A_1223))
      | ~ l3_lattices(A_1223)
      | v2_struct_0(A_1223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13073])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ r1_lattices(A_1,B_13,'#skF_1'(A_1,B_13,C_19))
      | r3_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13321,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
    | r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_13317,c_4])).

tff(c_13324,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
    | r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2707,c_13321])).

tff(c_13325,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6'))
    | r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13324])).

tff(c_13326,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_13325])).

tff(c_13329,plain,
    ( ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_12377,c_13326])).

tff(c_13335,plain,
    ( r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2707,c_60,c_58,c_13329])).

tff(c_13336,plain,(
    r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13335])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_2'(A_116,B_117,C_118),C_118)
      | r4_lattice3(A_116,B_117,C_118)
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l3_lattices(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_625,plain,(
    ! [A_231,B_232,B_233,C_234] :
      ( '#skF_3'('#skF_2'(A_231,B_232,a_2_1_lattice3(B_233,C_234)),B_233,C_234) = '#skF_2'(A_231,B_232,a_2_1_lattice3(B_233,C_234))
      | ~ l3_lattices(B_233)
      | v2_struct_0(B_233)
      | r4_lattice3(A_231,B_232,a_2_1_lattice3(B_233,C_234))
      | ~ m1_subset_1(B_232,u1_struct_0(A_231))
      | ~ l3_lattices(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_118,c_22])).

tff(c_636,plain,(
    ! [A_231,B_232] :
      ( r1_lattices('#skF_6','#skF_2'(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | r4_lattice3(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_232,u1_struct_0(A_231))
      | ~ l3_lattices(A_231)
      | v2_struct_0(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_223])).

tff(c_655,plain,(
    ! [A_231,B_232] :
      ( r1_lattices('#skF_6','#skF_2'(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | v2_struct_0('#skF_6')
      | r4_lattice3(A_231,B_232,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_232,u1_struct_0(A_231))
      | ~ l3_lattices(A_231)
      | v2_struct_0(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_636])).

tff(c_711,plain,(
    ! [A_242,B_243] :
      ( r1_lattices('#skF_6','#skF_2'(A_242,B_243,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_242,B_243,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | r4_lattice3(A_242,B_243,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l3_lattices(A_242)
      | v2_struct_0(A_242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_655])).

tff(c_737,plain,(
    ! [A_246,B_247] :
      ( r1_lattices('#skF_6','#skF_2'(A_246,B_247,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | r4_lattice3(A_246,B_247,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_247,u1_struct_0(A_246))
      | ~ l3_lattices(A_246)
      | v2_struct_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_14,c_711])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_741,plain,
    ( r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_737,c_12])).

tff(c_744,plain,
    ( r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_741])).

tff(c_745,plain,(
    r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_744])).

tff(c_46,plain,(
    ! [A_82,C_88,B_86] :
      ( k15_lattice3(A_82,C_88) = B_86
      | ~ r4_lattice3(A_82,B_86,C_88)
      | ~ r2_hidden(B_86,C_88)
      | ~ m1_subset_1(B_86,u1_struct_0(A_82))
      | ~ l3_lattices(A_82)
      | ~ v4_lattice3(A_82)
      | ~ v10_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_747,plain,
    ( k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7'
    | ~ r2_hidden('#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_745,c_46])).

tff(c_752,plain,
    ( k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7'
    | ~ r2_hidden('#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_747])).

tff(c_753,plain,
    ( k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7'
    | ~ r2_hidden('#skF_7',a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_752])).

tff(c_823,plain,(
    ~ r2_hidden('#skF_7',a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_826,plain,
    ( ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_823])).

tff(c_829,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_826])).

tff(c_831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_829])).

tff(c_832,plain,(
    k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_44,plain,(
    ! [A_79,B_81] :
      ( k16_lattice3(A_79,a_2_2_lattice3(A_79,B_81)) = k15_lattice3(A_79,B_81)
      | ~ l3_lattices(A_79)
      | ~ v4_lattice3(A_79)
      | ~ v10_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_427,plain,(
    ! [A_204,D_205,C_206] :
      ( r3_lattices(A_204,D_205,k16_lattice3(A_204,C_206))
      | ~ r3_lattice3(A_204,D_205,C_206)
      | ~ m1_subset_1(D_205,u1_struct_0(A_204))
      | ~ m1_subset_1(k16_lattice3(A_204,C_206),u1_struct_0(A_204))
      | ~ l3_lattices(A_204)
      | ~ v4_lattice3(A_204)
      | ~ v10_lattices(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2341,plain,(
    ! [A_403,D_404,B_405] :
      ( r3_lattices(A_403,D_404,k16_lattice3(A_403,a_2_2_lattice3(A_403,B_405)))
      | ~ r3_lattice3(A_403,D_404,a_2_2_lattice3(A_403,B_405))
      | ~ m1_subset_1(D_404,u1_struct_0(A_403))
      | ~ m1_subset_1(k15_lattice3(A_403,B_405),u1_struct_0(A_403))
      | ~ l3_lattices(A_403)
      | ~ v4_lattice3(A_403)
      | ~ v10_lattices(A_403)
      | v2_struct_0(A_403)
      | ~ l3_lattices(A_403)
      | ~ v4_lattice3(A_403)
      | ~ v10_lattices(A_403)
      | v2_struct_0(A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_427])).

tff(c_10297,plain,(
    ! [A_996,D_997,B_998] :
      ( r3_lattices(A_996,D_997,k15_lattice3(A_996,B_998))
      | ~ r3_lattice3(A_996,D_997,a_2_2_lattice3(A_996,B_998))
      | ~ m1_subset_1(D_997,u1_struct_0(A_996))
      | ~ m1_subset_1(k15_lattice3(A_996,B_998),u1_struct_0(A_996))
      | ~ l3_lattices(A_996)
      | ~ v4_lattice3(A_996)
      | ~ v10_lattices(A_996)
      | v2_struct_0(A_996)
      | ~ l3_lattices(A_996)
      | ~ v4_lattice3(A_996)
      | ~ v10_lattices(A_996)
      | v2_struct_0(A_996)
      | ~ l3_lattices(A_996)
      | ~ v4_lattice3(A_996)
      | ~ v10_lattices(A_996)
      | v2_struct_0(A_996) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2341])).

tff(c_10299,plain,(
    ! [D_997] :
      ( r3_lattices('#skF_6',D_997,k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ r3_lattice3('#skF_6',D_997,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(D_997,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_10297])).

tff(c_10301,plain,(
    ! [D_997] :
      ( r3_lattices('#skF_6',D_997,'#skF_7')
      | ~ r3_lattice3('#skF_6',D_997,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(D_997,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_60,c_58,c_56,c_60,c_58,c_56,c_54,c_832,c_10299])).

tff(c_10302,plain,(
    ! [D_997] :
      ( r3_lattices('#skF_6',D_997,'#skF_7')
      | ~ r3_lattice3('#skF_6',D_997,a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')))
      | ~ m1_subset_1(D_997,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_10301])).

tff(c_13397,plain,
    ( r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_13336,c_10302])).

tff(c_13417,plain,(
    r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_13397])).

tff(c_38,plain,(
    ! [A_57,B_69,C_75] :
      ( ~ r3_lattices(A_57,'#skF_5'(A_57,B_69,C_75),B_69)
      | k16_lattice3(A_57,C_75) = B_69
      | ~ r3_lattice3(A_57,B_69,C_75)
      | ~ m1_subset_1(B_69,u1_struct_0(A_57))
      | ~ l3_lattices(A_57)
      | ~ v4_lattice3(A_57)
      | ~ v10_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13428,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_13417,c_38])).

tff(c_13431,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_50,c_13428])).

tff(c_13433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48,c_13431])).

tff(c_13434,plain,(
    r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_2_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_13325])).

tff(c_13442,plain,
    ( r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_13434,c_10302])).

tff(c_13458,plain,(
    r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_13442])).

tff(c_13556,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_13458,c_38])).

tff(c_13559,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_50,c_13556])).

tff(c_13561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48,c_13559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.51/4.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.51/4.21  
% 11.51/4.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.51/4.21  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 11.51/4.21  
% 11.51/4.21  %Foreground sorts:
% 11.51/4.21  
% 11.51/4.21  
% 11.51/4.21  %Background operators:
% 11.51/4.21  
% 11.51/4.21  
% 11.51/4.21  %Foreground operators:
% 11.51/4.21  tff(l3_lattices, type, l3_lattices: $i > $o).
% 11.51/4.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.51/4.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.51/4.21  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 11.51/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.51/4.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.51/4.21  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 11.51/4.21  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 11.51/4.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.51/4.21  tff('#skF_7', type, '#skF_7': $i).
% 11.51/4.21  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 11.51/4.21  tff('#skF_6', type, '#skF_6': $i).
% 11.51/4.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.51/4.21  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 11.51/4.21  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 11.51/4.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.51/4.21  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 11.51/4.21  tff(v10_lattices, type, v10_lattices: $i > $o).
% 11.51/4.21  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 11.51/4.21  tff('#skF_8', type, '#skF_8': $i).
% 11.51/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.51/4.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.51/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.51/4.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.51/4.21  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 11.51/4.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.51/4.21  
% 11.51/4.24  tff(f_168, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 11.51/4.24  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 11.51/4.24  tff(f_75, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 11.51/4.24  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 11.51/4.24  tff(f_93, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 11.51/4.24  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 11.51/4.24  tff(f_148, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 11.51/4.24  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 11.51/4.24  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_48, plain, (k16_lattice3('#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_60, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_58, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_56, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_54, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_50, plain, (r3_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_40, plain, (![A_57, B_69, C_75]: (r3_lattice3(A_57, '#skF_5'(A_57, B_69, C_75), C_75) | k16_lattice3(A_57, C_75)=B_69 | ~r3_lattice3(A_57, B_69, C_75) | ~m1_subset_1(B_69, u1_struct_0(A_57)) | ~l3_lattices(A_57) | ~v4_lattice3(A_57) | ~v10_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.51/4.24  tff(c_42, plain, (![A_57, B_69, C_75]: (m1_subset_1('#skF_5'(A_57, B_69, C_75), u1_struct_0(A_57)) | k16_lattice3(A_57, C_75)=B_69 | ~r3_lattice3(A_57, B_69, C_75) | ~m1_subset_1(B_69, u1_struct_0(A_57)) | ~l3_lattices(A_57) | ~v4_lattice3(A_57) | ~v10_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.51/4.24  tff(c_18, plain, (![D_50, B_46, C_47]: (r2_hidden(D_50, a_2_1_lattice3(B_46, C_47)) | ~r3_lattice3(B_46, D_50, C_47) | ~m1_subset_1(D_50, u1_struct_0(B_46)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.51/4.24  tff(c_314, plain, (![A_183, B_184, C_185]: (r3_lattice3(A_183, '#skF_5'(A_183, B_184, C_185), C_185) | k16_lattice3(A_183, C_185)=B_184 | ~r3_lattice3(A_183, B_184, C_185) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l3_lattices(A_183) | ~v4_lattice3(A_183) | ~v10_lattices(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.51/4.24  tff(c_75, plain, (![D_104, B_105, C_106]: (r2_hidden(D_104, a_2_1_lattice3(B_105, C_106)) | ~r3_lattice3(B_105, D_104, C_106) | ~m1_subset_1(D_104, u1_struct_0(B_105)) | ~l3_lattices(B_105) | v2_struct_0(B_105))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.51/4.24  tff(c_22, plain, (![A_45, B_46, C_47]: ('#skF_3'(A_45, B_46, C_47)=A_45 | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.51/4.24  tff(c_79, plain, (![D_104, B_105, C_106]: ('#skF_3'(D_104, B_105, C_106)=D_104 | ~r3_lattice3(B_105, D_104, C_106) | ~m1_subset_1(D_104, u1_struct_0(B_105)) | ~l3_lattices(B_105) | v2_struct_0(B_105))), inference(resolution, [status(thm)], [c_75, c_22])).
% 11.51/4.24  tff(c_2350, plain, (![A_406, B_407, C_408]: ('#skF_3'('#skF_5'(A_406, B_407, C_408), A_406, C_408)='#skF_5'(A_406, B_407, C_408) | ~m1_subset_1('#skF_5'(A_406, B_407, C_408), u1_struct_0(A_406)) | k16_lattice3(A_406, C_408)=B_407 | ~r3_lattice3(A_406, B_407, C_408) | ~m1_subset_1(B_407, u1_struct_0(A_406)) | ~l3_lattices(A_406) | ~v4_lattice3(A_406) | ~v10_lattices(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_314, c_79])).
% 11.51/4.24  tff(c_2354, plain, (![A_409, B_410, C_411]: ('#skF_3'('#skF_5'(A_409, B_410, C_411), A_409, C_411)='#skF_5'(A_409, B_410, C_411) | k16_lattice3(A_409, C_411)=B_410 | ~r3_lattice3(A_409, B_410, C_411) | ~m1_subset_1(B_410, u1_struct_0(A_409)) | ~l3_lattices(A_409) | ~v4_lattice3(A_409) | ~v10_lattices(A_409) | v2_struct_0(A_409))), inference(resolution, [status(thm)], [c_42, c_2350])).
% 11.51/4.24  tff(c_2366, plain, (![C_411]: ('#skF_3'('#skF_5'('#skF_6', '#skF_7', C_411), '#skF_6', C_411)='#skF_5'('#skF_6', '#skF_7', C_411) | k16_lattice3('#skF_6', C_411)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_411) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_2354])).
% 11.51/4.24  tff(c_2374, plain, (![C_411]: ('#skF_3'('#skF_5'('#skF_6', '#skF_7', C_411), '#skF_6', C_411)='#skF_5'('#skF_6', '#skF_7', C_411) | k16_lattice3('#skF_6', C_411)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_411) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2366])).
% 11.51/4.24  tff(c_2376, plain, (![C_412]: ('#skF_3'('#skF_5'('#skF_6', '#skF_7', C_412), '#skF_6', C_412)='#skF_5'('#skF_6', '#skF_7', C_412) | k16_lattice3('#skF_6', C_412)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_412))), inference(negUnitSimplification, [status(thm)], [c_62, c_2374])).
% 11.51/4.24  tff(c_20, plain, (![B_46, A_45, C_47]: (r3_lattice3(B_46, '#skF_3'(A_45, B_46, C_47), C_47) | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.51/4.24  tff(c_24, plain, (![A_45, B_46, C_47]: (m1_subset_1('#skF_3'(A_45, B_46, C_47), u1_struct_0(B_46)) | ~r2_hidden(A_45, a_2_1_lattice3(B_46, C_47)) | ~l3_lattices(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.51/4.24  tff(c_52, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.51/4.24  tff(c_147, plain, (![A_145, B_146, D_147, C_148]: (r1_lattices(A_145, B_146, D_147) | ~r2_hidden(D_147, C_148) | ~m1_subset_1(D_147, u1_struct_0(A_145)) | ~r3_lattice3(A_145, B_146, C_148) | ~m1_subset_1(B_146, u1_struct_0(A_145)) | ~l3_lattices(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.24  tff(c_163, plain, (![A_149, B_150]: (r1_lattices(A_149, B_150, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_149)) | ~r3_lattice3(A_149, B_150, '#skF_8') | ~m1_subset_1(B_150, u1_struct_0(A_149)) | ~l3_lattices(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_52, c_147])).
% 11.51/4.24  tff(c_165, plain, (![B_150]: (r1_lattices('#skF_6', B_150, '#skF_7') | ~r3_lattice3('#skF_6', B_150, '#skF_8') | ~m1_subset_1(B_150, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_163])).
% 11.51/4.24  tff(c_168, plain, (![B_150]: (r1_lattices('#skF_6', B_150, '#skF_7') | ~r3_lattice3('#skF_6', B_150, '#skF_8') | ~m1_subset_1(B_150, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_165])).
% 11.51/4.24  tff(c_170, plain, (![B_151]: (r1_lattices('#skF_6', B_151, '#skF_7') | ~r3_lattice3('#skF_6', B_151, '#skF_8') | ~m1_subset_1(B_151, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_62, c_168])).
% 11.51/4.24  tff(c_186, plain, (![A_45, C_47]: (r1_lattices('#skF_6', '#skF_3'(A_45, '#skF_6', C_47), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_3'(A_45, '#skF_6', C_47), '#skF_8') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_6', C_47)) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_170])).
% 11.51/4.24  tff(c_204, plain, (![A_45, C_47]: (r1_lattices('#skF_6', '#skF_3'(A_45, '#skF_6', C_47), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_3'(A_45, '#skF_6', C_47), '#skF_8') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_6', C_47)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_186])).
% 11.51/4.24  tff(c_210, plain, (![A_154, C_155]: (r1_lattices('#skF_6', '#skF_3'(A_154, '#skF_6', C_155), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_3'(A_154, '#skF_6', C_155), '#skF_8') | ~r2_hidden(A_154, a_2_1_lattice3('#skF_6', C_155)))), inference(negUnitSimplification, [status(thm)], [c_62, c_204])).
% 11.51/4.24  tff(c_217, plain, (![A_45]: (r1_lattices('#skF_6', '#skF_3'(A_45, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_210])).
% 11.51/4.24  tff(c_222, plain, (![A_45]: (r1_lattices('#skF_6', '#skF_3'(A_45, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_217])).
% 11.51/4.24  tff(c_223, plain, (![A_45]: (r1_lattices('#skF_6', '#skF_3'(A_45, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_45, a_2_1_lattice3('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_222])).
% 11.51/4.24  tff(c_2406, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2376, c_223])).
% 11.51/4.24  tff(c_2430, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2406])).
% 11.51/4.24  tff(c_2431, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_48, c_2430])).
% 11.51/4.24  tff(c_2439, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2431])).
% 11.51/4.24  tff(c_2442, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_18, c_2439])).
% 11.51/4.24  tff(c_2445, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2442])).
% 11.51/4.24  tff(c_2446, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_2445])).
% 11.51/4.24  tff(c_2447, plain, (~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_2446])).
% 11.51/4.24  tff(c_2450, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_2447])).
% 11.51/4.24  tff(c_2453, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_50, c_2450])).
% 11.51/4.24  tff(c_2455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_48, c_2453])).
% 11.51/4.24  tff(c_2456, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_2446])).
% 11.51/4.24  tff(c_2510, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_2456])).
% 11.51/4.24  tff(c_2513, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_50, c_2510])).
% 11.51/4.24  tff(c_2515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_48, c_2513])).
% 11.51/4.24  tff(c_2517, plain, (r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_2431])).
% 11.51/4.24  tff(c_2544, plain, ('#skF_3'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2517, c_22])).
% 11.51/4.24  tff(c_2553, plain, ('#skF_3'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2544])).
% 11.51/4.24  tff(c_2554, plain, ('#skF_3'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_2553])).
% 11.51/4.24  tff(c_2676, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2554, c_24])).
% 11.51/4.24  tff(c_2706, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2517, c_2676])).
% 11.51/4.24  tff(c_2707, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_2706])).
% 11.51/4.24  tff(c_6, plain, (![A_1, B_13, C_19]: (r2_hidden('#skF_1'(A_1, B_13, C_19), C_19) | r3_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.24  tff(c_107, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_1'(A_113, B_114, C_115), C_115) | r3_lattice3(A_113, B_114, C_115) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.24  tff(c_30, plain, (![A_51, B_52, C_53]: ('#skF_4'(A_51, B_52, C_53)=A_51 | ~r2_hidden(A_51, a_2_2_lattice3(B_52, C_53)) | ~l3_lattices(B_52) | ~v4_lattice3(B_52) | ~v10_lattices(B_52) | v2_struct_0(B_52))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.51/4.24  tff(c_1294, plain, (![A_292, B_293, B_294, C_295]: ('#skF_4'('#skF_1'(A_292, B_293, a_2_2_lattice3(B_294, C_295)), B_294, C_295)='#skF_1'(A_292, B_293, a_2_2_lattice3(B_294, C_295)) | ~l3_lattices(B_294) | ~v4_lattice3(B_294) | ~v10_lattices(B_294) | v2_struct_0(B_294) | r3_lattice3(A_292, B_293, a_2_2_lattice3(B_294, C_295)) | ~m1_subset_1(B_293, u1_struct_0(A_292)) | ~l3_lattices(A_292) | v2_struct_0(A_292))), inference(resolution, [status(thm)], [c_107, c_30])).
% 11.51/4.24  tff(c_32, plain, (![A_51, B_52, C_53]: (m1_subset_1('#skF_4'(A_51, B_52, C_53), u1_struct_0(B_52)) | ~r2_hidden(A_51, a_2_2_lattice3(B_52, C_53)) | ~l3_lattices(B_52) | ~v4_lattice3(B_52) | ~v10_lattices(B_52) | v2_struct_0(B_52))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.51/4.24  tff(c_12367, plain, (![A_1147, B_1148, B_1149, C_1150]: (m1_subset_1('#skF_1'(A_1147, B_1148, a_2_2_lattice3(B_1149, C_1150)), u1_struct_0(B_1149)) | ~r2_hidden('#skF_1'(A_1147, B_1148, a_2_2_lattice3(B_1149, C_1150)), a_2_2_lattice3(B_1149, C_1150)) | ~l3_lattices(B_1149) | ~v4_lattice3(B_1149) | ~v10_lattices(B_1149) | v2_struct_0(B_1149) | ~l3_lattices(B_1149) | ~v4_lattice3(B_1149) | ~v10_lattices(B_1149) | v2_struct_0(B_1149) | r3_lattice3(A_1147, B_1148, a_2_2_lattice3(B_1149, C_1150)) | ~m1_subset_1(B_1148, u1_struct_0(A_1147)) | ~l3_lattices(A_1147) | v2_struct_0(A_1147))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_32])).
% 11.51/4.24  tff(c_12377, plain, (![A_1, B_13, B_1149, C_1150]: (m1_subset_1('#skF_1'(A_1, B_13, a_2_2_lattice3(B_1149, C_1150)), u1_struct_0(B_1149)) | ~l3_lattices(B_1149) | ~v4_lattice3(B_1149) | ~v10_lattices(B_1149) | v2_struct_0(B_1149) | r3_lattice3(A_1, B_13, a_2_2_lattice3(B_1149, C_1150)) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_6, c_12367])).
% 11.51/4.24  tff(c_28, plain, (![B_52, A_51, C_53]: (r4_lattice3(B_52, '#skF_4'(A_51, B_52, C_53), C_53) | ~r2_hidden(A_51, a_2_2_lattice3(B_52, C_53)) | ~l3_lattices(B_52) | ~v4_lattice3(B_52) | ~v10_lattices(B_52) | v2_struct_0(B_52))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.51/4.24  tff(c_12985, plain, (![B_1188, A_1189, B_1190, C_1191]: (r4_lattice3(B_1188, '#skF_1'(A_1189, B_1190, a_2_2_lattice3(B_1188, C_1191)), C_1191) | ~r2_hidden('#skF_1'(A_1189, B_1190, a_2_2_lattice3(B_1188, C_1191)), a_2_2_lattice3(B_1188, C_1191)) | ~l3_lattices(B_1188) | ~v4_lattice3(B_1188) | ~v10_lattices(B_1188) | v2_struct_0(B_1188) | ~l3_lattices(B_1188) | ~v4_lattice3(B_1188) | ~v10_lattices(B_1188) | v2_struct_0(B_1188) | r3_lattice3(A_1189, B_1190, a_2_2_lattice3(B_1188, C_1191)) | ~m1_subset_1(B_1190, u1_struct_0(A_1189)) | ~l3_lattices(A_1189) | v2_struct_0(A_1189))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_28])).
% 11.51/4.24  tff(c_12996, plain, (![B_1192, A_1193, B_1194, C_1195]: (r4_lattice3(B_1192, '#skF_1'(A_1193, B_1194, a_2_2_lattice3(B_1192, C_1195)), C_1195) | ~l3_lattices(B_1192) | ~v4_lattice3(B_1192) | ~v10_lattices(B_1192) | v2_struct_0(B_1192) | r3_lattice3(A_1193, B_1194, a_2_2_lattice3(B_1192, C_1195)) | ~m1_subset_1(B_1194, u1_struct_0(A_1193)) | ~l3_lattices(A_1193) | v2_struct_0(A_1193))), inference(resolution, [status(thm)], [c_6, c_12985])).
% 11.51/4.24  tff(c_10, plain, (![A_23, D_44, B_35, C_41]: (r1_lattices(A_23, D_44, B_35) | ~r2_hidden(D_44, C_41) | ~m1_subset_1(D_44, u1_struct_0(A_23)) | ~r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.51/4.24  tff(c_3151, plain, (![A_442, B_443]: (r1_lattices(A_442, '#skF_5'('#skF_6', '#skF_7', '#skF_8'), B_443) | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0(A_442)) | ~r4_lattice3(A_442, B_443, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_443, u1_struct_0(A_442)) | ~l3_lattices(A_442) | v2_struct_0(A_442))), inference(resolution, [status(thm)], [c_2517, c_10])).
% 11.51/4.24  tff(c_3156, plain, (![B_443]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), B_443) | ~r4_lattice3('#skF_6', B_443, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_443, u1_struct_0('#skF_6')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_3151])).
% 11.51/4.24  tff(c_3163, plain, (![B_443]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), B_443) | ~r4_lattice3('#skF_6', B_443, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_443, u1_struct_0('#skF_6')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_50, c_3156])).
% 11.51/4.24  tff(c_3164, plain, (![B_443]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), B_443) | ~r4_lattice3('#skF_6', B_443, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_443, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_62, c_48, c_3163])).
% 11.51/4.24  tff(c_13029, plain, (![A_1193, B_1194]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))) | ~m1_subset_1('#skF_1'(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | r3_lattice3(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(B_1194, u1_struct_0(A_1193)) | ~l3_lattices(A_1193) | v2_struct_0(A_1193))), inference(resolution, [status(thm)], [c_12996, c_3164])).
% 11.51/4.24  tff(c_13073, plain, (![A_1193, B_1194]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))) | ~m1_subset_1('#skF_1'(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | r3_lattice3(A_1193, B_1194, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(B_1194, u1_struct_0(A_1193)) | ~l3_lattices(A_1193) | v2_struct_0(A_1193))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_13029])).
% 11.51/4.24  tff(c_13317, plain, (![A_1223, B_1224]: (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_1'(A_1223, B_1224, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))) | ~m1_subset_1('#skF_1'(A_1223, B_1224, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | r3_lattice3(A_1223, B_1224, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(B_1224, u1_struct_0(A_1223)) | ~l3_lattices(A_1223) | v2_struct_0(A_1223))), inference(negUnitSimplification, [status(thm)], [c_62, c_13073])).
% 11.51/4.24  tff(c_4, plain, (![A_1, B_13, C_19]: (~r1_lattices(A_1, B_13, '#skF_1'(A_1, B_13, C_19)) | r3_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.24  tff(c_13321, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_13317, c_4])).
% 11.51/4.24  tff(c_13324, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2707, c_13321])).
% 11.51/4.24  tff(c_13325, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6')) | r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_13324])).
% 11.51/4.24  tff(c_13326, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_13325])).
% 11.51/4.24  tff(c_13329, plain, (~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_12377, c_13326])).
% 11.51/4.24  tff(c_13335, plain, (r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2707, c_60, c_58, c_13329])).
% 11.51/4.24  tff(c_13336, plain, (r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_13335])).
% 11.51/4.24  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.51/4.24  tff(c_118, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_2'(A_116, B_117, C_118), C_118) | r4_lattice3(A_116, B_117, C_118) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l3_lattices(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.51/4.24  tff(c_625, plain, (![A_231, B_232, B_233, C_234]: ('#skF_3'('#skF_2'(A_231, B_232, a_2_1_lattice3(B_233, C_234)), B_233, C_234)='#skF_2'(A_231, B_232, a_2_1_lattice3(B_233, C_234)) | ~l3_lattices(B_233) | v2_struct_0(B_233) | r4_lattice3(A_231, B_232, a_2_1_lattice3(B_233, C_234)) | ~m1_subset_1(B_232, u1_struct_0(A_231)) | ~l3_lattices(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_118, c_22])).
% 11.51/4.24  tff(c_636, plain, (![A_231, B_232]: (r1_lattices('#skF_6', '#skF_2'(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | r4_lattice3(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_232, u1_struct_0(A_231)) | ~l3_lattices(A_231) | v2_struct_0(A_231))), inference(superposition, [status(thm), theory('equality')], [c_625, c_223])).
% 11.51/4.24  tff(c_655, plain, (![A_231, B_232]: (r1_lattices('#skF_6', '#skF_2'(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6') | r4_lattice3(A_231, B_232, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_232, u1_struct_0(A_231)) | ~l3_lattices(A_231) | v2_struct_0(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_636])).
% 11.51/4.24  tff(c_711, plain, (![A_242, B_243]: (r1_lattices('#skF_6', '#skF_2'(A_242, B_243, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_242, B_243, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | r4_lattice3(A_242, B_243, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_243, u1_struct_0(A_242)) | ~l3_lattices(A_242) | v2_struct_0(A_242))), inference(negUnitSimplification, [status(thm)], [c_62, c_655])).
% 11.51/4.24  tff(c_737, plain, (![A_246, B_247]: (r1_lattices('#skF_6', '#skF_2'(A_246, B_247, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | r4_lattice3(A_246, B_247, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_247, u1_struct_0(A_246)) | ~l3_lattices(A_246) | v2_struct_0(A_246))), inference(resolution, [status(thm)], [c_14, c_711])).
% 11.51/4.24  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.51/4.24  tff(c_741, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_737, c_12])).
% 11.51/4.24  tff(c_744, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_741])).
% 11.51/4.24  tff(c_745, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_744])).
% 11.51/4.24  tff(c_46, plain, (![A_82, C_88, B_86]: (k15_lattice3(A_82, C_88)=B_86 | ~r4_lattice3(A_82, B_86, C_88) | ~r2_hidden(B_86, C_88) | ~m1_subset_1(B_86, u1_struct_0(A_82)) | ~l3_lattices(A_82) | ~v4_lattice3(A_82) | ~v10_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.51/4.24  tff(c_747, plain, (k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7' | ~r2_hidden('#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_745, c_46])).
% 11.51/4.24  tff(c_752, plain, (k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7' | ~r2_hidden('#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_747])).
% 11.51/4.24  tff(c_753, plain, (k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7' | ~r2_hidden('#skF_7', a_2_1_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_752])).
% 11.51/4.24  tff(c_823, plain, (~r2_hidden('#skF_7', a_2_1_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_753])).
% 11.51/4.24  tff(c_826, plain, (~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_18, c_823])).
% 11.51/4.24  tff(c_829, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_826])).
% 11.51/4.24  tff(c_831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_829])).
% 11.51/4.24  tff(c_832, plain, (k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_753])).
% 11.51/4.24  tff(c_44, plain, (![A_79, B_81]: (k16_lattice3(A_79, a_2_2_lattice3(A_79, B_81))=k15_lattice3(A_79, B_81) | ~l3_lattices(A_79) | ~v4_lattice3(A_79) | ~v10_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.51/4.24  tff(c_427, plain, (![A_204, D_205, C_206]: (r3_lattices(A_204, D_205, k16_lattice3(A_204, C_206)) | ~r3_lattice3(A_204, D_205, C_206) | ~m1_subset_1(D_205, u1_struct_0(A_204)) | ~m1_subset_1(k16_lattice3(A_204, C_206), u1_struct_0(A_204)) | ~l3_lattices(A_204) | ~v4_lattice3(A_204) | ~v10_lattices(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.51/4.24  tff(c_2341, plain, (![A_403, D_404, B_405]: (r3_lattices(A_403, D_404, k16_lattice3(A_403, a_2_2_lattice3(A_403, B_405))) | ~r3_lattice3(A_403, D_404, a_2_2_lattice3(A_403, B_405)) | ~m1_subset_1(D_404, u1_struct_0(A_403)) | ~m1_subset_1(k15_lattice3(A_403, B_405), u1_struct_0(A_403)) | ~l3_lattices(A_403) | ~v4_lattice3(A_403) | ~v10_lattices(A_403) | v2_struct_0(A_403) | ~l3_lattices(A_403) | ~v4_lattice3(A_403) | ~v10_lattices(A_403) | v2_struct_0(A_403))), inference(superposition, [status(thm), theory('equality')], [c_44, c_427])).
% 11.51/4.24  tff(c_10297, plain, (![A_996, D_997, B_998]: (r3_lattices(A_996, D_997, k15_lattice3(A_996, B_998)) | ~r3_lattice3(A_996, D_997, a_2_2_lattice3(A_996, B_998)) | ~m1_subset_1(D_997, u1_struct_0(A_996)) | ~m1_subset_1(k15_lattice3(A_996, B_998), u1_struct_0(A_996)) | ~l3_lattices(A_996) | ~v4_lattice3(A_996) | ~v10_lattices(A_996) | v2_struct_0(A_996) | ~l3_lattices(A_996) | ~v4_lattice3(A_996) | ~v10_lattices(A_996) | v2_struct_0(A_996) | ~l3_lattices(A_996) | ~v4_lattice3(A_996) | ~v10_lattices(A_996) | v2_struct_0(A_996))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2341])).
% 11.51/4.24  tff(c_10299, plain, (![D_997]: (r3_lattices('#skF_6', D_997, k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~r3_lattice3('#skF_6', D_997, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(D_997, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_832, c_10297])).
% 11.51/4.24  tff(c_10301, plain, (![D_997]: (r3_lattices('#skF_6', D_997, '#skF_7') | ~r3_lattice3('#skF_6', D_997, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(D_997, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_60, c_58, c_56, c_60, c_58, c_56, c_54, c_832, c_10299])).
% 11.51/4.24  tff(c_10302, plain, (![D_997]: (r3_lattices('#skF_6', D_997, '#skF_7') | ~r3_lattice3('#skF_6', D_997, a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))) | ~m1_subset_1(D_997, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_62, c_10301])).
% 11.51/4.24  tff(c_13397, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_13336, c_10302])).
% 11.51/4.24  tff(c_13417, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_13397])).
% 11.51/4.24  tff(c_38, plain, (![A_57, B_69, C_75]: (~r3_lattices(A_57, '#skF_5'(A_57, B_69, C_75), B_69) | k16_lattice3(A_57, C_75)=B_69 | ~r3_lattice3(A_57, B_69, C_75) | ~m1_subset_1(B_69, u1_struct_0(A_57)) | ~l3_lattices(A_57) | ~v4_lattice3(A_57) | ~v10_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.51/4.24  tff(c_13428, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_13417, c_38])).
% 11.51/4.24  tff(c_13431, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_50, c_13428])).
% 11.51/4.24  tff(c_13433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_48, c_13431])).
% 11.51/4.24  tff(c_13434, plain, (r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_2_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8')))), inference(splitRight, [status(thm)], [c_13325])).
% 11.51/4.24  tff(c_13442, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_13434, c_10302])).
% 11.51/4.24  tff(c_13458, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_13442])).
% 11.51/4.24  tff(c_13556, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_13458, c_38])).
% 11.51/4.24  tff(c_13559, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_50, c_13556])).
% 11.51/4.24  tff(c_13561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_48, c_13559])).
% 11.51/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.51/4.24  
% 11.51/4.24  Inference rules
% 11.51/4.24  ----------------------
% 11.51/4.24  #Ref     : 0
% 11.51/4.24  #Sup     : 2445
% 11.51/4.24  #Fact    : 0
% 11.51/4.24  #Define  : 0
% 11.51/4.24  #Split   : 39
% 11.51/4.24  #Chain   : 0
% 11.51/4.24  #Close   : 0
% 11.51/4.24  
% 11.51/4.24  Ordering : KBO
% 11.51/4.24  
% 11.51/4.24  Simplification rules
% 11.51/4.24  ----------------------
% 11.51/4.24  #Subsume      : 466
% 11.51/4.24  #Demod        : 4559
% 11.51/4.24  #Tautology    : 558
% 11.51/4.24  #SimpNegUnit  : 1211
% 11.51/4.24  #BackRed      : 22
% 11.51/4.24  
% 11.51/4.24  #Partial instantiations: 0
% 11.51/4.24  #Strategies tried      : 1
% 11.51/4.24  
% 11.51/4.24  Timing (in seconds)
% 11.51/4.24  ----------------------
% 11.51/4.24  Preprocessing        : 0.35
% 11.51/4.24  Parsing              : 0.18
% 11.51/4.24  CNF conversion       : 0.03
% 11.51/4.24  Main loop            : 3.11
% 11.51/4.24  Inferencing          : 1.05
% 11.51/4.24  Reduction            : 1.02
% 11.51/4.24  Demodulation         : 0.73
% 11.51/4.24  BG Simplification    : 0.09
% 11.51/4.24  Subsumption          : 0.77
% 11.51/4.24  Abstraction          : 0.15
% 11.51/4.24  MUC search           : 0.00
% 11.51/4.24  Cooper               : 0.00
% 11.51/4.24  Total                : 3.51
% 11.51/4.24  Index Insertion      : 0.00
% 11.51/4.24  Index Deletion       : 0.00
% 11.51/4.24  Index Matching       : 0.00
% 11.51/4.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
