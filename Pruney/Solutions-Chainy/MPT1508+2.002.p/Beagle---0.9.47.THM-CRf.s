%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 188 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 ( 828 expanded)
%              Number of equality atoms :   20 (  68 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_128,negated_conjecture,(
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

tff(f_108,axiom,(
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

tff(c_38,plain,(
    k16_lattice3('#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    r3_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v4_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_27,B_39,C_45] :
      ( r3_lattice3(A_27,'#skF_2'(A_27,B_39,C_45),C_45)
      | k16_lattice3(A_27,C_45) = B_39
      | ~ r3_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | ~ v4_lattice3(A_27)
      | ~ v10_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_167,plain,(
    ! [A_94,B_95,C_96] :
      ( m1_subset_1('#skF_2'(A_94,B_95,C_96),u1_struct_0(A_94))
      | k16_lattice3(A_94,C_96) = B_95
      | ~ r3_lattice3(A_94,B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l3_lattices(A_94)
      | ~ v4_lattice3(A_94)
      | ~ v10_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_63,plain,(
    ! [A_70,B_71,D_72,C_73] :
      ( r1_lattices(A_70,B_71,D_72)
      | ~ r2_hidden(D_72,C_73)
      | ~ m1_subset_1(D_72,u1_struct_0(A_70))
      | ~ r3_lattice3(A_70,B_71,C_73)
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    ! [A_74,B_75] :
      ( r1_lattices(A_74,B_75,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_74))
      | ~ r3_lattice3(A_74,B_75,'#skF_5')
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_72,plain,(
    ! [B_75] :
      ( r1_lattices('#skF_3',B_75,'#skF_4')
      | ~ r3_lattice3('#skF_3',B_75,'#skF_5')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_75,plain,(
    ! [B_75] :
      ( r1_lattices('#skF_3',B_75,'#skF_4')
      | ~ r3_lattice3('#skF_3',B_75,'#skF_5')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72])).

tff(c_76,plain,(
    ! [B_75] :
      ( r1_lattices('#skF_3',B_75,'#skF_4')
      | ~ r3_lattice3('#skF_3',B_75,'#skF_5')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_75])).

tff(c_177,plain,(
    ! [B_95,C_96] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | ~ r3_lattice3('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_5')
      | k16_lattice3('#skF_3',C_96) = B_95
      | ~ r3_lattice3('#skF_3',B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_167,c_76])).

tff(c_185,plain,(
    ! [B_95,C_96] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | ~ r3_lattice3('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_5')
      | k16_lattice3('#skF_3',C_96) = B_95
      | ~ r3_lattice3('#skF_3',B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_177])).

tff(c_194,plain,(
    ! [B_99,C_100] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_99,C_100),'#skF_4')
      | ~ r3_lattice3('#skF_3','#skF_2'('#skF_3',B_99,C_100),'#skF_5')
      | k16_lattice3('#skF_3',C_100) = B_99
      | ~ r3_lattice3('#skF_3',B_99,C_100)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_185])).

tff(c_198,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_39,'#skF_5'),'#skF_4')
      | k16_lattice3('#skF_3','#skF_5') = B_39
      | ~ r3_lattice3('#skF_3',B_39,'#skF_5')
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_201,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_39,'#skF_5'),'#skF_4')
      | k16_lattice3('#skF_3','#skF_5') = B_39
      | ~ r3_lattice3('#skF_3',B_39,'#skF_5')
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_198])).

tff(c_202,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_3','#skF_2'('#skF_3',B_39,'#skF_5'),'#skF_4')
      | k16_lattice3('#skF_3','#skF_5') = B_39
      | ~ r3_lattice3('#skF_3',B_39,'#skF_5')
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_201])).

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

tff(c_93,plain,(
    ! [A_79,B_80,C_81] :
      ( r3_lattices(A_79,B_80,C_81)
      | ~ r1_lattices(A_79,B_80,C_81)
      | ~ m1_subset_1(C_81,u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l3_lattices(A_79)
      | ~ v9_lattices(A_79)
      | ~ v8_lattices(A_79)
      | ~ v6_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [B_80] :
      ( r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_101,plain,(
    ! [B_80] :
      ( r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_97])).

tff(c_102,plain,(
    ! [B_80] :
      ( r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_101])).

tff(c_103,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_107,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_110,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_107])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_110])).

tff(c_113,plain,(
    ! [B_80] :
      ( ~ v8_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_115,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_118,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_121,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_118])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_121])).

tff(c_124,plain,(
    ! [B_80] :
      ( ~ v8_lattices('#skF_3')
      | r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_126,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_132,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_129])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_132])).

tff(c_135,plain,(
    ! [B_80] :
      ( r3_lattices('#skF_3',B_80,'#skF_4')
      | ~ r1_lattices('#skF_3',B_80,'#skF_4')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_171,plain,(
    ! [B_95,C_96] :
      ( r3_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | ~ r1_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | k16_lattice3('#skF_3',C_96) = B_95
      | ~ r3_lattice3('#skF_3',B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_167,c_135])).

tff(c_180,plain,(
    ! [B_95,C_96] :
      ( r3_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | ~ r1_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | k16_lattice3('#skF_3',C_96) = B_95
      | ~ r3_lattice3('#skF_3',B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_171])).

tff(c_181,plain,(
    ! [B_95,C_96] :
      ( r3_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | ~ r1_lattices('#skF_3','#skF_2'('#skF_3',B_95,C_96),'#skF_4')
      | k16_lattice3('#skF_3',C_96) = B_95
      | ~ r3_lattice3('#skF_3',B_95,C_96)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_180])).

tff(c_204,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r3_lattices(A_102,'#skF_2'(A_102,B_103,C_104),B_103)
      | k16_lattice3(A_102,C_104) = B_103
      | ~ r3_lattice3(A_102,B_103,C_104)
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l3_lattices(A_102)
      | ~ v4_lattice3(A_102)
      | ~ v10_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_208,plain,(
    ! [C_96] :
      ( ~ l3_lattices('#skF_3')
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_lattices('#skF_3','#skF_2'('#skF_3','#skF_4',C_96),'#skF_4')
      | k16_lattice3('#skF_3',C_96) = '#skF_4'
      | ~ r3_lattice3('#skF_3','#skF_4',C_96)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_181,c_204])).

tff(c_211,plain,(
    ! [C_96] :
      ( v2_struct_0('#skF_3')
      | ~ r1_lattices('#skF_3','#skF_2'('#skF_3','#skF_4',C_96),'#skF_4')
      | k16_lattice3('#skF_3',C_96) = '#skF_4'
      | ~ r3_lattice3('#skF_3','#skF_4',C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_48,c_46,c_208])).

tff(c_213,plain,(
    ! [C_105] :
      ( ~ r1_lattices('#skF_3','#skF_2'('#skF_3','#skF_4',C_105),'#skF_4')
      | k16_lattice3('#skF_3',C_105) = '#skF_4'
      | ~ r3_lattice3('#skF_3','#skF_4',C_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_211])).

tff(c_217,plain,
    ( k16_lattice3('#skF_3','#skF_5') = '#skF_4'
    | ~ r3_lattice3('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_202,c_213])).

tff(c_220,plain,(
    k16_lattice3('#skF_3','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.24/1.30  
% 2.24/1.30  %Foreground sorts:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Background operators:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Foreground operators:
% 2.24/1.30  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.24/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.24/1.30  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.30  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.24/1.30  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.24/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.30  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.24/1.30  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.24/1.30  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.24/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.30  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.24/1.30  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.24/1.30  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.30  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.30  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.24/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.30  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.24/1.30  
% 2.24/1.32  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 2.24/1.32  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 2.24/1.32  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 2.24/1.32  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.24/1.32  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.24/1.32  tff(c_38, plain, (k16_lattice3('#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_40, plain, (r3_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_50, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_48, plain, (v4_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_46, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_34, plain, (![A_27, B_39, C_45]: (r3_lattice3(A_27, '#skF_2'(A_27, B_39, C_45), C_45) | k16_lattice3(A_27, C_45)=B_39 | ~r3_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | ~v4_lattice3(A_27) | ~v10_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.32  tff(c_167, plain, (![A_94, B_95, C_96]: (m1_subset_1('#skF_2'(A_94, B_95, C_96), u1_struct_0(A_94)) | k16_lattice3(A_94, C_96)=B_95 | ~r3_lattice3(A_94, B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l3_lattices(A_94) | ~v4_lattice3(A_94) | ~v10_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.32  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.24/1.32  tff(c_63, plain, (![A_70, B_71, D_72, C_73]: (r1_lattices(A_70, B_71, D_72) | ~r2_hidden(D_72, C_73) | ~m1_subset_1(D_72, u1_struct_0(A_70)) | ~r3_lattice3(A_70, B_71, C_73) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l3_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.32  tff(c_70, plain, (![A_74, B_75]: (r1_lattices(A_74, B_75, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(A_74)) | ~r3_lattice3(A_74, B_75, '#skF_5') | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.24/1.32  tff(c_72, plain, (![B_75]: (r1_lattices('#skF_3', B_75, '#skF_4') | ~r3_lattice3('#skF_3', B_75, '#skF_5') | ~m1_subset_1(B_75, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_70])).
% 2.24/1.32  tff(c_75, plain, (![B_75]: (r1_lattices('#skF_3', B_75, '#skF_4') | ~r3_lattice3('#skF_3', B_75, '#skF_5') | ~m1_subset_1(B_75, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_72])).
% 2.24/1.32  tff(c_76, plain, (![B_75]: (r1_lattices('#skF_3', B_75, '#skF_4') | ~r3_lattice3('#skF_3', B_75, '#skF_5') | ~m1_subset_1(B_75, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_75])).
% 2.24/1.32  tff(c_177, plain, (![B_95, C_96]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | ~r3_lattice3('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_5') | k16_lattice3('#skF_3', C_96)=B_95 | ~r3_lattice3('#skF_3', B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_167, c_76])).
% 2.24/1.32  tff(c_185, plain, (![B_95, C_96]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | ~r3_lattice3('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_5') | k16_lattice3('#skF_3', C_96)=B_95 | ~r3_lattice3('#skF_3', B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_177])).
% 2.24/1.32  tff(c_194, plain, (![B_99, C_100]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_99, C_100), '#skF_4') | ~r3_lattice3('#skF_3', '#skF_2'('#skF_3', B_99, C_100), '#skF_5') | k16_lattice3('#skF_3', C_100)=B_99 | ~r3_lattice3('#skF_3', B_99, C_100) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_185])).
% 2.24/1.32  tff(c_198, plain, (![B_39]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_39, '#skF_5'), '#skF_4') | k16_lattice3('#skF_3', '#skF_5')=B_39 | ~r3_lattice3('#skF_3', B_39, '#skF_5') | ~m1_subset_1(B_39, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_194])).
% 2.24/1.32  tff(c_201, plain, (![B_39]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_39, '#skF_5'), '#skF_4') | k16_lattice3('#skF_3', '#skF_5')=B_39 | ~r3_lattice3('#skF_3', B_39, '#skF_5') | ~m1_subset_1(B_39, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_198])).
% 2.24/1.32  tff(c_202, plain, (![B_39]: (r1_lattices('#skF_3', '#skF_2'('#skF_3', B_39, '#skF_5'), '#skF_4') | k16_lattice3('#skF_3', '#skF_5')=B_39 | ~r3_lattice3('#skF_3', B_39, '#skF_5') | ~m1_subset_1(B_39, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_201])).
% 2.24/1.32  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.32  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.32  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.32  tff(c_93, plain, (![A_79, B_80, C_81]: (r3_lattices(A_79, B_80, C_81) | ~r1_lattices(A_79, B_80, C_81) | ~m1_subset_1(C_81, u1_struct_0(A_79)) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l3_lattices(A_79) | ~v9_lattices(A_79) | ~v8_lattices(A_79) | ~v6_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.32  tff(c_97, plain, (![B_80]: (r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_93])).
% 2.24/1.32  tff(c_101, plain, (![B_80]: (r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_97])).
% 2.24/1.32  tff(c_102, plain, (![B_80]: (r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_101])).
% 2.24/1.32  tff(c_103, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 2.24/1.32  tff(c_107, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_103])).
% 2.24/1.32  tff(c_110, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_107])).
% 2.24/1.32  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_110])).
% 2.24/1.32  tff(c_113, plain, (![B_80]: (~v8_lattices('#skF_3') | ~v9_lattices('#skF_3') | r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_102])).
% 2.24/1.32  tff(c_115, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_113])).
% 2.24/1.32  tff(c_118, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_115])).
% 2.24/1.32  tff(c_121, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_118])).
% 2.24/1.32  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_121])).
% 2.24/1.32  tff(c_124, plain, (![B_80]: (~v8_lattices('#skF_3') | r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_113])).
% 2.24/1.32  tff(c_126, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_124])).
% 2.24/1.32  tff(c_129, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_126])).
% 2.24/1.32  tff(c_132, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_129])).
% 2.24/1.32  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_132])).
% 2.24/1.32  tff(c_135, plain, (![B_80]: (r3_lattices('#skF_3', B_80, '#skF_4') | ~r1_lattices('#skF_3', B_80, '#skF_4') | ~m1_subset_1(B_80, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_124])).
% 2.24/1.32  tff(c_171, plain, (![B_95, C_96]: (r3_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | ~r1_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | k16_lattice3('#skF_3', C_96)=B_95 | ~r3_lattice3('#skF_3', B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_167, c_135])).
% 2.24/1.32  tff(c_180, plain, (![B_95, C_96]: (r3_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | ~r1_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | k16_lattice3('#skF_3', C_96)=B_95 | ~r3_lattice3('#skF_3', B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_171])).
% 2.24/1.32  tff(c_181, plain, (![B_95, C_96]: (r3_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | ~r1_lattices('#skF_3', '#skF_2'('#skF_3', B_95, C_96), '#skF_4') | k16_lattice3('#skF_3', C_96)=B_95 | ~r3_lattice3('#skF_3', B_95, C_96) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_180])).
% 2.24/1.32  tff(c_204, plain, (![A_102, B_103, C_104]: (~r3_lattices(A_102, '#skF_2'(A_102, B_103, C_104), B_103) | k16_lattice3(A_102, C_104)=B_103 | ~r3_lattice3(A_102, B_103, C_104) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l3_lattices(A_102) | ~v4_lattice3(A_102) | ~v10_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.32  tff(c_208, plain, (![C_96]: (~l3_lattices('#skF_3') | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~r1_lattices('#skF_3', '#skF_2'('#skF_3', '#skF_4', C_96), '#skF_4') | k16_lattice3('#skF_3', C_96)='#skF_4' | ~r3_lattice3('#skF_3', '#skF_4', C_96) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_181, c_204])).
% 2.24/1.32  tff(c_211, plain, (![C_96]: (v2_struct_0('#skF_3') | ~r1_lattices('#skF_3', '#skF_2'('#skF_3', '#skF_4', C_96), '#skF_4') | k16_lattice3('#skF_3', C_96)='#skF_4' | ~r3_lattice3('#skF_3', '#skF_4', C_96))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_48, c_46, c_208])).
% 2.24/1.32  tff(c_213, plain, (![C_105]: (~r1_lattices('#skF_3', '#skF_2'('#skF_3', '#skF_4', C_105), '#skF_4') | k16_lattice3('#skF_3', C_105)='#skF_4' | ~r3_lattice3('#skF_3', '#skF_4', C_105))), inference(negUnitSimplification, [status(thm)], [c_52, c_211])).
% 2.24/1.32  tff(c_217, plain, (k16_lattice3('#skF_3', '#skF_5')='#skF_4' | ~r3_lattice3('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_202, c_213])).
% 2.24/1.32  tff(c_220, plain, (k16_lattice3('#skF_3', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_217])).
% 2.24/1.32  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_220])).
% 2.24/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  Inference rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Ref     : 0
% 2.24/1.32  #Sup     : 21
% 2.24/1.32  #Fact    : 0
% 2.24/1.32  #Define  : 0
% 2.24/1.32  #Split   : 3
% 2.24/1.32  #Chain   : 0
% 2.24/1.32  #Close   : 0
% 2.24/1.32  
% 2.24/1.32  Ordering : KBO
% 2.24/1.32  
% 2.24/1.32  Simplification rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Subsume      : 0
% 2.24/1.32  #Demod        : 43
% 2.24/1.32  #Tautology    : 4
% 2.24/1.32  #SimpNegUnit  : 15
% 2.24/1.32  #BackRed      : 0
% 2.24/1.32  
% 2.24/1.32  #Partial instantiations: 0
% 2.24/1.32  #Strategies tried      : 1
% 2.24/1.32  
% 2.24/1.32  Timing (in seconds)
% 2.24/1.32  ----------------------
% 2.24/1.32  Preprocessing        : 0.32
% 2.24/1.32  Parsing              : 0.18
% 2.24/1.32  CNF conversion       : 0.03
% 2.24/1.32  Main loop            : 0.23
% 2.24/1.32  Inferencing          : 0.10
% 2.24/1.32  Reduction            : 0.06
% 2.24/1.32  Demodulation         : 0.04
% 2.24/1.32  BG Simplification    : 0.02
% 2.24/1.32  Subsumption          : 0.04
% 2.24/1.32  Abstraction          : 0.01
% 2.24/1.32  MUC search           : 0.00
% 2.24/1.33  Cooper               : 0.00
% 2.24/1.33  Total                : 0.59
% 2.24/1.33  Index Insertion      : 0.00
% 2.24/1.33  Index Deletion       : 0.00
% 2.24/1.33  Index Matching       : 0.00
% 2.24/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
