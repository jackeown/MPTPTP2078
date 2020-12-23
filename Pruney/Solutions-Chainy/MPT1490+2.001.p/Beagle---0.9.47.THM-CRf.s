%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:43 EST 2020

% Result     : Theorem 37.89s
% Output     : CNFRefutation 38.13s
% Verified   : 
% Statistics : Number of formulae       :  276 (1858 expanded)
%              Number of leaves         :   37 ( 685 expanded)
%              Depth                    :   48
%              Number of atoms          : 1208 (8603 expanded)
%              Number of equality atoms :   22 ( 219 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > k7_lattices > a_2_0_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(a_2_0_lattice3,type,(
    a_2_0_lattice3: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

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

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A,B] :
        ( ( ~ v2_struct_0(B)
          & v10_lattices(B)
          & v17_lattices(B)
          & l3_lattices(B) )
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(B))
           => ( r4_lattice3(B,C,A)
            <=> r3_lattice3(B,k7_lattices(B,C),a_2_0_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattice3)).

tff(f_144,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_lattices(A,k7_lattices(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(C)
        & v10_lattices(C)
        & v17_lattices(C)
        & l3_lattices(C) )
     => ( r2_hidden(A,a_2_0_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(C))
            & A = k7_lattices(C,D)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

tff(f_126,axiom,(
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

tff(f_75,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_lattices(A,B,C)
               => r3_lattices(A,k7_lattices(A,C),k7_lattices(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,
    ( ~ r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ r4_lattice3('#skF_5','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_71,plain,(
    ~ r4_lattice3('#skF_5','#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_38,plain,(
    ! [A_39,B_51,C_57] :
      ( r2_hidden('#skF_2'(A_39,B_51,C_57),C_57)
      | r4_lattice3(A_39,B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    ! [A_39,B_51,C_57] :
      ( m1_subset_1('#skF_2'(A_39,B_51,C_57),u1_struct_0(A_39))
      | r4_lattice3(A_39,B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_16,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k7_lattices(A_2,B_3),u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    v17_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_98,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_2'(A_84,B_85,C_86),u1_struct_0(A_84))
      | r4_lattice3(A_84,B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22,plain,(
    ! [A_7,B_9] :
      ( k7_lattices(A_7,k7_lattices(A_7,B_9)) = B_9
      | ~ m1_subset_1(B_9,u1_struct_0(A_7))
      | ~ l3_lattices(A_7)
      | ~ v17_lattices(A_7)
      | ~ v10_lattices(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_101,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_lattices(A_84,k7_lattices(A_84,'#skF_2'(A_84,B_85,C_86))) = '#skF_2'(A_84,B_85,C_86)
      | ~ v17_lattices(A_84)
      | ~ v10_lattices(A_84)
      | r4_lattice3(A_84,B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_98,c_22])).

tff(c_77,plain,(
    ! [A_79,B_80] :
      ( k7_lattices(A_79,k7_lattices(A_79,B_80)) = B_80
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l3_lattices(A_79)
      | ~ v17_lattices(A_79)
      | ~ v10_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_81,plain,
    ( k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | ~ v17_lattices('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_85,plain,
    ( k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_81])).

tff(c_86,plain,(
    k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_85])).

tff(c_126,plain,(
    ! [C_105,D_106,B_107] :
      ( r2_hidden(k7_lattices(C_105,D_106),a_2_0_lattice3(B_107,C_105))
      | ~ r2_hidden(D_106,B_107)
      | ~ m1_subset_1(D_106,u1_struct_0(C_105))
      | ~ l3_lattices(C_105)
      | ~ v17_lattices(C_105)
      | ~ v10_lattices(C_105)
      | v2_struct_0(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_131,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_107,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_107)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_126])).

tff(c_134,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_107,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_107)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_131])).

tff(c_135,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_107,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_107)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_134])).

tff(c_136,plain,(
    ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_139,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_136])).

tff(c_142,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_142])).

tff(c_146,plain,(
    m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_66,plain,
    ( r4_lattice3('#skF_5','#skF_6','#skF_4')
    | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_66])).

tff(c_42,plain,(
    ! [C_63,D_66,B_62] :
      ( r2_hidden(k7_lattices(C_63,D_66),a_2_0_lattice3(B_62,C_63))
      | ~ r2_hidden(D_66,B_62)
      | ~ m1_subset_1(D_66,u1_struct_0(C_63))
      | ~ l3_lattices(C_63)
      | ~ v17_lattices(C_63)
      | ~ v10_lattices(C_63)
      | v2_struct_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_256,plain,(
    ! [A_117,B_118,D_119,C_120] :
      ( r1_lattices(A_117,B_118,D_119)
      | ~ r2_hidden(D_119,C_120)
      | ~ m1_subset_1(D_119,u1_struct_0(A_117))
      | ~ r3_lattice3(A_117,B_118,C_120)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l3_lattices(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5052,plain,(
    ! [C_397,B_398,B_399,A_400,D_401] :
      ( r1_lattices(A_400,B_399,k7_lattices(C_397,D_401))
      | ~ m1_subset_1(k7_lattices(C_397,D_401),u1_struct_0(A_400))
      | ~ r3_lattice3(A_400,B_399,a_2_0_lattice3(B_398,C_397))
      | ~ m1_subset_1(B_399,u1_struct_0(A_400))
      | ~ l3_lattices(A_400)
      | v2_struct_0(A_400)
      | ~ r2_hidden(D_401,B_398)
      | ~ m1_subset_1(D_401,u1_struct_0(C_397))
      | ~ l3_lattices(C_397)
      | ~ v17_lattices(C_397)
      | ~ v10_lattices(C_397)
      | v2_struct_0(C_397) ) ),
    inference(resolution,[status(thm)],[c_42,c_256])).

tff(c_5083,plain,(
    ! [A_402,B_403,B_404,B_405] :
      ( r1_lattices(A_402,B_403,k7_lattices(A_402,B_404))
      | ~ r3_lattice3(A_402,B_403,a_2_0_lattice3(B_405,A_402))
      | ~ m1_subset_1(B_403,u1_struct_0(A_402))
      | ~ r2_hidden(B_404,B_405)
      | ~ v17_lattices(A_402)
      | ~ v10_lattices(A_402)
      | ~ m1_subset_1(B_404,u1_struct_0(A_402))
      | ~ l3_lattices(A_402)
      | v2_struct_0(A_402) ) ),
    inference(resolution,[status(thm)],[c_16,c_5052])).

tff(c_5085,plain,(
    ! [B_404] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_404))
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ r2_hidden(B_404,'#skF_4')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ m1_subset_1(B_404,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_5083])).

tff(c_5088,plain,(
    ! [B_404] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_404))
      | ~ r2_hidden(B_404,'#skF_4')
      | ~ m1_subset_1(B_404,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_146,c_5085])).

tff(c_5090,plain,(
    ! [B_406] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_406))
      | ~ r2_hidden(B_406,'#skF_4')
      | ~ m1_subset_1(B_406,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5088])).

tff(c_82,plain,(
    ! [A_2,B_3] :
      ( k7_lattices(A_2,k7_lattices(A_2,k7_lattices(A_2,B_3))) = k7_lattices(A_2,B_3)
      | ~ v17_lattices(A_2)
      | ~ v10_lattices(A_2)
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_436,plain,(
    ! [A_131,B_132,C_133] :
      ( r3_lattices(A_131,B_132,C_133)
      | ~ r1_lattices(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | ~ v9_lattices(A_131)
      | ~ v8_lattices(A_131)
      | ~ v6_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_448,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,'#skF_6')
      | ~ r1_lattices('#skF_5',B_132,'#skF_6')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_436])).

tff(c_459,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,'#skF_6')
      | ~ r1_lattices('#skF_5',B_132,'#skF_6')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_448])).

tff(c_460,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,'#skF_6')
      | ~ r1_lattices('#skF_5',B_132,'#skF_6')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_459])).

tff(c_461,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_464,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_461])).

tff(c_467,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_464])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_467])).

tff(c_471,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_438,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_146,c_436])).

tff(c_451,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_438])).

tff(c_452,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_451])).

tff(c_473,plain,(
    ! [B_132] :
      ( r3_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_132,k7_lattices('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_452])).

tff(c_474,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_477,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_474])).

tff(c_480,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_477])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_480])).

tff(c_484,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_470,plain,(
    ! [B_132] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_132,'#skF_6')
      | ~ r1_lattices('#skF_5',B_132,'#skF_6')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_486,plain,(
    ! [B_132] :
      ( ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_132,'#skF_6')
      | ~ r1_lattices('#skF_5',B_132,'#skF_6')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_470])).

tff(c_487,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_490,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_487])).

tff(c_493,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_490])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_493])).

tff(c_497,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_1379,plain,(
    ! [A_184,B_185,B_186] :
      ( r3_lattices(A_184,B_185,k7_lattices(A_184,B_186))
      | ~ r1_lattices(A_184,B_185,k7_lattices(A_184,B_186))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ v9_lattices(A_184)
      | ~ v8_lattices(A_184)
      | ~ v6_lattices(A_184)
      | ~ m1_subset_1(B_186,u1_struct_0(A_184))
      | ~ l3_lattices(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_16,c_436])).

tff(c_603,plain,(
    ! [A_144,C_145,B_146] :
      ( r3_lattices(A_144,k7_lattices(A_144,C_145),k7_lattices(A_144,B_146))
      | ~ r3_lattices(A_144,B_146,C_145)
      | ~ m1_subset_1(C_145,u1_struct_0(A_144))
      | ~ m1_subset_1(B_146,u1_struct_0(A_144))
      | ~ l3_lattices(A_144)
      | ~ v17_lattices(A_144)
      | ~ v10_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_635,plain,(
    ! [C_145] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',C_145),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_603])).

tff(c_653,plain,(
    ! [C_145] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',C_145),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_146,c_635])).

tff(c_654,plain,(
    ! [C_145] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',C_145),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_653])).

tff(c_1382,plain,(
    ! [B_186] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_186)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_186),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_186))
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1379,c_654])).

tff(c_1408,plain,(
    ! [B_186] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_186)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_186),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_186))
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_471,c_484,c_497,c_146,c_1382])).

tff(c_1418,plain,(
    ! [B_187] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_187)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_187),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_187))
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1408])).

tff(c_1456,plain,(
    ! [B_3] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_3),u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1418])).

tff(c_1492,plain,(
    ! [B_3] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_3),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_1456])).

tff(c_1493,plain,(
    ! [B_3] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)),u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_3),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1492])).

tff(c_5467,plain,(
    ! [B_410] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_410),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_410)),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_410,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',B_410),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_410),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5090,c_1493])).

tff(c_5524,plain,(
    ! [B_410] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_410),'#skF_6')
      | ~ m1_subset_1(B_410,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',B_410),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_410),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_5467])).

tff(c_5569,plain,(
    ! [B_410] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_410),'#skF_6')
      | ~ m1_subset_1(B_410,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',B_410),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_410),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5524])).

tff(c_5571,plain,(
    ! [B_411] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_411),'#skF_6')
      | ~ m1_subset_1(B_411,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',B_411),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_411),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5569])).

tff(c_5613,plain,(
    ! [B_3] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',B_3),'#skF_4')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_5571])).

tff(c_5647,plain,(
    ! [B_3] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',B_3),'#skF_4')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5613])).

tff(c_5649,plain,(
    ! [B_412] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',B_412),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',B_412),'#skF_4')
      | ~ m1_subset_1(B_412,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5647])).

tff(c_5695,plain,(
    ! [B_85,C_86] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86))),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_5649])).

tff(c_5741,plain,(
    ! [B_85,C_86] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86))),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_5695])).

tff(c_8458,plain,(
    ! [B_491,C_492] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_491,C_492),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_491,C_492))),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_491,C_492)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_491,C_492)
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5741])).

tff(c_8462,plain,(
    ! [B_85,C_86] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_85,C_86),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8458])).

tff(c_8464,plain,(
    ! [B_85,C_86] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_85,C_86),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_8462])).

tff(c_8466,plain,(
    ! [B_493,C_494] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_493,C_494),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_493,C_494),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_493,C_494)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_493,C_494)
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8464])).

tff(c_8469,plain,(
    ! [B_493,C_494] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_493,C_494),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_493,C_494),'#skF_4')
      | r4_lattice3('#skF_5',B_493,C_494)
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_493,C_494),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_8466])).

tff(c_8472,plain,(
    ! [B_493,C_494] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_493,C_494),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_493,C_494),'#skF_4')
      | r4_lattice3('#skF_5',B_493,C_494)
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_493,C_494),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8469])).

tff(c_8516,plain,(
    ! [B_498,C_499] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_498,C_499),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_498,C_499),'#skF_4')
      | r4_lattice3('#skF_5',B_498,C_499)
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_498,C_499),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8472])).

tff(c_8520,plain,(
    ! [B_51,C_57] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_51,C_57),'#skF_4')
      | r4_lattice3('#skF_5',B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_8516])).

tff(c_8523,plain,(
    ! [B_51,C_57] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_51,C_57),'#skF_4')
      | r4_lattice3('#skF_5',B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8520])).

tff(c_8525,plain,(
    ! [B_500,C_501] :
      ( r3_lattices('#skF_5','#skF_2'('#skF_5',B_500,C_501),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_500,C_501),'#skF_4')
      | r4_lattice3('#skF_5',B_500,C_501)
      | ~ m1_subset_1(B_500,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8523])).

tff(c_24,plain,(
    ! [A_10,C_16,B_14] :
      ( r3_lattices(A_10,k7_lattices(A_10,C_16),k7_lattices(A_10,B_14))
      | ~ r3_lattices(A_10,B_14,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ m1_subset_1(B_14,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | ~ v17_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_666,plain,(
    ! [C_148] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',C_148),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),C_148)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_653])).

tff(c_669,plain,(
    ! [B_14] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_14)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_14),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_14,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_666])).

tff(c_678,plain,(
    ! [B_14] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_14)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_14),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_14,'#skF_6')
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_669])).

tff(c_778,plain,(
    ! [B_151] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_151)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_151),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_678])).

tff(c_20,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_lattices(A_4,B_5,C_6)
      | ~ r3_lattices(A_4,B_5,C_6)
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l3_lattices(A_4)
      | ~ v9_lattices(A_4)
      | ~ v8_lattices(A_4)
      | ~ v6_lattices(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_780,plain,(
    ! [B_151] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_151)),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_151)),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_151),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_778,c_20])).

tff(c_811,plain,(
    ! [B_151] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_151)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_151)),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_151),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_484,c_497,c_52,c_50,c_780])).

tff(c_1687,plain,(
    ! [B_194] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_194)),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_194)),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_194),u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5',B_194,'#skF_6')
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_811])).

tff(c_1732,plain,(
    ! [B_194] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_194)),'#skF_6')
      | ~ r3_lattices('#skF_5',B_194,'#skF_6')
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_194),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_1687])).

tff(c_1768,plain,(
    ! [B_194] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_194)),'#skF_6')
      | ~ r3_lattices('#skF_5',B_194,'#skF_6')
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_194),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1732])).

tff(c_1776,plain,(
    ! [B_195] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5',B_195)),'#skF_6')
      | ~ r3_lattices('#skF_5',B_195,'#skF_6')
      | ~ m1_subset_1(B_195,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_195),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1768])).

tff(c_1815,plain,(
    ! [B_3] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_3),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)),u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1776])).

tff(c_1848,plain,(
    ! [B_3] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_3),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_3)),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_1815])).

tff(c_2156,plain,(
    ! [B_204] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',B_204),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5',B_204)),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1848])).

tff(c_2201,plain,(
    ! [B_204] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_204),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_2156])).

tff(c_2237,plain,(
    ! [B_204] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_204),'#skF_6')
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_204),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2201])).

tff(c_2239,plain,(
    ! [B_205] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_205),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_205),'#skF_6')
      | ~ m1_subset_1(B_205,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5',B_205),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2237])).

tff(c_2269,plain,(
    ! [B_3] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_2239])).

tff(c_2294,plain,(
    ! [B_3] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_3),'#skF_6')
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2269])).

tff(c_2296,plain,(
    ! [B_206] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',B_206),'#skF_6')
      | ~ r3_lattices('#skF_5',k7_lattices('#skF_5',B_206),'#skF_6')
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2294])).

tff(c_2307,plain,(
    ! [B_85,C_86] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86))),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2296])).

tff(c_2334,plain,(
    ! [B_85,C_86] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86))),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_2307])).

tff(c_3231,plain,(
    ! [B_328,C_329] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_2'('#skF_5',B_328,C_329))),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_328,C_329),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_328,C_329)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_328,C_329)
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2334])).

tff(c_3238,plain,(
    ! [B_85,C_86] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_3231])).

tff(c_3241,plain,(
    ! [B_85,C_86] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_85,C_86)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_85,C_86)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_3238])).

tff(c_3458,plain,(
    ! [B_334,C_335] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335)),u1_struct_0('#skF_5'))
      | r4_lattice3('#skF_5',B_334,C_335)
      | ~ m1_subset_1(B_334,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3241])).

tff(c_3461,plain,(
    ! [B_334,C_335] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | r4_lattice3('#skF_5',B_334,C_335)
      | ~ m1_subset_1(B_334,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_334,C_335),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_3458])).

tff(c_3464,plain,(
    ! [B_334,C_335] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_334,C_335),'#skF_6')
      | r4_lattice3('#skF_5',B_334,C_335)
      | ~ m1_subset_1(B_334,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_334,C_335),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3461])).

tff(c_3466,plain,(
    ! [B_336,C_337] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_336,C_337),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_336,C_337),'#skF_6')
      | r4_lattice3('#skF_5',B_336,C_337)
      | ~ m1_subset_1(B_336,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_336,C_337),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3464])).

tff(c_3470,plain,(
    ! [B_51,C_57] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | r4_lattice3('#skF_5',B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_3466])).

tff(c_3473,plain,(
    ! [B_51,C_57] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | r4_lattice3('#skF_5',B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3470])).

tff(c_3474,plain,(
    ! [B_51,C_57] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | ~ r3_lattices('#skF_5','#skF_2'('#skF_5',B_51,C_57),'#skF_6')
      | r4_lattice3('#skF_5',B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3473])).

tff(c_8536,plain,(
    ! [B_502,C_503] :
      ( r1_lattices('#skF_5','#skF_2'('#skF_5',B_502,C_503),'#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_5',B_502,C_503),'#skF_4')
      | r4_lattice3('#skF_5',B_502,C_503)
      | ~ m1_subset_1(B_502,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8525,c_3474])).

tff(c_36,plain,(
    ! [A_39,B_51,C_57] :
      ( ~ r1_lattices(A_39,'#skF_2'(A_39,B_51,C_57),B_51)
      | r4_lattice3(A_39,B_51,C_57)
      | ~ m1_subset_1(B_51,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8540,plain,(
    ! [C_503] :
      ( ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',C_503),'#skF_4')
      | r4_lattice3('#skF_5','#skF_6',C_503)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8536,c_36])).

tff(c_8543,plain,(
    ! [C_503] :
      ( v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',C_503),'#skF_4')
      | r4_lattice3('#skF_5','#skF_6',C_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_8540])).

tff(c_8545,plain,(
    ! [C_504] :
      ( ~ r2_hidden('#skF_2'('#skF_5','#skF_6',C_504),'#skF_4')
      | r4_lattice3('#skF_5','#skF_6',C_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8543])).

tff(c_8549,plain,
    ( r4_lattice3('#skF_5','#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_8545])).

tff(c_8552,plain,
    ( r4_lattice3('#skF_5','#skF_6','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_8549])).

tff(c_8554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_71,c_8552])).

tff(c_8555,plain,(
    ~ r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8562,plain,(
    ! [A_509,B_510] :
      ( k7_lattices(A_509,k7_lattices(A_509,B_510)) = B_510
      | ~ m1_subset_1(B_510,u1_struct_0(A_509))
      | ~ l3_lattices(A_509)
      | ~ v17_lattices(A_509)
      | ~ v10_lattices(A_509)
      | v2_struct_0(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8566,plain,
    ( k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | ~ v17_lattices('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_8562])).

tff(c_8570,plain,
    ( k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_8566])).

tff(c_8571,plain,(
    k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8570])).

tff(c_8612,plain,(
    ! [C_538,D_539,B_540] :
      ( r2_hidden(k7_lattices(C_538,D_539),a_2_0_lattice3(B_540,C_538))
      | ~ r2_hidden(D_539,B_540)
      | ~ m1_subset_1(D_539,u1_struct_0(C_538))
      | ~ l3_lattices(C_538)
      | ~ v17_lattices(C_538)
      | ~ v10_lattices(C_538)
      | v2_struct_0(C_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8617,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_540,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_540)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8571,c_8612])).

tff(c_8620,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_540,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_540)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_8617])).

tff(c_8621,plain,(
    ! [B_540] :
      ( r2_hidden('#skF_6',a_2_0_lattice3(B_540,'#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_6'),B_540)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8620])).

tff(c_8622,plain,(
    ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8621])).

tff(c_8625,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_8622])).

tff(c_8628,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_8625])).

tff(c_8630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8628])).

tff(c_8632,plain,(
    m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8621])).

tff(c_32,plain,(
    ! [A_17,B_29,C_35] :
      ( m1_subset_1('#skF_1'(A_17,B_29,C_35),u1_struct_0(A_17))
      | r3_lattice3(A_17,B_29,C_35)
      | ~ m1_subset_1(B_29,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_17,B_29,C_35] :
      ( r2_hidden('#skF_1'(A_17,B_29,C_35),C_35)
      | r3_lattice3(A_17,B_29,C_35)
      | ~ m1_subset_1(B_29,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_3'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,C_63))
      | ~ l3_lattices(C_63)
      | ~ v17_lattices(C_63)
      | ~ v10_lattices(C_63)
      | v2_struct_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8595,plain,(
    ! [C_532,A_533,B_534] :
      ( k7_lattices(C_532,'#skF_3'(A_533,B_534,C_532)) = A_533
      | ~ r2_hidden(A_533,a_2_0_lattice3(B_534,C_532))
      | ~ l3_lattices(C_532)
      | ~ v17_lattices(C_532)
      | ~ v10_lattices(C_532)
      | v2_struct_0(C_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_11630,plain,(
    ! [C_732,A_733,B_734,B_735] :
      ( k7_lattices(C_732,'#skF_3'('#skF_1'(A_733,B_734,a_2_0_lattice3(B_735,C_732)),B_735,C_732)) = '#skF_1'(A_733,B_734,a_2_0_lattice3(B_735,C_732))
      | ~ l3_lattices(C_732)
      | ~ v17_lattices(C_732)
      | ~ v10_lattices(C_732)
      | v2_struct_0(C_732)
      | r3_lattice3(A_733,B_734,a_2_0_lattice3(B_735,C_732))
      | ~ m1_subset_1(B_734,u1_struct_0(A_733))
      | ~ l3_lattices(A_733)
      | v2_struct_0(A_733) ) ),
    inference(resolution,[status(thm)],[c_30,c_8595])).

tff(c_8608,plain,(
    ! [A_535,B_536,C_537] :
      ( m1_subset_1('#skF_3'(A_535,B_536,C_537),u1_struct_0(C_537))
      | ~ r2_hidden(A_535,a_2_0_lattice3(B_536,C_537))
      | ~ l3_lattices(C_537)
      | ~ v17_lattices(C_537)
      | ~ v10_lattices(C_537)
      | v2_struct_0(C_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8611,plain,(
    ! [C_537,A_535,B_536] :
      ( k7_lattices(C_537,k7_lattices(C_537,'#skF_3'(A_535,B_536,C_537))) = '#skF_3'(A_535,B_536,C_537)
      | ~ r2_hidden(A_535,a_2_0_lattice3(B_536,C_537))
      | ~ l3_lattices(C_537)
      | ~ v17_lattices(C_537)
      | ~ v10_lattices(C_537)
      | v2_struct_0(C_537) ) ),
    inference(resolution,[status(thm)],[c_8608,c_22])).

tff(c_42061,plain,(
    ! [C_1357,A_1358,B_1359,B_1360] :
      ( k7_lattices(C_1357,'#skF_1'(A_1358,B_1359,a_2_0_lattice3(B_1360,C_1357))) = '#skF_3'('#skF_1'(A_1358,B_1359,a_2_0_lattice3(B_1360,C_1357)),B_1360,C_1357)
      | ~ r2_hidden('#skF_1'(A_1358,B_1359,a_2_0_lattice3(B_1360,C_1357)),a_2_0_lattice3(B_1360,C_1357))
      | ~ l3_lattices(C_1357)
      | ~ v17_lattices(C_1357)
      | ~ v10_lattices(C_1357)
      | v2_struct_0(C_1357)
      | ~ l3_lattices(C_1357)
      | ~ v17_lattices(C_1357)
      | ~ v10_lattices(C_1357)
      | v2_struct_0(C_1357)
      | r3_lattice3(A_1358,B_1359,a_2_0_lattice3(B_1360,C_1357))
      | ~ m1_subset_1(B_1359,u1_struct_0(A_1358))
      | ~ l3_lattices(A_1358)
      | v2_struct_0(A_1358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11630,c_8611])).

tff(c_93439,plain,(
    ! [C_2413,A_2414,B_2415,B_2416] :
      ( k7_lattices(C_2413,'#skF_1'(A_2414,B_2415,a_2_0_lattice3(B_2416,C_2413))) = '#skF_3'('#skF_1'(A_2414,B_2415,a_2_0_lattice3(B_2416,C_2413)),B_2416,C_2413)
      | ~ l3_lattices(C_2413)
      | ~ v17_lattices(C_2413)
      | ~ v10_lattices(C_2413)
      | v2_struct_0(C_2413)
      | r3_lattice3(A_2414,B_2415,a_2_0_lattice3(B_2416,C_2413))
      | ~ m1_subset_1(B_2415,u1_struct_0(A_2414))
      | ~ l3_lattices(A_2414)
      | v2_struct_0(A_2414) ) ),
    inference(resolution,[status(thm)],[c_30,c_42061])).

tff(c_8901,plain,(
    ! [A_565,B_566,C_567] :
      ( r3_lattices(A_565,B_566,C_567)
      | ~ r1_lattices(A_565,B_566,C_567)
      | ~ m1_subset_1(C_567,u1_struct_0(A_565))
      | ~ m1_subset_1(B_566,u1_struct_0(A_565))
      | ~ l3_lattices(A_565)
      | ~ v9_lattices(A_565)
      | ~ v8_lattices(A_565)
      | ~ v6_lattices(A_565)
      | v2_struct_0(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8913,plain,(
    ! [B_566] :
      ( r3_lattices('#skF_5',B_566,'#skF_6')
      | ~ r1_lattices('#skF_5',B_566,'#skF_6')
      | ~ m1_subset_1(B_566,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_8901])).

tff(c_8924,plain,(
    ! [B_566] :
      ( r3_lattices('#skF_5',B_566,'#skF_6')
      | ~ r1_lattices('#skF_5',B_566,'#skF_6')
      | ~ m1_subset_1(B_566,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8913])).

tff(c_8925,plain,(
    ! [B_566] :
      ( r3_lattices('#skF_5',B_566,'#skF_6')
      | ~ r1_lattices('#skF_5',B_566,'#skF_6')
      | ~ m1_subset_1(B_566,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8924])).

tff(c_8957,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8925])).

tff(c_8961,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_8957])).

tff(c_8964,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_8961])).

tff(c_8966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8964])).

tff(c_8968,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8925])).

tff(c_8967,plain,(
    ! [B_566] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_566,'#skF_6')
      | ~ r1_lattices('#skF_5',B_566,'#skF_6')
      | ~ m1_subset_1(B_566,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_8925])).

tff(c_8969,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8967])).

tff(c_8972,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_8969])).

tff(c_8975,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_8972])).

tff(c_8977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8975])).

tff(c_8978,plain,(
    ! [B_566] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_566,'#skF_6')
      | ~ r1_lattices('#skF_5',B_566,'#skF_6')
      | ~ m1_subset_1(B_566,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_8967])).

tff(c_8981,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8978])).

tff(c_8984,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_8981])).

tff(c_8987,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_8984])).

tff(c_8989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8987])).

tff(c_8991,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8978])).

tff(c_8979,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8967])).

tff(c_8585,plain,(
    ! [A_520,B_521,C_522] :
      ( m1_subset_1('#skF_1'(A_520,B_521,C_522),u1_struct_0(A_520))
      | r3_lattice3(A_520,B_521,C_522)
      | ~ m1_subset_1(B_521,u1_struct_0(A_520))
      | ~ l3_lattices(A_520)
      | v2_struct_0(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8588,plain,(
    ! [A_520,B_521,C_522] :
      ( k7_lattices(A_520,k7_lattices(A_520,'#skF_1'(A_520,B_521,C_522))) = '#skF_1'(A_520,B_521,C_522)
      | ~ v17_lattices(A_520)
      | ~ v10_lattices(A_520)
      | r3_lattice3(A_520,B_521,C_522)
      | ~ m1_subset_1(B_521,u1_struct_0(A_520))
      | ~ l3_lattices(A_520)
      | v2_struct_0(A_520) ) ),
    inference(resolution,[status(thm)],[c_8585,c_22])).

tff(c_8556,plain,(
    r4_lattice3('#skF_5','#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_48,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1('#skF_3'(A_61,B_62,C_63),u1_struct_0(C_63))
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,C_63))
      | ~ l3_lattices(C_63)
      | ~ v17_lattices(C_63)
      | ~ v10_lattices(C_63)
      | v2_struct_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8726,plain,(
    ! [A_546,D_547,B_548,C_549] :
      ( r1_lattices(A_546,D_547,B_548)
      | ~ r2_hidden(D_547,C_549)
      | ~ m1_subset_1(D_547,u1_struct_0(A_546))
      | ~ r4_lattice3(A_546,B_548,C_549)
      | ~ m1_subset_1(B_548,u1_struct_0(A_546))
      | ~ l3_lattices(A_546)
      | v2_struct_0(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_11991,plain,(
    ! [B_779,B_778,A_780,C_777,A_781] :
      ( r1_lattices(A_781,'#skF_3'(A_780,B_778,C_777),B_779)
      | ~ m1_subset_1('#skF_3'(A_780,B_778,C_777),u1_struct_0(A_781))
      | ~ r4_lattice3(A_781,B_779,B_778)
      | ~ m1_subset_1(B_779,u1_struct_0(A_781))
      | ~ l3_lattices(A_781)
      | v2_struct_0(A_781)
      | ~ r2_hidden(A_780,a_2_0_lattice3(B_778,C_777))
      | ~ l3_lattices(C_777)
      | ~ v17_lattices(C_777)
      | ~ v10_lattices(C_777)
      | v2_struct_0(C_777) ) ),
    inference(resolution,[status(thm)],[c_44,c_8726])).

tff(c_11994,plain,(
    ! [C_63,A_61,B_62,B_779] :
      ( r1_lattices(C_63,'#skF_3'(A_61,B_62,C_63),B_779)
      | ~ r4_lattice3(C_63,B_779,B_62)
      | ~ m1_subset_1(B_779,u1_struct_0(C_63))
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,C_63))
      | ~ l3_lattices(C_63)
      | ~ v17_lattices(C_63)
      | ~ v10_lattices(C_63)
      | v2_struct_0(C_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_11991])).

tff(c_9001,plain,(
    ! [B_573] :
      ( r3_lattices('#skF_5',B_573,'#skF_6')
      | ~ r1_lattices('#skF_5',B_573,'#skF_6')
      | ~ m1_subset_1(B_573,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_8978])).

tff(c_9008,plain,(
    ! [A_61,B_62] :
      ( r3_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r1_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,'#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_9001])).

tff(c_9027,plain,(
    ! [A_61,B_62] :
      ( r3_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r1_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,'#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_9008])).

tff(c_9028,plain,(
    ! [A_61,B_62] :
      ( r3_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r1_lattices('#skF_5','#skF_3'(A_61,B_62,'#skF_5'),'#skF_6')
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_9027])).

tff(c_46,plain,(
    ! [C_63,A_61,B_62] :
      ( k7_lattices(C_63,'#skF_3'(A_61,B_62,C_63)) = A_61
      | ~ r2_hidden(A_61,a_2_0_lattice3(B_62,C_63))
      | ~ l3_lattices(C_63)
      | ~ v17_lattices(C_63)
      | ~ v10_lattices(C_63)
      | v2_struct_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8618,plain,(
    ! [C_538,D_539,B_540] :
      ( k7_lattices(C_538,'#skF_3'(k7_lattices(C_538,D_539),B_540,C_538)) = k7_lattices(C_538,D_539)
      | ~ r2_hidden(D_539,B_540)
      | ~ m1_subset_1(D_539,u1_struct_0(C_538))
      | ~ l3_lattices(C_538)
      | ~ v17_lattices(C_538)
      | ~ v10_lattices(C_538)
      | v2_struct_0(C_538) ) ),
    inference(resolution,[status(thm)],[c_8612,c_46])).

tff(c_8567,plain,(
    ! [A_2,B_3] :
      ( k7_lattices(A_2,k7_lattices(A_2,k7_lattices(A_2,B_3))) = k7_lattices(A_2,B_3)
      | ~ v17_lattices(A_2)
      | ~ v10_lattices(A_2)
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_16,c_8562])).

tff(c_9044,plain,(
    ! [A_574,C_575,B_576] :
      ( r3_lattices(A_574,k7_lattices(A_574,C_575),k7_lattices(A_574,B_576))
      | ~ r3_lattices(A_574,B_576,C_575)
      | ~ m1_subset_1(C_575,u1_struct_0(A_574))
      | ~ m1_subset_1(B_576,u1_struct_0(A_574))
      | ~ l3_lattices(A_574)
      | ~ v17_lattices(A_574)
      | ~ v10_lattices(A_574)
      | v2_struct_0(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_25661,plain,(
    ! [A_1022,B_1023,B_1024] :
      ( r3_lattices(A_1022,k7_lattices(A_1022,B_1023),k7_lattices(A_1022,B_1024))
      | ~ r3_lattices(A_1022,B_1024,k7_lattices(A_1022,k7_lattices(A_1022,B_1023)))
      | ~ m1_subset_1(k7_lattices(A_1022,k7_lattices(A_1022,B_1023)),u1_struct_0(A_1022))
      | ~ m1_subset_1(B_1024,u1_struct_0(A_1022))
      | ~ l3_lattices(A_1022)
      | ~ v17_lattices(A_1022)
      | ~ v10_lattices(A_1022)
      | v2_struct_0(A_1022)
      | ~ v17_lattices(A_1022)
      | ~ v10_lattices(A_1022)
      | ~ m1_subset_1(B_1023,u1_struct_0(A_1022))
      | ~ l3_lattices(A_1022)
      | v2_struct_0(A_1022) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8567,c_9044])).

tff(c_25722,plain,(
    ! [B_1024] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_1024))
      | ~ r3_lattices('#skF_5',B_1024,'#skF_6')
      | ~ m1_subset_1(k7_lattices('#skF_5',k7_lattices('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1024,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8571,c_25661])).

tff(c_25737,plain,(
    ! [B_1024] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_1024))
      | ~ r3_lattices('#skF_5',B_1024,'#skF_6')
      | ~ m1_subset_1(B_1024,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_56,c_54,c_56,c_54,c_52,c_50,c_8571,c_25722])).

tff(c_25739,plain,(
    ! [B_1025] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',B_1025))
      | ~ r3_lattices('#skF_5',B_1025,'#skF_6')
      | ~ m1_subset_1(B_1025,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25737])).

tff(c_25807,plain,(
    ! [D_539,B_540] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_539))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_539),B_540,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k7_lattices('#skF_5',D_539),B_540,'#skF_5'),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_539,B_540)
      | ~ m1_subset_1(D_539,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8618,c_25739])).

tff(c_25874,plain,(
    ! [D_539,B_540] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_539))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_539),B_540,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k7_lattices('#skF_5',D_539),B_540,'#skF_5'),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_539,B_540)
      | ~ m1_subset_1(D_539,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_25807])).

tff(c_29943,plain,(
    ! [D_1087,B_1088] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1087))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_1087),B_1088,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k7_lattices('#skF_5',D_1087),B_1088,'#skF_5'),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_1087,B_1088)
      | ~ m1_subset_1(D_1087,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25874])).

tff(c_30019,plain,(
    ! [D_1087,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1087))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_1087),B_62,'#skF_5'),'#skF_6')
      | ~ r2_hidden(D_1087,B_62)
      | ~ m1_subset_1(D_1087,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',D_1087),a_2_0_lattice3(B_62,'#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_29943])).

tff(c_30079,plain,(
    ! [D_1087,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1087))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_1087),B_62,'#skF_5'),'#skF_6')
      | ~ r2_hidden(D_1087,B_62)
      | ~ m1_subset_1(D_1087,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',D_1087),a_2_0_lattice3(B_62,'#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_30019])).

tff(c_30089,plain,(
    ! [D_1093,B_1094] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1093))
      | ~ r3_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_1093),B_1094,'#skF_5'),'#skF_6')
      | ~ r2_hidden(D_1093,B_1094)
      | ~ m1_subset_1(D_1093,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',D_1093),a_2_0_lattice3(B_1094,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_30079])).

tff(c_30231,plain,(
    ! [D_1095,B_1096] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1095))
      | ~ r2_hidden(D_1095,B_1096)
      | ~ m1_subset_1(D_1095,u1_struct_0('#skF_5'))
      | ~ r1_lattices('#skF_5','#skF_3'(k7_lattices('#skF_5',D_1095),B_1096,'#skF_5'),'#skF_6')
      | ~ r2_hidden(k7_lattices('#skF_5',D_1095),a_2_0_lattice3(B_1096,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_9028,c_30089])).

tff(c_30276,plain,(
    ! [D_1095,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1095))
      | ~ r2_hidden(D_1095,B_62)
      | ~ m1_subset_1(D_1095,u1_struct_0('#skF_5'))
      | ~ r4_lattice3('#skF_5','#skF_6',B_62)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ r2_hidden(k7_lattices('#skF_5',D_1095),a_2_0_lattice3(B_62,'#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_11994,c_30231])).

tff(c_30338,plain,(
    ! [D_1095,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1095))
      | ~ r2_hidden(D_1095,B_62)
      | ~ m1_subset_1(D_1095,u1_struct_0('#skF_5'))
      | ~ r4_lattice3('#skF_5','#skF_6',B_62)
      | ~ r2_hidden(k7_lattices('#skF_5',D_1095),a_2_0_lattice3(B_62,'#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_30276])).

tff(c_30361,plain,(
    ! [D_1097,B_1098] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1097))
      | ~ r2_hidden(D_1097,B_1098)
      | ~ m1_subset_1(D_1097,u1_struct_0('#skF_5'))
      | ~ r4_lattice3('#skF_5','#skF_6',B_1098)
      | ~ r2_hidden(k7_lattices('#skF_5',D_1097),a_2_0_lattice3(B_1098,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_30338])).

tff(c_30406,plain,(
    ! [D_66,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_66))
      | ~ r4_lattice3('#skF_5','#skF_6',B_62)
      | ~ r2_hidden(D_66,B_62)
      | ~ m1_subset_1(D_66,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_30361])).

tff(c_30453,plain,(
    ! [D_66,B_62] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_66))
      | ~ r4_lattice3('#skF_5','#skF_6',B_62)
      | ~ r2_hidden(D_66,B_62)
      | ~ m1_subset_1(D_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_30406])).

tff(c_30458,plain,(
    ! [D_1099,B_1100] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1099))
      | ~ r4_lattice3('#skF_5','#skF_6',B_1100)
      | ~ r2_hidden(D_1099,B_1100)
      | ~ m1_subset_1(D_1099,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_30453])).

tff(c_30462,plain,(
    ! [D_1101] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),k7_lattices('#skF_5',D_1101))
      | ~ r2_hidden(D_1101,'#skF_4')
      | ~ m1_subset_1(D_1101,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8556,c_30458])).

tff(c_30526,plain,(
    ! [B_521,C_522] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_521,C_522))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_521,C_522)),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_1'('#skF_5',B_521,C_522)),u1_struct_0('#skF_5'))
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | r3_lattice3('#skF_5',B_521,C_522)
      | ~ m1_subset_1(B_521,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8588,c_30462])).

tff(c_30594,plain,(
    ! [B_521,C_522] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_521,C_522))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_521,C_522)),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_1'('#skF_5',B_521,C_522)),u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5',B_521,C_522)
      | ~ m1_subset_1(B_521,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_30526])).

tff(c_38708,plain,(
    ! [B_1218,C_1219] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1218,C_1219))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1218,C_1219)),'#skF_4')
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1218,C_1219)),u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5',B_1218,C_1219)
      | ~ m1_subset_1(B_1218,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_30594])).

tff(c_38711,plain,(
    ! [B_1218,C_1219] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1218,C_1219))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1218,C_1219)),'#skF_4')
      | r3_lattice3('#skF_5',B_1218,C_1219)
      | ~ m1_subset_1(B_1218,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1218,C_1219),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_38708])).

tff(c_38714,plain,(
    ! [B_1218,C_1219] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1218,C_1219))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1218,C_1219)),'#skF_4')
      | r3_lattice3('#skF_5',B_1218,C_1219)
      | ~ m1_subset_1(B_1218,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1218,C_1219),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38711])).

tff(c_38716,plain,(
    ! [B_1220,C_1221] :
      ( r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1220,C_1221))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1220,C_1221)),'#skF_4')
      | r3_lattice3('#skF_5',B_1220,C_1221)
      | ~ m1_subset_1(B_1220,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1220,C_1221),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_38714])).

tff(c_38723,plain,(
    ! [B_1220,C_1221] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1220,C_1221))
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1220,C_1221)),'#skF_4')
      | r3_lattice3('#skF_5',B_1220,C_1221)
      | ~ m1_subset_1(B_1220,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1220,C_1221),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38716,c_20])).

tff(c_38728,plain,(
    ! [B_1220,C_1221] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1220,C_1221))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1220,C_1221)),'#skF_4')
      | r3_lattice3('#skF_5',B_1220,C_1221)
      | ~ m1_subset_1(B_1220,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1220,C_1221),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8968,c_8991,c_8979,c_52,c_8632,c_38723])).

tff(c_38730,plain,(
    ! [B_1222,C_1223] :
      ( r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_6'),'#skF_1'('#skF_5',B_1222,C_1223))
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',B_1222,C_1223)),'#skF_4')
      | r3_lattice3('#skF_5',B_1222,C_1223)
      | ~ m1_subset_1(B_1222,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',B_1222,C_1223),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_38728])).

tff(c_28,plain,(
    ! [A_17,B_29,C_35] :
      ( ~ r1_lattices(A_17,B_29,'#skF_1'(A_17,B_29,C_35))
      | r3_lattice3(A_17,B_29,C_35)
      | ~ m1_subset_1(B_29,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38734,plain,(
    ! [C_1223] :
      ( ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)),'#skF_4')
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38730,c_28])).

tff(c_38737,plain,(
    ! [C_1223] :
      ( v2_struct_0('#skF_5')
      | ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)),'#skF_4')
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_52,c_38734])).

tff(c_38738,plain,(
    ! [C_1223] :
      ( ~ r2_hidden(k7_lattices('#skF_5','#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)),'#skF_4')
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223)
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),C_1223),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_38737])).

tff(c_94498,plain,(
    ! [B_2416] :
      ( ~ r2_hidden('#skF_3'('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5')),B_2416,'#skF_5'),'#skF_4')
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5')),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5'))
      | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93439,c_38738])).

tff(c_96046,plain,(
    ! [B_2416] :
      ( ~ r2_hidden('#skF_3'('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5')),B_2416,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5')),u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2416,'#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8632,c_56,c_54,c_52,c_94498])).

tff(c_96548,plain,(
    ! [B_2417] :
      ( ~ r2_hidden('#skF_3'('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2417,'#skF_5')),B_2417,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2417,'#skF_5')),u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3(B_2417,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_96046])).

tff(c_96556,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),u1_struct_0('#skF_5'))
    | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v17_lattices('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_96548])).

tff(c_96562,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),u1_struct_0('#skF_5'))
    | r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),a_2_0_lattice3('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_96556])).

tff(c_96563,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),a_2_0_lattice3('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8555,c_96562])).

tff(c_96564,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),a_2_0_lattice3('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_96563])).

tff(c_96567,plain,
    ( r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_96564])).

tff(c_96570,plain,
    ( r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8632,c_96567])).

tff(c_96572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8555,c_96570])).

tff(c_96573,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_96563])).

tff(c_96577,plain,
    ( r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_96573])).

tff(c_96580,plain,
    ( r3_lattice3('#skF_5',k7_lattices('#skF_5','#skF_6'),a_2_0_lattice3('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8632,c_96577])).

tff(c_96582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8555,c_96580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.89/20.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.89/20.80  
% 37.89/20.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.89/20.80  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > k7_lattices > a_2_0_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 37.89/20.80  
% 37.89/20.80  %Foreground sorts:
% 37.89/20.80  
% 37.89/20.80  
% 37.89/20.80  %Background operators:
% 37.89/20.80  
% 37.89/20.80  
% 37.89/20.80  %Foreground operators:
% 37.89/20.80  tff(l3_lattices, type, l3_lattices: $i > $o).
% 37.89/20.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 37.89/20.80  tff(a_2_0_lattice3, type, a_2_0_lattice3: ($i * $i) > $i).
% 37.89/20.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 37.89/20.80  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 37.89/20.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.89/20.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.89/20.80  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 37.89/20.80  tff(v17_lattices, type, v17_lattices: $i > $o).
% 37.89/20.80  tff('#skF_5', type, '#skF_5': $i).
% 37.89/20.80  tff(v4_lattices, type, v4_lattices: $i > $o).
% 37.89/20.80  tff('#skF_6', type, '#skF_6': $i).
% 37.89/20.80  tff(v6_lattices, type, v6_lattices: $i > $o).
% 37.89/20.80  tff(v9_lattices, type, v9_lattices: $i > $o).
% 37.89/20.80  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 37.89/20.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 37.89/20.80  tff(v5_lattices, type, v5_lattices: $i > $o).
% 37.89/20.80  tff(v10_lattices, type, v10_lattices: $i > $o).
% 37.89/20.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.89/20.80  tff('#skF_4', type, '#skF_4': $i).
% 37.89/20.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 37.89/20.80  tff(v8_lattices, type, v8_lattices: $i > $o).
% 37.89/20.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.89/20.80  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 37.89/20.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 37.89/20.80  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 37.89/20.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.89/20.80  tff(v7_lattices, type, v7_lattices: $i > $o).
% 37.89/20.80  
% 38.13/20.84  tff(f_179, negated_conjecture, ~(![A, B]: ((((~v2_struct_0(B) & v10_lattices(B)) & v17_lattices(B)) & l3_lattices(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (r4_lattice3(B, C, A) <=> r3_lattice3(B, k7_lattices(B, C), a_2_0_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattice3)).
% 38.13/20.84  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 38.13/20.84  tff(f_56, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 38.13/20.84  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_lattices(A, k7_lattices(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 38.13/20.84  tff(f_162, axiom, (![A, B, C]: ((((~v2_struct_0(C) & v10_lattices(C)) & v17_lattices(C)) & l3_lattices(C)) => (r2_hidden(A, a_2_0_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(C)) & (A = k7_lattices(C, D))) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_lattice3)).
% 38.13/20.84  tff(f_126, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 38.13/20.84  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 38.13/20.84  tff(f_75, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 38.13/20.84  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 38.13/20.84  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_60, plain, (~r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | ~r4_lattice3('#skF_5', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_71, plain, (~r4_lattice3('#skF_5', '#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 38.13/20.84  tff(c_52, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_38, plain, (![A_39, B_51, C_57]: (r2_hidden('#skF_2'(A_39, B_51, C_57), C_57) | r4_lattice3(A_39, B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 38.13/20.84  tff(c_40, plain, (![A_39, B_51, C_57]: (m1_subset_1('#skF_2'(A_39, B_51, C_57), u1_struct_0(A_39)) | r4_lattice3(A_39, B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 38.13/20.84  tff(c_16, plain, (![A_2, B_3]: (m1_subset_1(k7_lattices(A_2, B_3), u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_56])).
% 38.13/20.84  tff(c_56, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_54, plain, (v17_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_98, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_2'(A_84, B_85, C_86), u1_struct_0(A_84)) | r4_lattice3(A_84, B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_144])).
% 38.13/20.84  tff(c_22, plain, (![A_7, B_9]: (k7_lattices(A_7, k7_lattices(A_7, B_9))=B_9 | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l3_lattices(A_7) | ~v17_lattices(A_7) | ~v10_lattices(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.13/20.84  tff(c_101, plain, (![A_84, B_85, C_86]: (k7_lattices(A_84, k7_lattices(A_84, '#skF_2'(A_84, B_85, C_86)))='#skF_2'(A_84, B_85, C_86) | ~v17_lattices(A_84) | ~v10_lattices(A_84) | r4_lattice3(A_84, B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_98, c_22])).
% 38.13/20.84  tff(c_77, plain, (![A_79, B_80]: (k7_lattices(A_79, k7_lattices(A_79, B_80))=B_80 | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l3_lattices(A_79) | ~v17_lattices(A_79) | ~v10_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.13/20.84  tff(c_81, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6' | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_77])).
% 38.13/20.84  tff(c_85, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_81])).
% 38.13/20.84  tff(c_86, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_85])).
% 38.13/20.84  tff(c_126, plain, (![C_105, D_106, B_107]: (r2_hidden(k7_lattices(C_105, D_106), a_2_0_lattice3(B_107, C_105)) | ~r2_hidden(D_106, B_107) | ~m1_subset_1(D_106, u1_struct_0(C_105)) | ~l3_lattices(C_105) | ~v17_lattices(C_105) | ~v10_lattices(C_105) | v2_struct_0(C_105))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_131, plain, (![B_107]: (r2_hidden('#skF_6', a_2_0_lattice3(B_107, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_107) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_126])).
% 38.13/20.84  tff(c_134, plain, (![B_107]: (r2_hidden('#skF_6', a_2_0_lattice3(B_107, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_107) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_131])).
% 38.13/20.84  tff(c_135, plain, (![B_107]: (r2_hidden('#skF_6', a_2_0_lattice3(B_107, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_107) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_134])).
% 38.13/20.84  tff(c_136, plain, (~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_135])).
% 38.13/20.84  tff(c_139, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_16, c_136])).
% 38.13/20.84  tff(c_142, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_139])).
% 38.13/20.84  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_142])).
% 38.13/20.84  tff(c_146, plain, (m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_135])).
% 38.13/20.84  tff(c_66, plain, (r4_lattice3('#skF_5', '#skF_6', '#skF_4') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 38.13/20.84  tff(c_74, plain, (r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_71, c_66])).
% 38.13/20.84  tff(c_42, plain, (![C_63, D_66, B_62]: (r2_hidden(k7_lattices(C_63, D_66), a_2_0_lattice3(B_62, C_63)) | ~r2_hidden(D_66, B_62) | ~m1_subset_1(D_66, u1_struct_0(C_63)) | ~l3_lattices(C_63) | ~v17_lattices(C_63) | ~v10_lattices(C_63) | v2_struct_0(C_63))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_256, plain, (![A_117, B_118, D_119, C_120]: (r1_lattices(A_117, B_118, D_119) | ~r2_hidden(D_119, C_120) | ~m1_subset_1(D_119, u1_struct_0(A_117)) | ~r3_lattice3(A_117, B_118, C_120) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l3_lattices(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.13/20.84  tff(c_5052, plain, (![C_397, B_398, B_399, A_400, D_401]: (r1_lattices(A_400, B_399, k7_lattices(C_397, D_401)) | ~m1_subset_1(k7_lattices(C_397, D_401), u1_struct_0(A_400)) | ~r3_lattice3(A_400, B_399, a_2_0_lattice3(B_398, C_397)) | ~m1_subset_1(B_399, u1_struct_0(A_400)) | ~l3_lattices(A_400) | v2_struct_0(A_400) | ~r2_hidden(D_401, B_398) | ~m1_subset_1(D_401, u1_struct_0(C_397)) | ~l3_lattices(C_397) | ~v17_lattices(C_397) | ~v10_lattices(C_397) | v2_struct_0(C_397))), inference(resolution, [status(thm)], [c_42, c_256])).
% 38.13/20.84  tff(c_5083, plain, (![A_402, B_403, B_404, B_405]: (r1_lattices(A_402, B_403, k7_lattices(A_402, B_404)) | ~r3_lattice3(A_402, B_403, a_2_0_lattice3(B_405, A_402)) | ~m1_subset_1(B_403, u1_struct_0(A_402)) | ~r2_hidden(B_404, B_405) | ~v17_lattices(A_402) | ~v10_lattices(A_402) | ~m1_subset_1(B_404, u1_struct_0(A_402)) | ~l3_lattices(A_402) | v2_struct_0(A_402))), inference(resolution, [status(thm)], [c_16, c_5052])).
% 38.13/20.84  tff(c_5085, plain, (![B_404]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_404)) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden(B_404, '#skF_4') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | ~m1_subset_1(B_404, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_5083])).
% 38.13/20.84  tff(c_5088, plain, (![B_404]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_404)) | ~r2_hidden(B_404, '#skF_4') | ~m1_subset_1(B_404, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_146, c_5085])).
% 38.13/20.84  tff(c_5090, plain, (![B_406]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_406)) | ~r2_hidden(B_406, '#skF_4') | ~m1_subset_1(B_406, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5088])).
% 38.13/20.84  tff(c_82, plain, (![A_2, B_3]: (k7_lattices(A_2, k7_lattices(A_2, k7_lattices(A_2, B_3)))=k7_lattices(A_2, B_3) | ~v17_lattices(A_2) | ~v10_lattices(A_2) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(resolution, [status(thm)], [c_16, c_77])).
% 38.13/20.84  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.13/20.84  tff(c_436, plain, (![A_131, B_132, C_133]: (r3_lattices(A_131, B_132, C_133) | ~r1_lattices(A_131, B_132, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | ~v9_lattices(A_131) | ~v8_lattices(A_131) | ~v6_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_75])).
% 38.13/20.84  tff(c_448, plain, (![B_132]: (r3_lattices('#skF_5', B_132, '#skF_6') | ~r1_lattices('#skF_5', B_132, '#skF_6') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_436])).
% 38.13/20.84  tff(c_459, plain, (![B_132]: (r3_lattices('#skF_5', B_132, '#skF_6') | ~r1_lattices('#skF_5', B_132, '#skF_6') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_448])).
% 38.13/20.84  tff(c_460, plain, (![B_132]: (r3_lattices('#skF_5', B_132, '#skF_6') | ~r1_lattices('#skF_5', B_132, '#skF_6') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_459])).
% 38.13/20.84  tff(c_461, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_460])).
% 38.13/20.84  tff(c_464, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_461])).
% 38.13/20.84  tff(c_467, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_464])).
% 38.13/20.84  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_467])).
% 38.13/20.84  tff(c_471, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_460])).
% 38.13/20.84  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.13/20.84  tff(c_438, plain, (![B_132]: (r3_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_146, c_436])).
% 38.13/20.84  tff(c_451, plain, (![B_132]: (r3_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_438])).
% 38.13/20.84  tff(c_452, plain, (![B_132]: (r3_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_451])).
% 38.13/20.84  tff(c_473, plain, (![B_132]: (r3_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_132, k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_452])).
% 38.13/20.84  tff(c_474, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_473])).
% 38.13/20.84  tff(c_477, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_474])).
% 38.13/20.84  tff(c_480, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_477])).
% 38.13/20.84  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_480])).
% 38.13/20.84  tff(c_484, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_473])).
% 38.13/20.84  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.13/20.84  tff(c_470, plain, (![B_132]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_132, '#skF_6') | ~r1_lattices('#skF_5', B_132, '#skF_6') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_460])).
% 38.13/20.84  tff(c_486, plain, (![B_132]: (~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_132, '#skF_6') | ~r1_lattices('#skF_5', B_132, '#skF_6') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_470])).
% 38.13/20.84  tff(c_487, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_486])).
% 38.13/20.84  tff(c_490, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_487])).
% 38.13/20.84  tff(c_493, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_490])).
% 38.13/20.84  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_493])).
% 38.13/20.84  tff(c_497, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_486])).
% 38.13/20.84  tff(c_1379, plain, (![A_184, B_185, B_186]: (r3_lattices(A_184, B_185, k7_lattices(A_184, B_186)) | ~r1_lattices(A_184, B_185, k7_lattices(A_184, B_186)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~v9_lattices(A_184) | ~v8_lattices(A_184) | ~v6_lattices(A_184) | ~m1_subset_1(B_186, u1_struct_0(A_184)) | ~l3_lattices(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_16, c_436])).
% 38.13/20.84  tff(c_603, plain, (![A_144, C_145, B_146]: (r3_lattices(A_144, k7_lattices(A_144, C_145), k7_lattices(A_144, B_146)) | ~r3_lattices(A_144, B_146, C_145) | ~m1_subset_1(C_145, u1_struct_0(A_144)) | ~m1_subset_1(B_146, u1_struct_0(A_144)) | ~l3_lattices(A_144) | ~v17_lattices(A_144) | ~v10_lattices(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_108])).
% 38.13/20.84  tff(c_635, plain, (![C_145]: (r3_lattices('#skF_5', k7_lattices('#skF_5', C_145), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_145) | ~m1_subset_1(C_145, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_603])).
% 38.13/20.84  tff(c_653, plain, (![C_145]: (r3_lattices('#skF_5', k7_lattices('#skF_5', C_145), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_145) | ~m1_subset_1(C_145, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_146, c_635])).
% 38.13/20.84  tff(c_654, plain, (![C_145]: (r3_lattices('#skF_5', k7_lattices('#skF_5', C_145), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_145) | ~m1_subset_1(C_145, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_653])).
% 38.13/20.84  tff(c_1382, plain, (![B_186]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_186)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_186), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_186)) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~m1_subset_1(B_186, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1379, c_654])).
% 38.13/20.84  tff(c_1408, plain, (![B_186]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_186)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_186), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_186)) | ~m1_subset_1(B_186, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_471, c_484, c_497, c_146, c_1382])).
% 38.13/20.84  tff(c_1418, plain, (![B_187]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_187)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_187), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_187)) | ~m1_subset_1(B_187, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1408])).
% 38.13/20.84  tff(c_1456, plain, (![B_3]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_3)), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', k7_lattices('#skF_5', B_3))) | ~m1_subset_1(k7_lattices('#skF_5', B_3), u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1418])).
% 38.13/20.84  tff(c_1492, plain, (![B_3]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_3)), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', k7_lattices('#skF_5', B_3))) | ~m1_subset_1(k7_lattices('#skF_5', B_3), u1_struct_0('#skF_5')) | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_1456])).
% 38.13/20.84  tff(c_1493, plain, (![B_3]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_3)), u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', k7_lattices('#skF_5', B_3))) | ~m1_subset_1(k7_lattices('#skF_5', B_3), u1_struct_0('#skF_5')) | ~m1_subset_1(B_3, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1492])).
% 38.13/20.84  tff(c_5467, plain, (![B_410]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_410), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_410)), u1_struct_0('#skF_5')) | ~m1_subset_1(B_410, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', B_410), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', B_410), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_5090, c_1493])).
% 38.13/20.84  tff(c_5524, plain, (![B_410]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_410), '#skF_6') | ~m1_subset_1(B_410, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', B_410), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', B_410), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_5467])).
% 38.13/20.84  tff(c_5569, plain, (![B_410]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_410), '#skF_6') | ~m1_subset_1(B_410, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', B_410), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', B_410), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5524])).
% 38.13/20.84  tff(c_5571, plain, (![B_411]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_411), '#skF_6') | ~m1_subset_1(B_411, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', B_411), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', B_411), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5569])).
% 38.13/20.84  tff(c_5613, plain, (![B_3]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', B_3), '#skF_4') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_5571])).
% 38.13/20.84  tff(c_5647, plain, (![B_3]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', B_3), '#skF_4') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5613])).
% 38.13/20.84  tff(c_5649, plain, (![B_412]: (r3_lattices('#skF_5', k7_lattices('#skF_5', B_412), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', B_412), '#skF_4') | ~m1_subset_1(B_412, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5647])).
% 38.13/20.84  tff(c_5695, plain, (![B_85, C_86]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86))), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_5649])).
% 38.13/20.84  tff(c_5741, plain, (![B_85, C_86]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86))), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_5695])).
% 38.13/20.84  tff(c_8458, plain, (![B_491, C_492]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_491, C_492), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_491, C_492))), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_491, C_492)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_491, C_492) | ~m1_subset_1(B_491, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5741])).
% 38.13/20.84  tff(c_8462, plain, (![B_85, C_86]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_85, C_86), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8458])).
% 38.13/20.84  tff(c_8464, plain, (![B_85, C_86]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_85, C_86), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_8462])).
% 38.13/20.84  tff(c_8466, plain, (![B_493, C_494]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_493, C_494), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_493, C_494), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_493, C_494)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_493, C_494) | ~m1_subset_1(B_493, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_8464])).
% 38.13/20.84  tff(c_8469, plain, (![B_493, C_494]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_493, C_494), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_493, C_494), '#skF_4') | r4_lattice3('#skF_5', B_493, C_494) | ~m1_subset_1(B_493, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_493, C_494), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_8466])).
% 38.13/20.84  tff(c_8472, plain, (![B_493, C_494]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_493, C_494), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_493, C_494), '#skF_4') | r4_lattice3('#skF_5', B_493, C_494) | ~m1_subset_1(B_493, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_493, C_494), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8469])).
% 38.13/20.84  tff(c_8516, plain, (![B_498, C_499]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_498, C_499), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_498, C_499), '#skF_4') | r4_lattice3('#skF_5', B_498, C_499) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_498, C_499), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_8472])).
% 38.13/20.84  tff(c_8520, plain, (![B_51, C_57]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_51, C_57), '#skF_4') | r4_lattice3('#skF_5', B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_8516])).
% 38.13/20.84  tff(c_8523, plain, (![B_51, C_57]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_51, C_57), '#skF_4') | r4_lattice3('#skF_5', B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8520])).
% 38.13/20.84  tff(c_8525, plain, (![B_500, C_501]: (r3_lattices('#skF_5', '#skF_2'('#skF_5', B_500, C_501), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_500, C_501), '#skF_4') | r4_lattice3('#skF_5', B_500, C_501) | ~m1_subset_1(B_500, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_8523])).
% 38.13/20.84  tff(c_24, plain, (![A_10, C_16, B_14]: (r3_lattices(A_10, k7_lattices(A_10, C_16), k7_lattices(A_10, B_14)) | ~r3_lattices(A_10, B_14, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_10)) | ~m1_subset_1(B_14, u1_struct_0(A_10)) | ~l3_lattices(A_10) | ~v17_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_108])).
% 38.13/20.84  tff(c_666, plain, (![C_148]: (r3_lattices('#skF_5', k7_lattices('#skF_5', C_148), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_148) | ~m1_subset_1(C_148, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_653])).
% 38.13/20.84  tff(c_669, plain, (![B_14]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_14)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_14), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_14, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(B_14, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_666])).
% 38.13/20.84  tff(c_678, plain, (![B_14]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_14)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_14), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_14, '#skF_6') | ~m1_subset_1(B_14, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_669])).
% 38.13/20.84  tff(c_778, plain, (![B_151]: (r3_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_151)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_151), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_678])).
% 38.13/20.84  tff(c_20, plain, (![A_4, B_5, C_6]: (r1_lattices(A_4, B_5, C_6) | ~r3_lattices(A_4, B_5, C_6) | ~m1_subset_1(C_6, u1_struct_0(A_4)) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l3_lattices(A_4) | ~v9_lattices(A_4) | ~v8_lattices(A_4) | ~v6_lattices(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_75])).
% 38.13/20.84  tff(c_780, plain, (![B_151]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_151)), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_151)), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(k7_lattices('#skF_5', B_151), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_778, c_20])).
% 38.13/20.84  tff(c_811, plain, (![B_151]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_151)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_151)), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(k7_lattices('#skF_5', B_151), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_484, c_497, c_52, c_50, c_780])).
% 38.13/20.84  tff(c_1687, plain, (![B_194]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_194)), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_194)), u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_194), u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', B_194, '#skF_6') | ~m1_subset_1(B_194, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_811])).
% 38.13/20.84  tff(c_1732, plain, (![B_194]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_194)), '#skF_6') | ~r3_lattices('#skF_5', B_194, '#skF_6') | ~m1_subset_1(B_194, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_194), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_1687])).
% 38.13/20.84  tff(c_1768, plain, (![B_194]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_194)), '#skF_6') | ~r3_lattices('#skF_5', B_194, '#skF_6') | ~m1_subset_1(B_194, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_194), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1732])).
% 38.13/20.84  tff(c_1776, plain, (![B_195]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', B_195)), '#skF_6') | ~r3_lattices('#skF_5', B_195, '#skF_6') | ~m1_subset_1(B_195, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_195), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1768])).
% 38.13/20.84  tff(c_1815, plain, (![B_3]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_3), u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_3)), u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1776])).
% 38.13/20.84  tff(c_1848, plain, (![B_3]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_3), u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_3)), u1_struct_0('#skF_5')) | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_1815])).
% 38.13/20.84  tff(c_2156, plain, (![B_204]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', B_204), u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', B_204)), u1_struct_0('#skF_5')) | ~m1_subset_1(B_204, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1848])).
% 38.13/20.84  tff(c_2201, plain, (![B_204]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~m1_subset_1(B_204, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_204), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_2156])).
% 38.13/20.84  tff(c_2237, plain, (![B_204]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_204), '#skF_6') | ~m1_subset_1(B_204, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_204), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2201])).
% 38.13/20.84  tff(c_2239, plain, (![B_205]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_205), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_205), '#skF_6') | ~m1_subset_1(B_205, u1_struct_0('#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', B_205), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2237])).
% 38.13/20.84  tff(c_2269, plain, (![B_3]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_2239])).
% 38.13/20.84  tff(c_2294, plain, (![B_3]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_3), '#skF_6') | ~m1_subset_1(B_3, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2269])).
% 38.13/20.84  tff(c_2296, plain, (![B_206]: (r1_lattices('#skF_5', k7_lattices('#skF_5', B_206), '#skF_6') | ~r3_lattices('#skF_5', k7_lattices('#skF_5', B_206), '#skF_6') | ~m1_subset_1(B_206, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2294])).
% 38.13/20.84  tff(c_2307, plain, (![B_85, C_86]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86))), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2296])).
% 38.13/20.84  tff(c_2334, plain, (![B_85, C_86]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86))), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_2307])).
% 38.13/20.84  tff(c_3231, plain, (![B_328, C_329]: (r1_lattices('#skF_5', k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_2'('#skF_5', B_328, C_329))), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_328, C_329), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_328, C_329)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_328, C_329) | ~m1_subset_1(B_328, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2334])).
% 38.13/20.84  tff(c_3238, plain, (![B_85, C_86]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_3231])).
% 38.13/20.84  tff(c_3241, plain, (![B_85, C_86]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_85, C_86)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_85, C_86) | ~m1_subset_1(B_85, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_3238])).
% 38.13/20.84  tff(c_3458, plain, (![B_334, C_335]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335)), u1_struct_0('#skF_5')) | r4_lattice3('#skF_5', B_334, C_335) | ~m1_subset_1(B_334, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_3241])).
% 38.13/20.84  tff(c_3461, plain, (![B_334, C_335]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | r4_lattice3('#skF_5', B_334, C_335) | ~m1_subset_1(B_334, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_334, C_335), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_3458])).
% 38.13/20.84  tff(c_3464, plain, (![B_334, C_335]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_334, C_335), '#skF_6') | r4_lattice3('#skF_5', B_334, C_335) | ~m1_subset_1(B_334, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_334, C_335), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3461])).
% 38.13/20.84  tff(c_3466, plain, (![B_336, C_337]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_336, C_337), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_336, C_337), '#skF_6') | r4_lattice3('#skF_5', B_336, C_337) | ~m1_subset_1(B_336, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_5', B_336, C_337), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_3464])).
% 38.13/20.84  tff(c_3470, plain, (![B_51, C_57]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | r4_lattice3('#skF_5', B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_3466])).
% 38.13/20.84  tff(c_3473, plain, (![B_51, C_57]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | r4_lattice3('#skF_5', B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3470])).
% 38.13/20.84  tff(c_3474, plain, (![B_51, C_57]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | ~r3_lattices('#skF_5', '#skF_2'('#skF_5', B_51, C_57), '#skF_6') | r4_lattice3('#skF_5', B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_3473])).
% 38.13/20.84  tff(c_8536, plain, (![B_502, C_503]: (r1_lattices('#skF_5', '#skF_2'('#skF_5', B_502, C_503), '#skF_6') | ~r2_hidden('#skF_2'('#skF_5', B_502, C_503), '#skF_4') | r4_lattice3('#skF_5', B_502, C_503) | ~m1_subset_1(B_502, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8525, c_3474])).
% 38.13/20.84  tff(c_36, plain, (![A_39, B_51, C_57]: (~r1_lattices(A_39, '#skF_2'(A_39, B_51, C_57), B_51) | r4_lattice3(A_39, B_51, C_57) | ~m1_subset_1(B_51, u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 38.13/20.84  tff(c_8540, plain, (![C_503]: (~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', C_503), '#skF_4') | r4_lattice3('#skF_5', '#skF_6', C_503) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8536, c_36])).
% 38.13/20.84  tff(c_8543, plain, (![C_503]: (v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', C_503), '#skF_4') | r4_lattice3('#skF_5', '#skF_6', C_503))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_8540])).
% 38.13/20.84  tff(c_8545, plain, (![C_504]: (~r2_hidden('#skF_2'('#skF_5', '#skF_6', C_504), '#skF_4') | r4_lattice3('#skF_5', '#skF_6', C_504))), inference(negUnitSimplification, [status(thm)], [c_58, c_8543])).
% 38.13/20.84  tff(c_8549, plain, (r4_lattice3('#skF_5', '#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_8545])).
% 38.13/20.84  tff(c_8552, plain, (r4_lattice3('#skF_5', '#skF_6', '#skF_4') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_8549])).
% 38.13/20.84  tff(c_8554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_71, c_8552])).
% 38.13/20.84  tff(c_8555, plain, (~r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 38.13/20.84  tff(c_8562, plain, (![A_509, B_510]: (k7_lattices(A_509, k7_lattices(A_509, B_510))=B_510 | ~m1_subset_1(B_510, u1_struct_0(A_509)) | ~l3_lattices(A_509) | ~v17_lattices(A_509) | ~v10_lattices(A_509) | v2_struct_0(A_509))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.13/20.84  tff(c_8566, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6' | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_8562])).
% 38.13/20.84  tff(c_8570, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_8566])).
% 38.13/20.84  tff(c_8571, plain, (k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_8570])).
% 38.13/20.84  tff(c_8612, plain, (![C_538, D_539, B_540]: (r2_hidden(k7_lattices(C_538, D_539), a_2_0_lattice3(B_540, C_538)) | ~r2_hidden(D_539, B_540) | ~m1_subset_1(D_539, u1_struct_0(C_538)) | ~l3_lattices(C_538) | ~v17_lattices(C_538) | ~v10_lattices(C_538) | v2_struct_0(C_538))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_8617, plain, (![B_540]: (r2_hidden('#skF_6', a_2_0_lattice3(B_540, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_540) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8571, c_8612])).
% 38.13/20.84  tff(c_8620, plain, (![B_540]: (r2_hidden('#skF_6', a_2_0_lattice3(B_540, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_540) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_8617])).
% 38.13/20.84  tff(c_8621, plain, (![B_540]: (r2_hidden('#skF_6', a_2_0_lattice3(B_540, '#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', '#skF_6'), B_540) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_8620])).
% 38.13/20.84  tff(c_8622, plain, (~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_8621])).
% 38.13/20.84  tff(c_8625, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_16, c_8622])).
% 38.13/20.84  tff(c_8628, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_8625])).
% 38.13/20.84  tff(c_8630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8628])).
% 38.13/20.84  tff(c_8632, plain, (m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_8621])).
% 38.13/20.84  tff(c_32, plain, (![A_17, B_29, C_35]: (m1_subset_1('#skF_1'(A_17, B_29, C_35), u1_struct_0(A_17)) | r3_lattice3(A_17, B_29, C_35) | ~m1_subset_1(B_29, u1_struct_0(A_17)) | ~l3_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.13/20.84  tff(c_30, plain, (![A_17, B_29, C_35]: (r2_hidden('#skF_1'(A_17, B_29, C_35), C_35) | r3_lattice3(A_17, B_29, C_35) | ~m1_subset_1(B_29, u1_struct_0(A_17)) | ~l3_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.13/20.84  tff(c_44, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_3'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, a_2_0_lattice3(B_62, C_63)) | ~l3_lattices(C_63) | ~v17_lattices(C_63) | ~v10_lattices(C_63) | v2_struct_0(C_63))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_8595, plain, (![C_532, A_533, B_534]: (k7_lattices(C_532, '#skF_3'(A_533, B_534, C_532))=A_533 | ~r2_hidden(A_533, a_2_0_lattice3(B_534, C_532)) | ~l3_lattices(C_532) | ~v17_lattices(C_532) | ~v10_lattices(C_532) | v2_struct_0(C_532))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_11630, plain, (![C_732, A_733, B_734, B_735]: (k7_lattices(C_732, '#skF_3'('#skF_1'(A_733, B_734, a_2_0_lattice3(B_735, C_732)), B_735, C_732))='#skF_1'(A_733, B_734, a_2_0_lattice3(B_735, C_732)) | ~l3_lattices(C_732) | ~v17_lattices(C_732) | ~v10_lattices(C_732) | v2_struct_0(C_732) | r3_lattice3(A_733, B_734, a_2_0_lattice3(B_735, C_732)) | ~m1_subset_1(B_734, u1_struct_0(A_733)) | ~l3_lattices(A_733) | v2_struct_0(A_733))), inference(resolution, [status(thm)], [c_30, c_8595])).
% 38.13/20.84  tff(c_8608, plain, (![A_535, B_536, C_537]: (m1_subset_1('#skF_3'(A_535, B_536, C_537), u1_struct_0(C_537)) | ~r2_hidden(A_535, a_2_0_lattice3(B_536, C_537)) | ~l3_lattices(C_537) | ~v17_lattices(C_537) | ~v10_lattices(C_537) | v2_struct_0(C_537))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_8611, plain, (![C_537, A_535, B_536]: (k7_lattices(C_537, k7_lattices(C_537, '#skF_3'(A_535, B_536, C_537)))='#skF_3'(A_535, B_536, C_537) | ~r2_hidden(A_535, a_2_0_lattice3(B_536, C_537)) | ~l3_lattices(C_537) | ~v17_lattices(C_537) | ~v10_lattices(C_537) | v2_struct_0(C_537))), inference(resolution, [status(thm)], [c_8608, c_22])).
% 38.13/20.84  tff(c_42061, plain, (![C_1357, A_1358, B_1359, B_1360]: (k7_lattices(C_1357, '#skF_1'(A_1358, B_1359, a_2_0_lattice3(B_1360, C_1357)))='#skF_3'('#skF_1'(A_1358, B_1359, a_2_0_lattice3(B_1360, C_1357)), B_1360, C_1357) | ~r2_hidden('#skF_1'(A_1358, B_1359, a_2_0_lattice3(B_1360, C_1357)), a_2_0_lattice3(B_1360, C_1357)) | ~l3_lattices(C_1357) | ~v17_lattices(C_1357) | ~v10_lattices(C_1357) | v2_struct_0(C_1357) | ~l3_lattices(C_1357) | ~v17_lattices(C_1357) | ~v10_lattices(C_1357) | v2_struct_0(C_1357) | r3_lattice3(A_1358, B_1359, a_2_0_lattice3(B_1360, C_1357)) | ~m1_subset_1(B_1359, u1_struct_0(A_1358)) | ~l3_lattices(A_1358) | v2_struct_0(A_1358))), inference(superposition, [status(thm), theory('equality')], [c_11630, c_8611])).
% 38.13/20.84  tff(c_93439, plain, (![C_2413, A_2414, B_2415, B_2416]: (k7_lattices(C_2413, '#skF_1'(A_2414, B_2415, a_2_0_lattice3(B_2416, C_2413)))='#skF_3'('#skF_1'(A_2414, B_2415, a_2_0_lattice3(B_2416, C_2413)), B_2416, C_2413) | ~l3_lattices(C_2413) | ~v17_lattices(C_2413) | ~v10_lattices(C_2413) | v2_struct_0(C_2413) | r3_lattice3(A_2414, B_2415, a_2_0_lattice3(B_2416, C_2413)) | ~m1_subset_1(B_2415, u1_struct_0(A_2414)) | ~l3_lattices(A_2414) | v2_struct_0(A_2414))), inference(resolution, [status(thm)], [c_30, c_42061])).
% 38.13/20.84  tff(c_8901, plain, (![A_565, B_566, C_567]: (r3_lattices(A_565, B_566, C_567) | ~r1_lattices(A_565, B_566, C_567) | ~m1_subset_1(C_567, u1_struct_0(A_565)) | ~m1_subset_1(B_566, u1_struct_0(A_565)) | ~l3_lattices(A_565) | ~v9_lattices(A_565) | ~v8_lattices(A_565) | ~v6_lattices(A_565) | v2_struct_0(A_565))), inference(cnfTransformation, [status(thm)], [f_75])).
% 38.13/20.84  tff(c_8913, plain, (![B_566]: (r3_lattices('#skF_5', B_566, '#skF_6') | ~r1_lattices('#skF_5', B_566, '#skF_6') | ~m1_subset_1(B_566, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_8901])).
% 38.13/20.84  tff(c_8924, plain, (![B_566]: (r3_lattices('#skF_5', B_566, '#skF_6') | ~r1_lattices('#skF_5', B_566, '#skF_6') | ~m1_subset_1(B_566, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8913])).
% 38.13/20.84  tff(c_8925, plain, (![B_566]: (r3_lattices('#skF_5', B_566, '#skF_6') | ~r1_lattices('#skF_5', B_566, '#skF_6') | ~m1_subset_1(B_566, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_8924])).
% 38.13/20.84  tff(c_8957, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_8925])).
% 38.13/20.84  tff(c_8961, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_8957])).
% 38.13/20.84  tff(c_8964, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_8961])).
% 38.13/20.84  tff(c_8966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8964])).
% 38.13/20.84  tff(c_8968, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_8925])).
% 38.13/20.84  tff(c_8967, plain, (![B_566]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_566, '#skF_6') | ~r1_lattices('#skF_5', B_566, '#skF_6') | ~m1_subset_1(B_566, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_8925])).
% 38.13/20.84  tff(c_8969, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_8967])).
% 38.13/20.84  tff(c_8972, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_8969])).
% 38.13/20.84  tff(c_8975, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_8972])).
% 38.13/20.84  tff(c_8977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8975])).
% 38.13/20.84  tff(c_8978, plain, (![B_566]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_566, '#skF_6') | ~r1_lattices('#skF_5', B_566, '#skF_6') | ~m1_subset_1(B_566, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_8967])).
% 38.13/20.84  tff(c_8981, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_8978])).
% 38.13/20.84  tff(c_8984, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_8981])).
% 38.13/20.84  tff(c_8987, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_8984])).
% 38.13/20.84  tff(c_8989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8987])).
% 38.13/20.84  tff(c_8991, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_8978])).
% 38.13/20.84  tff(c_8979, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_8967])).
% 38.13/20.84  tff(c_8585, plain, (![A_520, B_521, C_522]: (m1_subset_1('#skF_1'(A_520, B_521, C_522), u1_struct_0(A_520)) | r3_lattice3(A_520, B_521, C_522) | ~m1_subset_1(B_521, u1_struct_0(A_520)) | ~l3_lattices(A_520) | v2_struct_0(A_520))), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.13/20.84  tff(c_8588, plain, (![A_520, B_521, C_522]: (k7_lattices(A_520, k7_lattices(A_520, '#skF_1'(A_520, B_521, C_522)))='#skF_1'(A_520, B_521, C_522) | ~v17_lattices(A_520) | ~v10_lattices(A_520) | r3_lattice3(A_520, B_521, C_522) | ~m1_subset_1(B_521, u1_struct_0(A_520)) | ~l3_lattices(A_520) | v2_struct_0(A_520))), inference(resolution, [status(thm)], [c_8585, c_22])).
% 38.13/20.84  tff(c_8556, plain, (r4_lattice3('#skF_5', '#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 38.13/20.84  tff(c_48, plain, (![A_61, B_62, C_63]: (m1_subset_1('#skF_3'(A_61, B_62, C_63), u1_struct_0(C_63)) | ~r2_hidden(A_61, a_2_0_lattice3(B_62, C_63)) | ~l3_lattices(C_63) | ~v17_lattices(C_63) | ~v10_lattices(C_63) | v2_struct_0(C_63))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_8726, plain, (![A_546, D_547, B_548, C_549]: (r1_lattices(A_546, D_547, B_548) | ~r2_hidden(D_547, C_549) | ~m1_subset_1(D_547, u1_struct_0(A_546)) | ~r4_lattice3(A_546, B_548, C_549) | ~m1_subset_1(B_548, u1_struct_0(A_546)) | ~l3_lattices(A_546) | v2_struct_0(A_546))), inference(cnfTransformation, [status(thm)], [f_144])).
% 38.13/20.84  tff(c_11991, plain, (![B_779, B_778, A_780, C_777, A_781]: (r1_lattices(A_781, '#skF_3'(A_780, B_778, C_777), B_779) | ~m1_subset_1('#skF_3'(A_780, B_778, C_777), u1_struct_0(A_781)) | ~r4_lattice3(A_781, B_779, B_778) | ~m1_subset_1(B_779, u1_struct_0(A_781)) | ~l3_lattices(A_781) | v2_struct_0(A_781) | ~r2_hidden(A_780, a_2_0_lattice3(B_778, C_777)) | ~l3_lattices(C_777) | ~v17_lattices(C_777) | ~v10_lattices(C_777) | v2_struct_0(C_777))), inference(resolution, [status(thm)], [c_44, c_8726])).
% 38.13/20.84  tff(c_11994, plain, (![C_63, A_61, B_62, B_779]: (r1_lattices(C_63, '#skF_3'(A_61, B_62, C_63), B_779) | ~r4_lattice3(C_63, B_779, B_62) | ~m1_subset_1(B_779, u1_struct_0(C_63)) | ~r2_hidden(A_61, a_2_0_lattice3(B_62, C_63)) | ~l3_lattices(C_63) | ~v17_lattices(C_63) | ~v10_lattices(C_63) | v2_struct_0(C_63))), inference(resolution, [status(thm)], [c_48, c_11991])).
% 38.13/20.84  tff(c_9001, plain, (![B_573]: (r3_lattices('#skF_5', B_573, '#skF_6') | ~r1_lattices('#skF_5', B_573, '#skF_6') | ~m1_subset_1(B_573, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_8978])).
% 38.13/20.84  tff(c_9008, plain, (![A_61, B_62]: (r3_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r1_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r2_hidden(A_61, a_2_0_lattice3(B_62, '#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_9001])).
% 38.13/20.84  tff(c_9027, plain, (![A_61, B_62]: (r3_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r1_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r2_hidden(A_61, a_2_0_lattice3(B_62, '#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_9008])).
% 38.13/20.84  tff(c_9028, plain, (![A_61, B_62]: (r3_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r1_lattices('#skF_5', '#skF_3'(A_61, B_62, '#skF_5'), '#skF_6') | ~r2_hidden(A_61, a_2_0_lattice3(B_62, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_9027])).
% 38.13/20.84  tff(c_46, plain, (![C_63, A_61, B_62]: (k7_lattices(C_63, '#skF_3'(A_61, B_62, C_63))=A_61 | ~r2_hidden(A_61, a_2_0_lattice3(B_62, C_63)) | ~l3_lattices(C_63) | ~v17_lattices(C_63) | ~v10_lattices(C_63) | v2_struct_0(C_63))), inference(cnfTransformation, [status(thm)], [f_162])).
% 38.13/20.84  tff(c_8618, plain, (![C_538, D_539, B_540]: (k7_lattices(C_538, '#skF_3'(k7_lattices(C_538, D_539), B_540, C_538))=k7_lattices(C_538, D_539) | ~r2_hidden(D_539, B_540) | ~m1_subset_1(D_539, u1_struct_0(C_538)) | ~l3_lattices(C_538) | ~v17_lattices(C_538) | ~v10_lattices(C_538) | v2_struct_0(C_538))), inference(resolution, [status(thm)], [c_8612, c_46])).
% 38.13/20.84  tff(c_8567, plain, (![A_2, B_3]: (k7_lattices(A_2, k7_lattices(A_2, k7_lattices(A_2, B_3)))=k7_lattices(A_2, B_3) | ~v17_lattices(A_2) | ~v10_lattices(A_2) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(resolution, [status(thm)], [c_16, c_8562])).
% 38.13/20.84  tff(c_9044, plain, (![A_574, C_575, B_576]: (r3_lattices(A_574, k7_lattices(A_574, C_575), k7_lattices(A_574, B_576)) | ~r3_lattices(A_574, B_576, C_575) | ~m1_subset_1(C_575, u1_struct_0(A_574)) | ~m1_subset_1(B_576, u1_struct_0(A_574)) | ~l3_lattices(A_574) | ~v17_lattices(A_574) | ~v10_lattices(A_574) | v2_struct_0(A_574))), inference(cnfTransformation, [status(thm)], [f_108])).
% 38.13/20.84  tff(c_25661, plain, (![A_1022, B_1023, B_1024]: (r3_lattices(A_1022, k7_lattices(A_1022, B_1023), k7_lattices(A_1022, B_1024)) | ~r3_lattices(A_1022, B_1024, k7_lattices(A_1022, k7_lattices(A_1022, B_1023))) | ~m1_subset_1(k7_lattices(A_1022, k7_lattices(A_1022, B_1023)), u1_struct_0(A_1022)) | ~m1_subset_1(B_1024, u1_struct_0(A_1022)) | ~l3_lattices(A_1022) | ~v17_lattices(A_1022) | ~v10_lattices(A_1022) | v2_struct_0(A_1022) | ~v17_lattices(A_1022) | ~v10_lattices(A_1022) | ~m1_subset_1(B_1023, u1_struct_0(A_1022)) | ~l3_lattices(A_1022) | v2_struct_0(A_1022))), inference(superposition, [status(thm), theory('equality')], [c_8567, c_9044])).
% 38.13/20.84  tff(c_25722, plain, (![B_1024]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_1024)) | ~r3_lattices('#skF_5', B_1024, '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6')), u1_struct_0('#skF_5')) | ~m1_subset_1(B_1024, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8571, c_25661])).
% 38.13/20.84  tff(c_25737, plain, (![B_1024]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_1024)) | ~r3_lattices('#skF_5', B_1024, '#skF_6') | ~m1_subset_1(B_1024, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_56, c_54, c_56, c_54, c_52, c_50, c_8571, c_25722])).
% 38.13/20.84  tff(c_25739, plain, (![B_1025]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', B_1025)) | ~r3_lattices('#skF_5', B_1025, '#skF_6') | ~m1_subset_1(B_1025, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_25737])).
% 38.13/20.84  tff(c_25807, plain, (![D_539, B_540]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_539)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_539), B_540, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'(k7_lattices('#skF_5', D_539), B_540, '#skF_5'), u1_struct_0('#skF_5')) | ~r2_hidden(D_539, B_540) | ~m1_subset_1(D_539, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8618, c_25739])).
% 38.13/20.84  tff(c_25874, plain, (![D_539, B_540]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_539)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_539), B_540, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'(k7_lattices('#skF_5', D_539), B_540, '#skF_5'), u1_struct_0('#skF_5')) | ~r2_hidden(D_539, B_540) | ~m1_subset_1(D_539, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_25807])).
% 38.13/20.84  tff(c_29943, plain, (![D_1087, B_1088]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1087)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_1087), B_1088, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'(k7_lattices('#skF_5', D_1087), B_1088, '#skF_5'), u1_struct_0('#skF_5')) | ~r2_hidden(D_1087, B_1088) | ~m1_subset_1(D_1087, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_25874])).
% 38.13/20.84  tff(c_30019, plain, (![D_1087, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1087)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_1087), B_62, '#skF_5'), '#skF_6') | ~r2_hidden(D_1087, B_62) | ~m1_subset_1(D_1087, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', D_1087), a_2_0_lattice3(B_62, '#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_29943])).
% 38.13/20.84  tff(c_30079, plain, (![D_1087, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1087)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_1087), B_62, '#skF_5'), '#skF_6') | ~r2_hidden(D_1087, B_62) | ~m1_subset_1(D_1087, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', D_1087), a_2_0_lattice3(B_62, '#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_30019])).
% 38.13/20.84  tff(c_30089, plain, (![D_1093, B_1094]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1093)) | ~r3_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_1093), B_1094, '#skF_5'), '#skF_6') | ~r2_hidden(D_1093, B_1094) | ~m1_subset_1(D_1093, u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', D_1093), a_2_0_lattice3(B_1094, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_30079])).
% 38.13/20.84  tff(c_30231, plain, (![D_1095, B_1096]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1095)) | ~r2_hidden(D_1095, B_1096) | ~m1_subset_1(D_1095, u1_struct_0('#skF_5')) | ~r1_lattices('#skF_5', '#skF_3'(k7_lattices('#skF_5', D_1095), B_1096, '#skF_5'), '#skF_6') | ~r2_hidden(k7_lattices('#skF_5', D_1095), a_2_0_lattice3(B_1096, '#skF_5')))), inference(resolution, [status(thm)], [c_9028, c_30089])).
% 38.13/20.84  tff(c_30276, plain, (![D_1095, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1095)) | ~r2_hidden(D_1095, B_62) | ~m1_subset_1(D_1095, u1_struct_0('#skF_5')) | ~r4_lattice3('#skF_5', '#skF_6', B_62) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k7_lattices('#skF_5', D_1095), a_2_0_lattice3(B_62, '#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_11994, c_30231])).
% 38.13/20.84  tff(c_30338, plain, (![D_1095, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1095)) | ~r2_hidden(D_1095, B_62) | ~m1_subset_1(D_1095, u1_struct_0('#skF_5')) | ~r4_lattice3('#skF_5', '#skF_6', B_62) | ~r2_hidden(k7_lattices('#skF_5', D_1095), a_2_0_lattice3(B_62, '#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_30276])).
% 38.13/20.84  tff(c_30361, plain, (![D_1097, B_1098]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1097)) | ~r2_hidden(D_1097, B_1098) | ~m1_subset_1(D_1097, u1_struct_0('#skF_5')) | ~r4_lattice3('#skF_5', '#skF_6', B_1098) | ~r2_hidden(k7_lattices('#skF_5', D_1097), a_2_0_lattice3(B_1098, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_30338])).
% 38.13/20.84  tff(c_30406, plain, (![D_66, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_66)) | ~r4_lattice3('#skF_5', '#skF_6', B_62) | ~r2_hidden(D_66, B_62) | ~m1_subset_1(D_66, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_30361])).
% 38.13/20.84  tff(c_30453, plain, (![D_66, B_62]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_66)) | ~r4_lattice3('#skF_5', '#skF_6', B_62) | ~r2_hidden(D_66, B_62) | ~m1_subset_1(D_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_30406])).
% 38.13/20.84  tff(c_30458, plain, (![D_1099, B_1100]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1099)) | ~r4_lattice3('#skF_5', '#skF_6', B_1100) | ~r2_hidden(D_1099, B_1100) | ~m1_subset_1(D_1099, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_30453])).
% 38.13/20.84  tff(c_30462, plain, (![D_1101]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), k7_lattices('#skF_5', D_1101)) | ~r2_hidden(D_1101, '#skF_4') | ~m1_subset_1(D_1101, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8556, c_30458])).
% 38.13/20.84  tff(c_30526, plain, (![B_521, C_522]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_521, C_522)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_521, C_522)), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_521, C_522)), u1_struct_0('#skF_5')) | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | r3_lattice3('#skF_5', B_521, C_522) | ~m1_subset_1(B_521, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8588, c_30462])).
% 38.13/20.84  tff(c_30594, plain, (![B_521, C_522]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_521, C_522)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_521, C_522)), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_521, C_522)), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', B_521, C_522) | ~m1_subset_1(B_521, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_30526])).
% 38.13/20.84  tff(c_38708, plain, (![B_1218, C_1219]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1218, C_1219)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1218, C_1219)), '#skF_4') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1218, C_1219)), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', B_1218, C_1219) | ~m1_subset_1(B_1218, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_30594])).
% 38.13/20.84  tff(c_38711, plain, (![B_1218, C_1219]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1218, C_1219)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1218, C_1219)), '#skF_4') | r3_lattice3('#skF_5', B_1218, C_1219) | ~m1_subset_1(B_1218, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1218, C_1219), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_38708])).
% 38.13/20.84  tff(c_38714, plain, (![B_1218, C_1219]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1218, C_1219)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1218, C_1219)), '#skF_4') | r3_lattice3('#skF_5', B_1218, C_1219) | ~m1_subset_1(B_1218, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1218, C_1219), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38711])).
% 38.13/20.84  tff(c_38716, plain, (![B_1220, C_1221]: (r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1220, C_1221)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1220, C_1221)), '#skF_4') | r3_lattice3('#skF_5', B_1220, C_1221) | ~m1_subset_1(B_1220, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1220, C_1221), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_38714])).
% 38.13/20.84  tff(c_38723, plain, (![B_1220, C_1221]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1220, C_1221)) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1220, C_1221)), '#skF_4') | r3_lattice3('#skF_5', B_1220, C_1221) | ~m1_subset_1(B_1220, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1220, C_1221), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_38716, c_20])).
% 38.13/20.84  tff(c_38728, plain, (![B_1220, C_1221]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1220, C_1221)) | v2_struct_0('#skF_5') | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1220, C_1221)), '#skF_4') | r3_lattice3('#skF_5', B_1220, C_1221) | ~m1_subset_1(B_1220, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1220, C_1221), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8968, c_8991, c_8979, c_52, c_8632, c_38723])).
% 38.13/20.84  tff(c_38730, plain, (![B_1222, C_1223]: (r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_6'), '#skF_1'('#skF_5', B_1222, C_1223)) | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', B_1222, C_1223)), '#skF_4') | r3_lattice3('#skF_5', B_1222, C_1223) | ~m1_subset_1(B_1222, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', B_1222, C_1223), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_38728])).
% 38.13/20.84  tff(c_28, plain, (![A_17, B_29, C_35]: (~r1_lattices(A_17, B_29, '#skF_1'(A_17, B_29, C_35)) | r3_lattice3(A_17, B_29, C_35) | ~m1_subset_1(B_29, u1_struct_0(A_17)) | ~l3_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.13/20.84  tff(c_38734, plain, (![C_1223]: (~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223)), '#skF_4') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_38730, c_28])).
% 38.13/20.84  tff(c_38737, plain, (![C_1223]: (v2_struct_0('#skF_5') | ~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223)), '#skF_4') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223) | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_52, c_38734])).
% 38.13/20.84  tff(c_38738, plain, (![C_1223]: (~r2_hidden(k7_lattices('#skF_5', '#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223)), '#skF_4') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223) | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), C_1223), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_38737])).
% 38.13/20.84  tff(c_94498, plain, (![B_2416]: (~r2_hidden('#skF_3'('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')), B_2416, '#skF_5'), '#skF_4') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_93439, c_38738])).
% 38.13/20.84  tff(c_96046, plain, (![B_2416]: (~r2_hidden('#skF_3'('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')), B_2416, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2416, '#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8632, c_56, c_54, c_52, c_94498])).
% 38.13/20.84  tff(c_96548, plain, (![B_2417]: (~r2_hidden('#skF_3'('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2417, '#skF_5')), B_2417, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2417, '#skF_5')), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3(B_2417, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_96046])).
% 38.13/20.84  tff(c_96556, plain, (~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), a_2_0_lattice3('#skF_4', '#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_96548])).
% 38.13/20.84  tff(c_96562, plain, (~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), a_2_0_lattice3('#skF_4', '#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_96556])).
% 38.13/20.84  tff(c_96563, plain, (~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), a_2_0_lattice3('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_8555, c_96562])).
% 38.13/20.84  tff(c_96564, plain, (~r2_hidden('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), a_2_0_lattice3('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_96563])).
% 38.13/20.84  tff(c_96567, plain, (r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_96564])).
% 38.13/20.84  tff(c_96570, plain, (r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8632, c_96567])).
% 38.13/20.84  tff(c_96572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8555, c_96570])).
% 38.13/20.84  tff(c_96573, plain, (~m1_subset_1('#skF_1'('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_96563])).
% 38.13/20.84  tff(c_96577, plain, (r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_96573])).
% 38.13/20.84  tff(c_96580, plain, (r3_lattice3('#skF_5', k7_lattices('#skF_5', '#skF_6'), a_2_0_lattice3('#skF_4', '#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8632, c_96577])).
% 38.13/20.84  tff(c_96582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8555, c_96580])).
% 38.13/20.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.13/20.84  
% 38.13/20.84  Inference rules
% 38.13/20.84  ----------------------
% 38.13/20.84  #Ref     : 0
% 38.13/20.84  #Sup     : 15624
% 38.13/20.84  #Fact    : 0
% 38.13/20.84  #Define  : 0
% 38.13/20.84  #Split   : 26
% 38.13/20.84  #Chain   : 0
% 38.13/20.84  #Close   : 0
% 38.13/20.84  
% 38.13/20.84  Ordering : KBO
% 38.13/20.84  
% 38.13/20.84  Simplification rules
% 38.13/20.84  ----------------------
% 38.13/20.84  #Subsume      : 3808
% 38.13/20.84  #Demod        : 40223
% 38.13/20.84  #Tautology    : 456
% 38.13/20.84  #SimpNegUnit  : 12612
% 38.13/20.84  #BackRed      : 2
% 38.13/20.84  
% 38.13/20.84  #Partial instantiations: 0
% 38.13/20.84  #Strategies tried      : 1
% 38.13/20.84  
% 38.13/20.84  Timing (in seconds)
% 38.13/20.84  ----------------------
% 38.13/20.84  Preprocessing        : 0.35
% 38.13/20.84  Parsing              : 0.18
% 38.13/20.84  CNF conversion       : 0.03
% 38.13/20.84  Main loop            : 19.67
% 38.13/20.84  Inferencing          : 4.25
% 38.13/20.84  Reduction            : 5.36
% 38.13/20.84  Demodulation         : 3.61
% 38.13/20.84  BG Simplification    : 0.47
% 38.13/20.84  Subsumption          : 8.73
% 38.13/20.84  Abstraction          : 0.78
% 38.13/20.84  MUC search           : 0.00
% 38.13/20.84  Cooper               : 0.00
% 38.13/20.84  Total                : 20.10
% 38.13/20.84  Index Insertion      : 0.00
% 38.13/20.84  Index Deletion       : 0.00
% 38.13/20.84  Index Matching       : 0.00
% 38.13/20.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
