%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1508+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:58 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 195 expanded)
%              Number of leaves         :   34 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  281 ( 899 expanded)
%              Number of equality atoms :    9 (  47 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

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

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_153,negated_conjecture,(
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

tff(f_46,axiom,(
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

tff(f_78,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
             => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_116,axiom,(
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

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k16_lattice3('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    v4_lattice3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_55,B_56,C_57] :
      ( r3_lattices(A_55,B_56,C_57)
      | ~ r1_lattices(A_55,B_56,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l3_lattices(A_55)
      | ~ v9_lattices(A_55)
      | ~ v8_lattices(A_55)
      | ~ v6_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    ! [B_56] :
      ( r3_lattices('#skF_1',B_56,'#skF_2')
      | ~ r1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_78,plain,(
    ! [B_56] :
      ( r3_lattices('#skF_1',B_56,'#skF_2')
      | ~ r1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_79,plain,(
    ! [B_56] :
      ( r3_lattices('#skF_1',B_56,'#skF_2')
      | ~ r1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_80,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_93,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_96,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_96])).

tff(c_100,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [B_56] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_56,'#skF_2')
      | ~ r1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_101,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_104,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_101])).

tff(c_107,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_107])).

tff(c_110,plain,(
    ! [B_56] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_56,'#skF_2')
      | ~ r1_lattices('#skF_1',B_56,'#skF_2')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_112,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_115,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_118,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_115])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_118])).

tff(c_122,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_111,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_38,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    ! [A_34] :
      ( l2_lattices(A_34)
      | ~ l3_lattices(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_36,plain,(
    r3_lattice3('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_16,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k16_lattice3(A_2,B_3),u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_22,B_26,C_28] :
      ( r3_lattices(A_22,B_26,k16_lattice3(A_22,C_28))
      | ~ r3_lattice3(A_22,B_26,C_28)
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l3_lattices(A_22)
      | ~ v4_lattice3(A_22)
      | ~ v10_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_136,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_lattices(A_62,B_63,C_64)
      | ~ r3_lattices(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l3_lattices(A_62)
      | ~ v9_lattices(A_62)
      | ~ v8_lattices(A_62)
      | ~ v6_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_167,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_lattices(A_78,B_79,k16_lattice3(A_78,C_80))
      | ~ m1_subset_1(k16_lattice3(A_78,C_80),u1_struct_0(A_78))
      | ~ v9_lattices(A_78)
      | ~ v8_lattices(A_78)
      | ~ v6_lattices(A_78)
      | ~ r3_lattice3(A_78,B_79,C_80)
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l3_lattices(A_78)
      | ~ v4_lattice3(A_78)
      | ~ v10_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_170,plain,(
    ! [A_2,B_79,B_3] :
      ( r1_lattices(A_2,B_79,k16_lattice3(A_2,B_3))
      | ~ v9_lattices(A_2)
      | ~ v8_lattices(A_2)
      | ~ v6_lattices(A_2)
      | ~ r3_lattice3(A_2,B_79,B_3)
      | ~ m1_subset_1(B_79,u1_struct_0(A_2))
      | ~ v4_lattice3(A_2)
      | ~ v10_lattices(A_2)
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_28,plain,(
    ! [A_15,C_21,B_19] :
      ( r3_lattices(A_15,k16_lattice3(A_15,C_21),B_19)
      | ~ r2_hidden(B_19,C_21)
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l3_lattices(A_15)
      | ~ v4_lattice3(A_15)
      | ~ v10_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_158,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_lattices(A_69,k16_lattice3(A_69,C_70),B_71)
      | ~ m1_subset_1(k16_lattice3(A_69,C_70),u1_struct_0(A_69))
      | ~ v9_lattices(A_69)
      | ~ v8_lattices(A_69)
      | ~ v6_lattices(A_69)
      | ~ r2_hidden(B_71,C_70)
      | ~ m1_subset_1(B_71,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_162,plain,(
    ! [A_72,B_73,B_74] :
      ( r1_lattices(A_72,k16_lattice3(A_72,B_73),B_74)
      | ~ v9_lattices(A_72)
      | ~ v8_lattices(A_72)
      | ~ v6_lattices(A_72)
      | ~ r2_hidden(B_74,B_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_72))
      | ~ v4_lattice3(A_72)
      | ~ v10_lattices(A_72)
      | ~ l3_lattices(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_16,c_158])).

tff(c_26,plain,(
    ! [C_14,B_12,A_8] :
      ( C_14 = B_12
      | ~ r1_lattices(A_8,C_14,B_12)
      | ~ r1_lattices(A_8,B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ m1_subset_1(B_12,u1_struct_0(A_8))
      | ~ l2_lattices(A_8)
      | ~ v4_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_175,plain,(
    ! [A_84,B_85,B_86] :
      ( k16_lattice3(A_84,B_85) = B_86
      | ~ r1_lattices(A_84,B_86,k16_lattice3(A_84,B_85))
      | ~ m1_subset_1(k16_lattice3(A_84,B_85),u1_struct_0(A_84))
      | ~ l2_lattices(A_84)
      | ~ v4_lattices(A_84)
      | ~ v9_lattices(A_84)
      | ~ v8_lattices(A_84)
      | ~ v6_lattices(A_84)
      | ~ r2_hidden(B_86,B_85)
      | ~ m1_subset_1(B_86,u1_struct_0(A_84))
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_162,c_26])).

tff(c_183,plain,(
    ! [A_87,B_88,B_89] :
      ( k16_lattice3(A_87,B_88) = B_89
      | ~ m1_subset_1(k16_lattice3(A_87,B_88),u1_struct_0(A_87))
      | ~ l2_lattices(A_87)
      | ~ v4_lattices(A_87)
      | ~ r2_hidden(B_89,B_88)
      | ~ v9_lattices(A_87)
      | ~ v8_lattices(A_87)
      | ~ v6_lattices(A_87)
      | ~ r3_lattice3(A_87,B_89,B_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_87))
      | ~ v4_lattice3(A_87)
      | ~ v10_lattices(A_87)
      | ~ l3_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_170,c_175])).

tff(c_187,plain,(
    ! [A_90,B_91,B_92] :
      ( k16_lattice3(A_90,B_91) = B_92
      | ~ l2_lattices(A_90)
      | ~ v4_lattices(A_90)
      | ~ r2_hidden(B_92,B_91)
      | ~ v9_lattices(A_90)
      | ~ v8_lattices(A_90)
      | ~ v6_lattices(A_90)
      | ~ r3_lattice3(A_90,B_92,B_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_90))
      | ~ v4_lattice3(A_90)
      | ~ v10_lattices(A_90)
      | ~ l3_lattices(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_16,c_183])).

tff(c_189,plain,
    ( k16_lattice3('#skF_1','#skF_3') = '#skF_2'
    | ~ l2_lattices('#skF_1')
    | ~ v4_lattices('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ v4_lattice3('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_187])).

tff(c_192,plain,
    ( k16_lattice3('#skF_1','#skF_3') = '#skF_2'
    | ~ v4_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_40,c_100,c_122,c_111,c_38,c_58,c_189])).

tff(c_193,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34,c_192])).

tff(c_196,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_199,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_196])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_199])).

%------------------------------------------------------------------------------
