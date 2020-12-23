%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:48 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
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

tff(f_154,negated_conjecture,(
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

tff(f_72,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_134,axiom,(
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

tff(f_117,axiom,(
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

tff(f_91,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    k16_lattice3('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v4_lattice3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_58,B_59,C_60] :
      ( r3_lattices(A_58,B_59,C_60)
      | ~ r1_lattices(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l3_lattices(A_58)
      | ~ v9_lattices(A_58)
      | ~ v8_lattices(A_58)
      | ~ v6_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [B_59] :
      ( r3_lattices('#skF_1',B_59,'#skF_2')
      | ~ r1_lattices('#skF_1',B_59,'#skF_2')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_88,plain,(
    ! [B_59] :
      ( r3_lattices('#skF_1',B_59,'#skF_2')
      | ~ r1_lattices('#skF_1',B_59,'#skF_2')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_89,plain,(
    ! [B_59] :
      ( r3_lattices('#skF_1',B_59,'#skF_2')
      | ~ r1_lattices('#skF_1',B_59,'#skF_2')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_88])).

tff(c_90,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_93,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_96,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_96])).

tff(c_100,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_89])).

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

tff(c_99,plain,(
    ! [B_59] :
      ( ~ v8_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | r3_lattices('#skF_1',B_59,'#skF_2')
      | ~ r1_lattices('#skF_1',B_59,'#skF_2')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_89])).

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
    ! [B_59] :
      ( ~ v8_lattices('#skF_1')
      | r3_lattices('#skF_1',B_59,'#skF_2')
      | ~ r1_lattices('#skF_1',B_59,'#skF_2')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_1')) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_49,plain,(
    ! [A_33] :
      ( l2_lattices(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_36,plain,(
    r3_lattice3('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k16_lattice3(A_13,B_14),u1_struct_0(A_13))
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [A_22,B_26,C_28] :
      ( r3_lattices(A_22,B_26,k16_lattice3(A_22,C_28))
      | ~ r3_lattice3(A_22,B_26,C_28)
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l3_lattices(A_22)
      | ~ v4_lattice3(A_22)
      | ~ v10_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_70,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_lattices(A_55,B_56,C_57)
      | ~ r3_lattices(A_55,B_56,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l3_lattices(A_55)
      | ~ v9_lattices(A_55)
      | ~ v8_lattices(A_55)
      | ~ v6_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_lattices(A_75,B_76,k16_lattice3(A_75,C_77))
      | ~ m1_subset_1(k16_lattice3(A_75,C_77),u1_struct_0(A_75))
      | ~ v9_lattices(A_75)
      | ~ v8_lattices(A_75)
      | ~ v6_lattices(A_75)
      | ~ r3_lattice3(A_75,B_76,C_77)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l3_lattices(A_75)
      | ~ v4_lattice3(A_75)
      | ~ v10_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_160,plain,(
    ! [A_13,B_76,B_14] :
      ( r1_lattices(A_13,B_76,k16_lattice3(A_13,B_14))
      | ~ v9_lattices(A_13)
      | ~ v8_lattices(A_13)
      | ~ v6_lattices(A_13)
      | ~ r3_lattice3(A_13,B_76,B_14)
      | ~ m1_subset_1(B_76,u1_struct_0(A_13))
      | ~ v4_lattice3(A_13)
      | ~ v10_lattices(A_13)
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_28,plain,(
    ! [A_15,C_21,B_19] :
      ( r3_lattices(A_15,k16_lattice3(A_15,C_21),B_19)
      | ~ r2_hidden(B_19,C_21)
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l3_lattices(A_15)
      | ~ v4_lattice3(A_15)
      | ~ v10_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_148,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_lattices(A_66,k16_lattice3(A_66,C_67),B_68)
      | ~ m1_subset_1(k16_lattice3(A_66,C_67),u1_struct_0(A_66))
      | ~ v9_lattices(A_66)
      | ~ v8_lattices(A_66)
      | ~ v6_lattices(A_66)
      | ~ r2_hidden(B_68,C_67)
      | ~ m1_subset_1(B_68,u1_struct_0(A_66))
      | ~ l3_lattices(A_66)
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_152,plain,(
    ! [A_69,B_70,B_71] :
      ( r1_lattices(A_69,k16_lattice3(A_69,B_70),B_71)
      | ~ v9_lattices(A_69)
      | ~ v8_lattices(A_69)
      | ~ v6_lattices(A_69)
      | ~ r2_hidden(B_71,B_70)
      | ~ m1_subset_1(B_71,u1_struct_0(A_69))
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | ~ l3_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_24,plain,(
    ! [C_12,B_10,A_6] :
      ( C_12 = B_10
      | ~ r1_lattices(A_6,C_12,B_10)
      | ~ r1_lattices(A_6,B_10,C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(B_10,u1_struct_0(A_6))
      | ~ l2_lattices(A_6)
      | ~ v4_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_165,plain,(
    ! [A_81,B_82,B_83] :
      ( k16_lattice3(A_81,B_82) = B_83
      | ~ r1_lattices(A_81,B_83,k16_lattice3(A_81,B_82))
      | ~ m1_subset_1(k16_lattice3(A_81,B_82),u1_struct_0(A_81))
      | ~ l2_lattices(A_81)
      | ~ v4_lattices(A_81)
      | ~ v9_lattices(A_81)
      | ~ v8_lattices(A_81)
      | ~ v6_lattices(A_81)
      | ~ r2_hidden(B_83,B_82)
      | ~ m1_subset_1(B_83,u1_struct_0(A_81))
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_152,c_24])).

tff(c_181,plain,(
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
    inference(resolution,[status(thm)],[c_160,c_165])).

tff(c_185,plain,(
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
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_187,plain,
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
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_190,plain,
    ( k16_lattice3('#skF_1','#skF_3') = '#skF_2'
    | ~ v4_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_40,c_100,c_122,c_111,c_38,c_53,c_187])).

tff(c_191,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34,c_190])).

tff(c_194,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_197,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:31:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  
% 2.30/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.28  
% 2.30/1.28  %Foreground sorts:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Background operators:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Foreground operators:
% 2.30/1.28  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.30/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.28  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.30/1.28  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.28  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.30/1.28  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 2.30/1.28  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.30/1.28  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.30/1.28  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.30/1.28  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.30/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.28  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.30/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.28  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.30/1.28  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.30/1.28  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.28  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.28  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.30/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.28  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.30/1.28  
% 2.30/1.30  tff(f_154, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 2.30/1.30  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.30/1.30  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.30/1.30  tff(f_53, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.30/1.30  tff(f_98, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 2.30/1.30  tff(f_134, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 2.30/1.30  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 2.30/1.30  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 2.30/1.30  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_42, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_46, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.30  tff(c_34, plain, (k16_lattice3('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_44, plain, (v4_lattice3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.30  tff(c_80, plain, (![A_58, B_59, C_60]: (r3_lattices(A_58, B_59, C_60) | ~r1_lattices(A_58, B_59, C_60) | ~m1_subset_1(C_60, u1_struct_0(A_58)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l3_lattices(A_58) | ~v9_lattices(A_58) | ~v8_lattices(A_58) | ~v6_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.30  tff(c_84, plain, (![B_59]: (r3_lattices('#skF_1', B_59, '#skF_2') | ~r1_lattices('#skF_1', B_59, '#skF_2') | ~m1_subset_1(B_59, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.30/1.30  tff(c_88, plain, (![B_59]: (r3_lattices('#skF_1', B_59, '#skF_2') | ~r1_lattices('#skF_1', B_59, '#skF_2') | ~m1_subset_1(B_59, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_84])).
% 2.30/1.30  tff(c_89, plain, (![B_59]: (r3_lattices('#skF_1', B_59, '#skF_2') | ~r1_lattices('#skF_1', B_59, '#skF_2') | ~m1_subset_1(B_59, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_88])).
% 2.30/1.30  tff(c_90, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_89])).
% 2.30/1.30  tff(c_93, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_90])).
% 2.30/1.30  tff(c_96, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_93])).
% 2.30/1.30  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_96])).
% 2.30/1.30  tff(c_100, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_89])).
% 2.30/1.30  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.30  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.30  tff(c_99, plain, (![B_59]: (~v8_lattices('#skF_1') | ~v9_lattices('#skF_1') | r3_lattices('#skF_1', B_59, '#skF_2') | ~r1_lattices('#skF_1', B_59, '#skF_2') | ~m1_subset_1(B_59, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_89])).
% 2.30/1.30  tff(c_101, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_99])).
% 2.30/1.30  tff(c_104, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_101])).
% 2.30/1.30  tff(c_107, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_104])).
% 2.30/1.30  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_107])).
% 2.30/1.30  tff(c_110, plain, (![B_59]: (~v8_lattices('#skF_1') | r3_lattices('#skF_1', B_59, '#skF_2') | ~r1_lattices('#skF_1', B_59, '#skF_2') | ~m1_subset_1(B_59, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_99])).
% 2.30/1.30  tff(c_112, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_110])).
% 2.30/1.30  tff(c_115, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_112])).
% 2.30/1.30  tff(c_118, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_115])).
% 2.30/1.30  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_118])).
% 2.30/1.30  tff(c_122, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_110])).
% 2.30/1.30  tff(c_111, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_99])).
% 2.30/1.30  tff(c_38, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_49, plain, (![A_33]: (l2_lattices(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.30  tff(c_53, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.30/1.30  tff(c_36, plain, (r3_lattice3('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.30/1.30  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(k16_lattice3(A_13, B_14), u1_struct_0(A_13)) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.30/1.30  tff(c_32, plain, (![A_22, B_26, C_28]: (r3_lattices(A_22, B_26, k16_lattice3(A_22, C_28)) | ~r3_lattice3(A_22, B_26, C_28) | ~m1_subset_1(B_26, u1_struct_0(A_22)) | ~l3_lattices(A_22) | ~v4_lattice3(A_22) | ~v10_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.30/1.30  tff(c_70, plain, (![A_55, B_56, C_57]: (r1_lattices(A_55, B_56, C_57) | ~r3_lattices(A_55, B_56, C_57) | ~m1_subset_1(C_57, u1_struct_0(A_55)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l3_lattices(A_55) | ~v9_lattices(A_55) | ~v8_lattices(A_55) | ~v6_lattices(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.30  tff(c_157, plain, (![A_75, B_76, C_77]: (r1_lattices(A_75, B_76, k16_lattice3(A_75, C_77)) | ~m1_subset_1(k16_lattice3(A_75, C_77), u1_struct_0(A_75)) | ~v9_lattices(A_75) | ~v8_lattices(A_75) | ~v6_lattices(A_75) | ~r3_lattice3(A_75, B_76, C_77) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l3_lattices(A_75) | ~v4_lattice3(A_75) | ~v10_lattices(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_32, c_70])).
% 2.30/1.30  tff(c_160, plain, (![A_13, B_76, B_14]: (r1_lattices(A_13, B_76, k16_lattice3(A_13, B_14)) | ~v9_lattices(A_13) | ~v8_lattices(A_13) | ~v6_lattices(A_13) | ~r3_lattice3(A_13, B_76, B_14) | ~m1_subset_1(B_76, u1_struct_0(A_13)) | ~v4_lattice3(A_13) | ~v10_lattices(A_13) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_26, c_157])).
% 2.30/1.30  tff(c_28, plain, (![A_15, C_21, B_19]: (r3_lattices(A_15, k16_lattice3(A_15, C_21), B_19) | ~r2_hidden(B_19, C_21) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l3_lattices(A_15) | ~v4_lattice3(A_15) | ~v10_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.30/1.30  tff(c_148, plain, (![A_66, C_67, B_68]: (r1_lattices(A_66, k16_lattice3(A_66, C_67), B_68) | ~m1_subset_1(k16_lattice3(A_66, C_67), u1_struct_0(A_66)) | ~v9_lattices(A_66) | ~v8_lattices(A_66) | ~v6_lattices(A_66) | ~r2_hidden(B_68, C_67) | ~m1_subset_1(B_68, u1_struct_0(A_66)) | ~l3_lattices(A_66) | ~v4_lattice3(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_28, c_70])).
% 2.30/1.30  tff(c_152, plain, (![A_69, B_70, B_71]: (r1_lattices(A_69, k16_lattice3(A_69, B_70), B_71) | ~v9_lattices(A_69) | ~v8_lattices(A_69) | ~v6_lattices(A_69) | ~r2_hidden(B_71, B_70) | ~m1_subset_1(B_71, u1_struct_0(A_69)) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | ~l3_lattices(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_26, c_148])).
% 2.30/1.30  tff(c_24, plain, (![C_12, B_10, A_6]: (C_12=B_10 | ~r1_lattices(A_6, C_12, B_10) | ~r1_lattices(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l2_lattices(A_6) | ~v4_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.30/1.30  tff(c_165, plain, (![A_81, B_82, B_83]: (k16_lattice3(A_81, B_82)=B_83 | ~r1_lattices(A_81, B_83, k16_lattice3(A_81, B_82)) | ~m1_subset_1(k16_lattice3(A_81, B_82), u1_struct_0(A_81)) | ~l2_lattices(A_81) | ~v4_lattices(A_81) | ~v9_lattices(A_81) | ~v8_lattices(A_81) | ~v6_lattices(A_81) | ~r2_hidden(B_83, B_82) | ~m1_subset_1(B_83, u1_struct_0(A_81)) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_152, c_24])).
% 2.30/1.30  tff(c_181, plain, (![A_87, B_88, B_89]: (k16_lattice3(A_87, B_88)=B_89 | ~m1_subset_1(k16_lattice3(A_87, B_88), u1_struct_0(A_87)) | ~l2_lattices(A_87) | ~v4_lattices(A_87) | ~r2_hidden(B_89, B_88) | ~v9_lattices(A_87) | ~v8_lattices(A_87) | ~v6_lattices(A_87) | ~r3_lattice3(A_87, B_89, B_88) | ~m1_subset_1(B_89, u1_struct_0(A_87)) | ~v4_lattice3(A_87) | ~v10_lattices(A_87) | ~l3_lattices(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_160, c_165])).
% 2.30/1.30  tff(c_185, plain, (![A_90, B_91, B_92]: (k16_lattice3(A_90, B_91)=B_92 | ~l2_lattices(A_90) | ~v4_lattices(A_90) | ~r2_hidden(B_92, B_91) | ~v9_lattices(A_90) | ~v8_lattices(A_90) | ~v6_lattices(A_90) | ~r3_lattice3(A_90, B_92, B_91) | ~m1_subset_1(B_92, u1_struct_0(A_90)) | ~v4_lattice3(A_90) | ~v10_lattices(A_90) | ~l3_lattices(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_26, c_181])).
% 2.30/1.30  tff(c_187, plain, (k16_lattice3('#skF_1', '#skF_3')='#skF_2' | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | ~r2_hidden('#skF_2', '#skF_3') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~v4_lattice3('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_185])).
% 2.30/1.30  tff(c_190, plain, (k16_lattice3('#skF_1', '#skF_3')='#skF_2' | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_44, c_40, c_100, c_122, c_111, c_38, c_53, c_187])).
% 2.30/1.30  tff(c_191, plain, (~v4_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_34, c_190])).
% 2.30/1.30  tff(c_194, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_191])).
% 2.30/1.30  tff(c_197, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_194])).
% 2.30/1.30  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_197])).
% 2.30/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  Inference rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Ref     : 0
% 2.30/1.30  #Sup     : 25
% 2.30/1.30  #Fact    : 0
% 2.30/1.30  #Define  : 0
% 2.30/1.30  #Split   : 4
% 2.30/1.30  #Chain   : 0
% 2.30/1.30  #Close   : 0
% 2.30/1.30  
% 2.30/1.30  Ordering : KBO
% 2.30/1.30  
% 2.30/1.30  Simplification rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Subsume      : 3
% 2.30/1.30  #Demod        : 24
% 2.30/1.30  #Tautology    : 3
% 2.30/1.30  #SimpNegUnit  : 8
% 2.30/1.30  #BackRed      : 0
% 2.30/1.30  
% 2.30/1.30  #Partial instantiations: 0
% 2.30/1.30  #Strategies tried      : 1
% 2.30/1.30  
% 2.30/1.30  Timing (in seconds)
% 2.30/1.30  ----------------------
% 2.65/1.30  Preprocessing        : 0.30
% 2.65/1.30  Parsing              : 0.17
% 2.65/1.30  CNF conversion       : 0.02
% 2.65/1.30  Main loop            : 0.24
% 2.65/1.30  Inferencing          : 0.11
% 2.65/1.30  Reduction            : 0.06
% 2.65/1.31  Demodulation         : 0.04
% 2.65/1.31  BG Simplification    : 0.02
% 2.65/1.31  Subsumption          : 0.05
% 2.65/1.31  Abstraction          : 0.01
% 2.65/1.31  MUC search           : 0.00
% 2.65/1.31  Cooper               : 0.00
% 2.65/1.31  Total                : 0.58
% 2.65/1.31  Index Insertion      : 0.00
% 2.65/1.31  Index Deletion       : 0.00
% 2.65/1.31  Index Matching       : 0.00
% 2.65/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
