%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 193 expanded)
%              Number of leaves         :   35 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  270 ( 870 expanded)
%              Number of equality atoms :   10 (  48 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

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

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
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

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_145,axiom,(
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

tff(f_119,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    k15_lattice3('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_64,B_65,C_66] :
      ( r3_lattices(A_64,B_65,C_66)
      | ~ r1_lattices(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l3_lattices(A_64)
      | ~ v9_lattices(A_64)
      | ~ v8_lattices(A_64)
      | ~ v6_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    ! [B_65] :
      ( r3_lattices('#skF_2',B_65,'#skF_3')
      | ~ r1_lattices('#skF_2',B_65,'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_97,plain,(
    ! [B_65] :
      ( r3_lattices('#skF_2',B_65,'#skF_3')
      | ~ r1_lattices('#skF_2',B_65,'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93])).

tff(c_98,plain,(
    ! [B_65] :
      ( r3_lattices('#skF_2',B_65,'#skF_3')
      | ~ r1_lattices('#skF_2',B_65,'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97])).

tff(c_99,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_102,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_105,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_105])).

tff(c_109,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_98])).

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

tff(c_108,plain,(
    ! [B_65] :
      ( ~ v8_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | r3_lattices('#skF_2',B_65,'#skF_3')
      | ~ r1_lattices('#skF_2',B_65,'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_110,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_113,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_110])).

tff(c_116,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_116])).

tff(c_119,plain,(
    ! [B_65] :
      ( ~ v8_lattices('#skF_2')
      | r3_lattices('#skF_2',B_65,'#skF_3')
      | ~ r1_lattices('#skF_2',B_65,'#skF_3')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_121,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_124,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_127,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_124])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_127])).

tff(c_131,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_120,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_57,plain,(
    ! [A_38] :
      ( l2_lattices(A_38)
      | ~ l3_lattices(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_44,plain,(
    r4_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k15_lattice3(A_25,B_26),u1_struct_0(A_25))
      | ~ l3_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    ! [A_27,B_31,C_33] :
      ( r3_lattices(A_27,B_31,k15_lattice3(A_27,C_33))
      | ~ r2_hidden(B_31,C_33)
      | ~ m1_subset_1(B_31,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | ~ v4_lattice3(A_27)
      | ~ v10_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_82,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_lattices(A_61,B_62,C_63)
      | ~ r3_lattices(A_61,B_62,C_63)
      | ~ m1_subset_1(C_63,u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l3_lattices(A_61)
      | ~ v9_lattices(A_61)
      | ~ v8_lattices(A_61)
      | ~ v6_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_lattices(A_89,B_90,k15_lattice3(A_89,C_91))
      | ~ m1_subset_1(k15_lattice3(A_89,C_91),u1_struct_0(A_89))
      | ~ v9_lattices(A_89)
      | ~ v8_lattices(A_89)
      | ~ v6_lattices(A_89)
      | ~ r2_hidden(B_90,C_91)
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l3_lattices(A_89)
      | ~ v4_lattice3(A_89)
      | ~ v10_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_194,plain,(
    ! [A_25,B_90,B_26] :
      ( r1_lattices(A_25,B_90,k15_lattice3(A_25,B_26))
      | ~ v9_lattices(A_25)
      | ~ v8_lattices(A_25)
      | ~ v6_lattices(A_25)
      | ~ r2_hidden(B_90,B_26)
      | ~ m1_subset_1(B_90,u1_struct_0(A_25))
      | ~ v4_lattice3(A_25)
      | ~ v10_lattices(A_25)
      | ~ l3_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_36,c_191])).

tff(c_178,plain,(
    ! [A_83,B_84,D_85] :
      ( r1_lattices(A_83,k15_lattice3(A_83,B_84),D_85)
      | ~ r4_lattice3(A_83,D_85,B_84)
      | ~ m1_subset_1(D_85,u1_struct_0(A_83))
      | ~ m1_subset_1(k15_lattice3(A_83,B_84),u1_struct_0(A_83))
      | ~ v4_lattice3(A_83)
      | ~ v10_lattices(A_83)
      | ~ l3_lattices(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_182,plain,(
    ! [A_86,B_87,D_88] :
      ( r1_lattices(A_86,k15_lattice3(A_86,B_87),D_88)
      | ~ r4_lattice3(A_86,D_88,B_87)
      | ~ m1_subset_1(D_88,u1_struct_0(A_86))
      | ~ v4_lattice3(A_86)
      | ~ v10_lattices(A_86)
      | ~ l3_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_36,c_178])).

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

tff(c_200,plain,(
    ! [A_98,B_99,D_100] :
      ( k15_lattice3(A_98,B_99) = D_100
      | ~ r1_lattices(A_98,D_100,k15_lattice3(A_98,B_99))
      | ~ m1_subset_1(k15_lattice3(A_98,B_99),u1_struct_0(A_98))
      | ~ l2_lattices(A_98)
      | ~ v4_lattices(A_98)
      | ~ r4_lattice3(A_98,D_100,B_99)
      | ~ m1_subset_1(D_100,u1_struct_0(A_98))
      | ~ v4_lattice3(A_98)
      | ~ v10_lattices(A_98)
      | ~ l3_lattices(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_182,c_24])).

tff(c_208,plain,(
    ! [A_101,B_102,B_103] :
      ( k15_lattice3(A_101,B_102) = B_103
      | ~ m1_subset_1(k15_lattice3(A_101,B_102),u1_struct_0(A_101))
      | ~ l2_lattices(A_101)
      | ~ v4_lattices(A_101)
      | ~ r4_lattice3(A_101,B_103,B_102)
      | ~ v9_lattices(A_101)
      | ~ v8_lattices(A_101)
      | ~ v6_lattices(A_101)
      | ~ r2_hidden(B_103,B_102)
      | ~ m1_subset_1(B_103,u1_struct_0(A_101))
      | ~ v4_lattice3(A_101)
      | ~ v10_lattices(A_101)
      | ~ l3_lattices(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_194,c_200])).

tff(c_212,plain,(
    ! [A_104,B_105,B_106] :
      ( k15_lattice3(A_104,B_105) = B_106
      | ~ l2_lattices(A_104)
      | ~ v4_lattices(A_104)
      | ~ r4_lattice3(A_104,B_106,B_105)
      | ~ v9_lattices(A_104)
      | ~ v8_lattices(A_104)
      | ~ v6_lattices(A_104)
      | ~ r2_hidden(B_106,B_105)
      | ~ m1_subset_1(B_106,u1_struct_0(A_104))
      | ~ v4_lattice3(A_104)
      | ~ v10_lattices(A_104)
      | ~ l3_lattices(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_36,c_208])).

tff(c_218,plain,
    ( k15_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ l2_lattices('#skF_2')
    | ~ v4_lattices('#skF_2')
    | ~ v9_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_212])).

tff(c_224,plain,
    ( k15_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ v4_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_52,c_48,c_46,c_109,c_131,c_120,c_61,c_218])).

tff(c_225,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_42,c_224])).

tff(c_228,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_231,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.46/1.34  
% 2.46/1.34  %Foreground sorts:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Background operators:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Foreground operators:
% 2.46/1.34  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.46/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.34  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.46/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.46/1.34  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.34  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.46/1.34  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 2.46/1.34  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.46/1.34  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.46/1.34  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.46/1.34  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.46/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.34  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.46/1.34  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 2.46/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.34  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.46/1.34  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.46/1.34  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.34  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.34  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.46/1.34  
% 2.46/1.36  tff(f_165, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 2.46/1.36  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.46/1.36  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.46/1.36  tff(f_53, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.46/1.36  tff(f_126, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 2.46/1.36  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 2.46/1.36  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 2.46/1.36  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 2.46/1.36  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_50, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_54, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.36  tff(c_42, plain, (k15_lattice3('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_52, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.36  tff(c_89, plain, (![A_64, B_65, C_66]: (r3_lattices(A_64, B_65, C_66) | ~r1_lattices(A_64, B_65, C_66) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l3_lattices(A_64) | ~v9_lattices(A_64) | ~v8_lattices(A_64) | ~v6_lattices(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.36  tff(c_93, plain, (![B_65]: (r3_lattices('#skF_2', B_65, '#skF_3') | ~r1_lattices('#skF_2', B_65, '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_89])).
% 2.46/1.36  tff(c_97, plain, (![B_65]: (r3_lattices('#skF_2', B_65, '#skF_3') | ~r1_lattices('#skF_2', B_65, '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93])).
% 2.46/1.36  tff(c_98, plain, (![B_65]: (r3_lattices('#skF_2', B_65, '#skF_3') | ~r1_lattices('#skF_2', B_65, '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97])).
% 2.46/1.36  tff(c_99, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 2.46/1.36  tff(c_102, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.46/1.36  tff(c_105, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_102])).
% 2.46/1.36  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_105])).
% 2.46/1.36  tff(c_109, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_98])).
% 2.46/1.36  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.36  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.36  tff(c_108, plain, (![B_65]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_65, '#skF_3') | ~r1_lattices('#skF_2', B_65, '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_98])).
% 2.46/1.36  tff(c_110, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_108])).
% 2.46/1.36  tff(c_113, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_110])).
% 2.46/1.36  tff(c_116, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_113])).
% 2.46/1.36  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_116])).
% 2.46/1.36  tff(c_119, plain, (![B_65]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_65, '#skF_3') | ~r1_lattices('#skF_2', B_65, '#skF_3') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_108])).
% 2.46/1.36  tff(c_121, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_119])).
% 2.46/1.36  tff(c_124, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.46/1.36  tff(c_127, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_124])).
% 2.46/1.36  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_127])).
% 2.46/1.36  tff(c_131, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_119])).
% 2.46/1.36  tff(c_120, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_108])).
% 2.46/1.36  tff(c_57, plain, (![A_38]: (l2_lattices(A_38) | ~l3_lattices(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.36  tff(c_61, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_50, c_57])).
% 2.46/1.36  tff(c_44, plain, (r4_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.46/1.36  tff(c_36, plain, (![A_25, B_26]: (m1_subset_1(k15_lattice3(A_25, B_26), u1_struct_0(A_25)) | ~l3_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.46/1.36  tff(c_40, plain, (![A_27, B_31, C_33]: (r3_lattices(A_27, B_31, k15_lattice3(A_27, C_33)) | ~r2_hidden(B_31, C_33) | ~m1_subset_1(B_31, u1_struct_0(A_27)) | ~l3_lattices(A_27) | ~v4_lattice3(A_27) | ~v10_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.46/1.36  tff(c_82, plain, (![A_61, B_62, C_63]: (r1_lattices(A_61, B_62, C_63) | ~r3_lattices(A_61, B_62, C_63) | ~m1_subset_1(C_63, u1_struct_0(A_61)) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l3_lattices(A_61) | ~v9_lattices(A_61) | ~v8_lattices(A_61) | ~v6_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.36  tff(c_191, plain, (![A_89, B_90, C_91]: (r1_lattices(A_89, B_90, k15_lattice3(A_89, C_91)) | ~m1_subset_1(k15_lattice3(A_89, C_91), u1_struct_0(A_89)) | ~v9_lattices(A_89) | ~v8_lattices(A_89) | ~v6_lattices(A_89) | ~r2_hidden(B_90, C_91) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l3_lattices(A_89) | ~v4_lattice3(A_89) | ~v10_lattices(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_40, c_82])).
% 2.46/1.36  tff(c_194, plain, (![A_25, B_90, B_26]: (r1_lattices(A_25, B_90, k15_lattice3(A_25, B_26)) | ~v9_lattices(A_25) | ~v8_lattices(A_25) | ~v6_lattices(A_25) | ~r2_hidden(B_90, B_26) | ~m1_subset_1(B_90, u1_struct_0(A_25)) | ~v4_lattice3(A_25) | ~v10_lattices(A_25) | ~l3_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_36, c_191])).
% 2.46/1.36  tff(c_178, plain, (![A_83, B_84, D_85]: (r1_lattices(A_83, k15_lattice3(A_83, B_84), D_85) | ~r4_lattice3(A_83, D_85, B_84) | ~m1_subset_1(D_85, u1_struct_0(A_83)) | ~m1_subset_1(k15_lattice3(A_83, B_84), u1_struct_0(A_83)) | ~v4_lattice3(A_83) | ~v10_lattices(A_83) | ~l3_lattices(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.36  tff(c_182, plain, (![A_86, B_87, D_88]: (r1_lattices(A_86, k15_lattice3(A_86, B_87), D_88) | ~r4_lattice3(A_86, D_88, B_87) | ~m1_subset_1(D_88, u1_struct_0(A_86)) | ~v4_lattice3(A_86) | ~v10_lattices(A_86) | ~l3_lattices(A_86) | v2_struct_0(A_86))), inference(resolution, [status(thm)], [c_36, c_178])).
% 2.46/1.36  tff(c_24, plain, (![C_12, B_10, A_6]: (C_12=B_10 | ~r1_lattices(A_6, C_12, B_10) | ~r1_lattices(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l2_lattices(A_6) | ~v4_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.46/1.36  tff(c_200, plain, (![A_98, B_99, D_100]: (k15_lattice3(A_98, B_99)=D_100 | ~r1_lattices(A_98, D_100, k15_lattice3(A_98, B_99)) | ~m1_subset_1(k15_lattice3(A_98, B_99), u1_struct_0(A_98)) | ~l2_lattices(A_98) | ~v4_lattices(A_98) | ~r4_lattice3(A_98, D_100, B_99) | ~m1_subset_1(D_100, u1_struct_0(A_98)) | ~v4_lattice3(A_98) | ~v10_lattices(A_98) | ~l3_lattices(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_182, c_24])).
% 2.46/1.36  tff(c_208, plain, (![A_101, B_102, B_103]: (k15_lattice3(A_101, B_102)=B_103 | ~m1_subset_1(k15_lattice3(A_101, B_102), u1_struct_0(A_101)) | ~l2_lattices(A_101) | ~v4_lattices(A_101) | ~r4_lattice3(A_101, B_103, B_102) | ~v9_lattices(A_101) | ~v8_lattices(A_101) | ~v6_lattices(A_101) | ~r2_hidden(B_103, B_102) | ~m1_subset_1(B_103, u1_struct_0(A_101)) | ~v4_lattice3(A_101) | ~v10_lattices(A_101) | ~l3_lattices(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_194, c_200])).
% 2.46/1.36  tff(c_212, plain, (![A_104, B_105, B_106]: (k15_lattice3(A_104, B_105)=B_106 | ~l2_lattices(A_104) | ~v4_lattices(A_104) | ~r4_lattice3(A_104, B_106, B_105) | ~v9_lattices(A_104) | ~v8_lattices(A_104) | ~v6_lattices(A_104) | ~r2_hidden(B_106, B_105) | ~m1_subset_1(B_106, u1_struct_0(A_104)) | ~v4_lattice3(A_104) | ~v10_lattices(A_104) | ~l3_lattices(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_36, c_208])).
% 2.46/1.36  tff(c_218, plain, (k15_lattice3('#skF_2', '#skF_4')='#skF_3' | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_212])).
% 2.46/1.36  tff(c_224, plain, (k15_lattice3('#skF_2', '#skF_4')='#skF_3' | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_52, c_48, c_46, c_109, c_131, c_120, c_61, c_218])).
% 2.46/1.36  tff(c_225, plain, (~v4_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_42, c_224])).
% 2.46/1.36  tff(c_228, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_225])).
% 2.46/1.36  tff(c_231, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_228])).
% 2.46/1.36  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_231])).
% 2.46/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  Inference rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Ref     : 0
% 2.46/1.36  #Sup     : 29
% 2.46/1.36  #Fact    : 0
% 2.46/1.36  #Define  : 0
% 2.46/1.36  #Split   : 4
% 2.46/1.36  #Chain   : 0
% 2.46/1.36  #Close   : 0
% 2.46/1.36  
% 2.46/1.36  Ordering : KBO
% 2.46/1.36  
% 2.46/1.36  Simplification rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Subsume      : 4
% 2.46/1.36  #Demod        : 32
% 2.46/1.36  #Tautology    : 5
% 2.46/1.36  #SimpNegUnit  : 10
% 2.46/1.36  #BackRed      : 0
% 2.46/1.36  
% 2.46/1.36  #Partial instantiations: 0
% 2.46/1.36  #Strategies tried      : 1
% 2.46/1.36  
% 2.46/1.36  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.36  Preprocessing        : 0.32
% 2.46/1.36  Parsing              : 0.17
% 2.46/1.36  CNF conversion       : 0.02
% 2.46/1.36  Main loop            : 0.26
% 2.46/1.36  Inferencing          : 0.11
% 2.46/1.36  Reduction            : 0.06
% 2.46/1.36  Demodulation         : 0.04
% 2.46/1.36  BG Simplification    : 0.02
% 2.46/1.36  Subsumption          : 0.05
% 2.46/1.36  Abstraction          : 0.01
% 2.46/1.36  MUC search           : 0.00
% 2.46/1.36  Cooper               : 0.00
% 2.46/1.36  Total                : 0.61
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
