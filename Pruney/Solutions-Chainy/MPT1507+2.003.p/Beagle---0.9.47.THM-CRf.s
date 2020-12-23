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
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 203 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  332 ( 949 expanded)
%              Number of equality atoms :   13 (  51 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

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

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_53,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_147,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_54,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    k15_lattice3('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [A_74,B_75,C_76] :
      ( r3_lattices(A_74,B_75,C_76)
      | ~ r1_lattices(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | ~ v9_lattices(A_74)
      | ~ v8_lattices(A_74)
      | ~ v6_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_130])).

tff(c_141,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_136])).

tff(c_142,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_141])).

tff(c_143,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_146,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_149,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_149])).

tff(c_153,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_142])).

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

tff(c_152,plain,(
    ! [B_75] :
      ( ~ v8_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_154,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_154])).

tff(c_160,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_160])).

tff(c_163,plain,(
    ! [B_75] :
      ( ~ v8_lattices('#skF_2')
      | r3_lattices('#skF_2',B_75,'#skF_3')
      | ~ r1_lattices('#skF_2',B_75,'#skF_3')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_165,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_168,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_171,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_168])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_171])).

tff(c_175,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_164,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_57,plain,(
    ! [A_35] :
      ( l2_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_44,plain,(
    r4_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_28,plain,(
    ! [D_20,B_16,C_17] :
      ( r2_hidden(D_20,a_2_2_lattice3(B_16,C_17))
      | ~ r4_lattice3(B_16,D_20,C_17)
      | ~ m1_subset_1(D_20,u1_struct_0(B_16))
      | ~ l3_lattices(B_16)
      | ~ v4_lattice3(B_16)
      | ~ v10_lattices(B_16)
      | v2_struct_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k15_lattice3(A_13,B_14),u1_struct_0(A_13))
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [A_21,B_23] :
      ( k16_lattice3(A_21,a_2_2_lattice3(A_21,B_23)) = k15_lattice3(A_21,B_23)
      | ~ l3_lattices(A_21)
      | ~ v4_lattice3(A_21)
      | ~ v10_lattices(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_86,plain,(
    ! [A_56,C_57,B_58] :
      ( r3_lattices(A_56,k16_lattice3(A_56,C_57),B_58)
      | ~ r2_hidden(B_58,C_57)
      | ~ m1_subset_1(B_58,u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | ~ v4_lattice3(A_56)
      | ~ v10_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_220,plain,(
    ! [A_84,B_85,B_86] :
      ( r3_lattices(A_84,k15_lattice3(A_84,B_85),B_86)
      | ~ r2_hidden(B_86,a_2_2_lattice3(A_84,B_85))
      | ~ m1_subset_1(B_86,u1_struct_0(A_84))
      | ~ l3_lattices(A_84)
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | v2_struct_0(A_84)
      | ~ l3_lattices(A_84)
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_86])).

tff(c_22,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_lattices(A_3,B_4,C_5)
      | ~ r3_lattices(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,u1_struct_0(A_3))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l3_lattices(A_3)
      | ~ v9_lattices(A_3)
      | ~ v8_lattices(A_3)
      | ~ v6_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_380,plain,(
    ! [A_117,B_118,B_119] :
      ( r1_lattices(A_117,k15_lattice3(A_117,B_118),B_119)
      | ~ m1_subset_1(k15_lattice3(A_117,B_118),u1_struct_0(A_117))
      | ~ v9_lattices(A_117)
      | ~ v8_lattices(A_117)
      | ~ v6_lattices(A_117)
      | ~ r2_hidden(B_119,a_2_2_lattice3(A_117,B_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_117))
      | ~ l3_lattices(A_117)
      | ~ v4_lattice3(A_117)
      | ~ v10_lattices(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_220,c_22])).

tff(c_383,plain,(
    ! [A_13,B_14,B_119] :
      ( r1_lattices(A_13,k15_lattice3(A_13,B_14),B_119)
      | ~ v9_lattices(A_13)
      | ~ v8_lattices(A_13)
      | ~ v6_lattices(A_13)
      | ~ r2_hidden(B_119,a_2_2_lattice3(A_13,B_14))
      | ~ m1_subset_1(B_119,u1_struct_0(A_13))
      | ~ v4_lattice3(A_13)
      | ~ v10_lattices(A_13)
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_380])).

tff(c_40,plain,(
    ! [A_24,B_28,C_30] :
      ( r3_lattices(A_24,B_28,k15_lattice3(A_24,C_30))
      | ~ r2_hidden(B_28,C_30)
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | ~ v4_lattice3(A_24)
      | ~ v10_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_123,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_lattices(A_71,B_72,C_73)
      | ~ r3_lattices(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v9_lattices(A_71)
      | ~ v8_lattices(A_71)
      | ~ v6_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_338,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_lattices(A_103,B_104,k15_lattice3(A_103,C_105))
      | ~ m1_subset_1(k15_lattice3(A_103,C_105),u1_struct_0(A_103))
      | ~ v9_lattices(A_103)
      | ~ v8_lattices(A_103)
      | ~ v6_lattices(A_103)
      | ~ r2_hidden(B_104,C_105)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l3_lattices(A_103)
      | ~ v4_lattice3(A_103)
      | ~ v10_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_40,c_123])).

tff(c_342,plain,(
    ! [A_106,B_107,B_108] :
      ( r1_lattices(A_106,B_107,k15_lattice3(A_106,B_108))
      | ~ v9_lattices(A_106)
      | ~ v8_lattices(A_106)
      | ~ v6_lattices(A_106)
      | ~ r2_hidden(B_107,B_108)
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ v4_lattice3(A_106)
      | ~ v10_lattices(A_106)
      | ~ l3_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_26,c_338])).

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

tff(c_552,plain,(
    ! [A_144,B_145,B_146] :
      ( k15_lattice3(A_144,B_145) = B_146
      | ~ r1_lattices(A_144,k15_lattice3(A_144,B_145),B_146)
      | ~ m1_subset_1(k15_lattice3(A_144,B_145),u1_struct_0(A_144))
      | ~ l2_lattices(A_144)
      | ~ v4_lattices(A_144)
      | ~ v9_lattices(A_144)
      | ~ v8_lattices(A_144)
      | ~ v6_lattices(A_144)
      | ~ r2_hidden(B_146,B_145)
      | ~ m1_subset_1(B_146,u1_struct_0(A_144))
      | ~ v4_lattice3(A_144)
      | ~ v10_lattices(A_144)
      | ~ l3_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_342,c_24])).

tff(c_560,plain,(
    ! [A_147,B_148,B_149] :
      ( k15_lattice3(A_147,B_148) = B_149
      | ~ m1_subset_1(k15_lattice3(A_147,B_148),u1_struct_0(A_147))
      | ~ l2_lattices(A_147)
      | ~ v4_lattices(A_147)
      | ~ r2_hidden(B_149,B_148)
      | ~ v9_lattices(A_147)
      | ~ v8_lattices(A_147)
      | ~ v6_lattices(A_147)
      | ~ r2_hidden(B_149,a_2_2_lattice3(A_147,B_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_147))
      | ~ v4_lattice3(A_147)
      | ~ v10_lattices(A_147)
      | ~ l3_lattices(A_147)
      | v2_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_383,c_552])).

tff(c_564,plain,(
    ! [A_150,B_151,B_152] :
      ( k15_lattice3(A_150,B_151) = B_152
      | ~ l2_lattices(A_150)
      | ~ v4_lattices(A_150)
      | ~ r2_hidden(B_152,B_151)
      | ~ v9_lattices(A_150)
      | ~ v8_lattices(A_150)
      | ~ v6_lattices(A_150)
      | ~ r2_hidden(B_152,a_2_2_lattice3(A_150,B_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_150))
      | ~ v4_lattice3(A_150)
      | ~ v10_lattices(A_150)
      | ~ l3_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_26,c_560])).

tff(c_569,plain,(
    ! [B_153,C_154,D_155] :
      ( k15_lattice3(B_153,C_154) = D_155
      | ~ l2_lattices(B_153)
      | ~ v4_lattices(B_153)
      | ~ r2_hidden(D_155,C_154)
      | ~ v9_lattices(B_153)
      | ~ v8_lattices(B_153)
      | ~ v6_lattices(B_153)
      | ~ r4_lattice3(B_153,D_155,C_154)
      | ~ m1_subset_1(D_155,u1_struct_0(B_153))
      | ~ l3_lattices(B_153)
      | ~ v4_lattice3(B_153)
      | ~ v10_lattices(B_153)
      | v2_struct_0(B_153) ) ),
    inference(resolution,[status(thm)],[c_28,c_564])).

tff(c_573,plain,
    ( k15_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ l2_lattices('#skF_2')
    | ~ v4_lattices('#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v9_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_569])).

tff(c_577,plain,
    ( k15_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ v4_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_153,c_175,c_164,c_46,c_61,c_573])).

tff(c_578,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_42,c_577])).

tff(c_592,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_578])).

tff(c_595,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_592])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:43:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.46  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.03/1.46  
% 3.03/1.46  %Foreground sorts:
% 3.03/1.46  
% 3.03/1.46  
% 3.03/1.46  %Background operators:
% 3.03/1.46  
% 3.03/1.46  
% 3.03/1.46  %Foreground operators:
% 3.03/1.46  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.03/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.03/1.46  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.03/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.03/1.46  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.46  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.03/1.46  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.03/1.46  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.03/1.46  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.03/1.46  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.03/1.46  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.03/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.46  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.03/1.46  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.03/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.46  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.03/1.46  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.03/1.46  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.03/1.46  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.46  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.46  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.03/1.46  
% 3.35/1.48  tff(f_167, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattice3)).
% 3.35/1.48  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.35/1.48  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.35/1.48  tff(f_53, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.35/1.48  tff(f_116, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 3.35/1.48  tff(f_98, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 3.35/1.48  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 3.35/1.48  tff(f_147, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.35/1.48  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 3.35/1.48  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_50, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_54, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.48  tff(c_42, plain, (k15_lattice3('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_52, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.48  tff(c_130, plain, (![A_74, B_75, C_76]: (r3_lattices(A_74, B_75, C_76) | ~r1_lattices(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v9_lattices(A_74) | ~v8_lattices(A_74) | ~v6_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.35/1.48  tff(c_136, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_130])).
% 3.35/1.48  tff(c_141, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_136])).
% 3.35/1.48  tff(c_142, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_141])).
% 3.35/1.48  tff(c_143, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_142])).
% 3.35/1.48  tff(c_146, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_143])).
% 3.35/1.48  tff(c_149, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_146])).
% 3.35/1.48  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_149])).
% 3.35/1.48  tff(c_153, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_142])).
% 3.35/1.48  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.48  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.48  tff(c_152, plain, (![B_75]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_142])).
% 3.35/1.48  tff(c_154, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_152])).
% 3.35/1.48  tff(c_157, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_154])).
% 3.35/1.48  tff(c_160, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_157])).
% 3.35/1.48  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_160])).
% 3.35/1.48  tff(c_163, plain, (![B_75]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_152])).
% 3.35/1.48  tff(c_165, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_163])).
% 3.35/1.48  tff(c_168, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_165])).
% 3.35/1.48  tff(c_171, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_168])).
% 3.35/1.48  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_171])).
% 3.35/1.48  tff(c_175, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_163])).
% 3.35/1.48  tff(c_164, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 3.35/1.48  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_57, plain, (![A_35]: (l2_lattices(A_35) | ~l3_lattices(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.48  tff(c_61, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_50, c_57])).
% 3.35/1.48  tff(c_44, plain, (r4_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.35/1.48  tff(c_28, plain, (![D_20, B_16, C_17]: (r2_hidden(D_20, a_2_2_lattice3(B_16, C_17)) | ~r4_lattice3(B_16, D_20, C_17) | ~m1_subset_1(D_20, u1_struct_0(B_16)) | ~l3_lattices(B_16) | ~v4_lattice3(B_16) | ~v10_lattices(B_16) | v2_struct_0(B_16))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.35/1.48  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(k15_lattice3(A_13, B_14), u1_struct_0(A_13)) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.35/1.48  tff(c_36, plain, (![A_21, B_23]: (k16_lattice3(A_21, a_2_2_lattice3(A_21, B_23))=k15_lattice3(A_21, B_23) | ~l3_lattices(A_21) | ~v4_lattice3(A_21) | ~v10_lattices(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.35/1.48  tff(c_86, plain, (![A_56, C_57, B_58]: (r3_lattices(A_56, k16_lattice3(A_56, C_57), B_58) | ~r2_hidden(B_58, C_57) | ~m1_subset_1(B_58, u1_struct_0(A_56)) | ~l3_lattices(A_56) | ~v4_lattice3(A_56) | ~v10_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.35/1.48  tff(c_220, plain, (![A_84, B_85, B_86]: (r3_lattices(A_84, k15_lattice3(A_84, B_85), B_86) | ~r2_hidden(B_86, a_2_2_lattice3(A_84, B_85)) | ~m1_subset_1(B_86, u1_struct_0(A_84)) | ~l3_lattices(A_84) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | v2_struct_0(A_84) | ~l3_lattices(A_84) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_36, c_86])).
% 3.35/1.48  tff(c_22, plain, (![A_3, B_4, C_5]: (r1_lattices(A_3, B_4, C_5) | ~r3_lattices(A_3, B_4, C_5) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l3_lattices(A_3) | ~v9_lattices(A_3) | ~v8_lattices(A_3) | ~v6_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.35/1.48  tff(c_380, plain, (![A_117, B_118, B_119]: (r1_lattices(A_117, k15_lattice3(A_117, B_118), B_119) | ~m1_subset_1(k15_lattice3(A_117, B_118), u1_struct_0(A_117)) | ~v9_lattices(A_117) | ~v8_lattices(A_117) | ~v6_lattices(A_117) | ~r2_hidden(B_119, a_2_2_lattice3(A_117, B_118)) | ~m1_subset_1(B_119, u1_struct_0(A_117)) | ~l3_lattices(A_117) | ~v4_lattice3(A_117) | ~v10_lattices(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_220, c_22])).
% 3.35/1.48  tff(c_383, plain, (![A_13, B_14, B_119]: (r1_lattices(A_13, k15_lattice3(A_13, B_14), B_119) | ~v9_lattices(A_13) | ~v8_lattices(A_13) | ~v6_lattices(A_13) | ~r2_hidden(B_119, a_2_2_lattice3(A_13, B_14)) | ~m1_subset_1(B_119, u1_struct_0(A_13)) | ~v4_lattice3(A_13) | ~v10_lattices(A_13) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_26, c_380])).
% 3.35/1.48  tff(c_40, plain, (![A_24, B_28, C_30]: (r3_lattices(A_24, B_28, k15_lattice3(A_24, C_30)) | ~r2_hidden(B_28, C_30) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l3_lattices(A_24) | ~v4_lattice3(A_24) | ~v10_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.35/1.48  tff(c_123, plain, (![A_71, B_72, C_73]: (r1_lattices(A_71, B_72, C_73) | ~r3_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v9_lattices(A_71) | ~v8_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.35/1.48  tff(c_338, plain, (![A_103, B_104, C_105]: (r1_lattices(A_103, B_104, k15_lattice3(A_103, C_105)) | ~m1_subset_1(k15_lattice3(A_103, C_105), u1_struct_0(A_103)) | ~v9_lattices(A_103) | ~v8_lattices(A_103) | ~v6_lattices(A_103) | ~r2_hidden(B_104, C_105) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l3_lattices(A_103) | ~v4_lattice3(A_103) | ~v10_lattices(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_40, c_123])).
% 3.35/1.48  tff(c_342, plain, (![A_106, B_107, B_108]: (r1_lattices(A_106, B_107, k15_lattice3(A_106, B_108)) | ~v9_lattices(A_106) | ~v8_lattices(A_106) | ~v6_lattices(A_106) | ~r2_hidden(B_107, B_108) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~v4_lattice3(A_106) | ~v10_lattices(A_106) | ~l3_lattices(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_26, c_338])).
% 3.35/1.48  tff(c_24, plain, (![C_12, B_10, A_6]: (C_12=B_10 | ~r1_lattices(A_6, C_12, B_10) | ~r1_lattices(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l2_lattices(A_6) | ~v4_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.48  tff(c_552, plain, (![A_144, B_145, B_146]: (k15_lattice3(A_144, B_145)=B_146 | ~r1_lattices(A_144, k15_lattice3(A_144, B_145), B_146) | ~m1_subset_1(k15_lattice3(A_144, B_145), u1_struct_0(A_144)) | ~l2_lattices(A_144) | ~v4_lattices(A_144) | ~v9_lattices(A_144) | ~v8_lattices(A_144) | ~v6_lattices(A_144) | ~r2_hidden(B_146, B_145) | ~m1_subset_1(B_146, u1_struct_0(A_144)) | ~v4_lattice3(A_144) | ~v10_lattices(A_144) | ~l3_lattices(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_342, c_24])).
% 3.35/1.48  tff(c_560, plain, (![A_147, B_148, B_149]: (k15_lattice3(A_147, B_148)=B_149 | ~m1_subset_1(k15_lattice3(A_147, B_148), u1_struct_0(A_147)) | ~l2_lattices(A_147) | ~v4_lattices(A_147) | ~r2_hidden(B_149, B_148) | ~v9_lattices(A_147) | ~v8_lattices(A_147) | ~v6_lattices(A_147) | ~r2_hidden(B_149, a_2_2_lattice3(A_147, B_148)) | ~m1_subset_1(B_149, u1_struct_0(A_147)) | ~v4_lattice3(A_147) | ~v10_lattices(A_147) | ~l3_lattices(A_147) | v2_struct_0(A_147))), inference(resolution, [status(thm)], [c_383, c_552])).
% 3.35/1.48  tff(c_564, plain, (![A_150, B_151, B_152]: (k15_lattice3(A_150, B_151)=B_152 | ~l2_lattices(A_150) | ~v4_lattices(A_150) | ~r2_hidden(B_152, B_151) | ~v9_lattices(A_150) | ~v8_lattices(A_150) | ~v6_lattices(A_150) | ~r2_hidden(B_152, a_2_2_lattice3(A_150, B_151)) | ~m1_subset_1(B_152, u1_struct_0(A_150)) | ~v4_lattice3(A_150) | ~v10_lattices(A_150) | ~l3_lattices(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_26, c_560])).
% 3.35/1.48  tff(c_569, plain, (![B_153, C_154, D_155]: (k15_lattice3(B_153, C_154)=D_155 | ~l2_lattices(B_153) | ~v4_lattices(B_153) | ~r2_hidden(D_155, C_154) | ~v9_lattices(B_153) | ~v8_lattices(B_153) | ~v6_lattices(B_153) | ~r4_lattice3(B_153, D_155, C_154) | ~m1_subset_1(D_155, u1_struct_0(B_153)) | ~l3_lattices(B_153) | ~v4_lattice3(B_153) | ~v10_lattices(B_153) | v2_struct_0(B_153))), inference(resolution, [status(thm)], [c_28, c_564])).
% 3.35/1.48  tff(c_573, plain, (k15_lattice3('#skF_2', '#skF_4')='#skF_3' | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | ~r2_hidden('#skF_3', '#skF_4') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_569])).
% 3.35/1.48  tff(c_577, plain, (k15_lattice3('#skF_2', '#skF_4')='#skF_3' | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_153, c_175, c_164, c_46, c_61, c_573])).
% 3.35/1.48  tff(c_578, plain, (~v4_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_42, c_577])).
% 3.35/1.48  tff(c_592, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_578])).
% 3.35/1.48  tff(c_595, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_592])).
% 3.35/1.48  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_595])).
% 3.35/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.48  
% 3.35/1.48  Inference rules
% 3.35/1.48  ----------------------
% 3.35/1.48  #Ref     : 0
% 3.35/1.48  #Sup     : 103
% 3.35/1.48  #Fact    : 0
% 3.35/1.48  #Define  : 0
% 3.35/1.48  #Split   : 4
% 3.35/1.48  #Chain   : 0
% 3.35/1.48  #Close   : 0
% 3.35/1.48  
% 3.35/1.48  Ordering : KBO
% 3.35/1.48  
% 3.35/1.48  Simplification rules
% 3.35/1.48  ----------------------
% 3.35/1.48  #Subsume      : 18
% 3.35/1.48  #Demod        : 166
% 3.35/1.48  #Tautology    : 28
% 3.35/1.48  #SimpNegUnit  : 35
% 3.35/1.48  #BackRed      : 0
% 3.35/1.48  
% 3.35/1.48  #Partial instantiations: 0
% 3.35/1.48  #Strategies tried      : 1
% 3.35/1.48  
% 3.35/1.48  Timing (in seconds)
% 3.35/1.48  ----------------------
% 3.35/1.48  Preprocessing        : 0.31
% 3.35/1.48  Parsing              : 0.17
% 3.35/1.48  CNF conversion       : 0.02
% 3.35/1.48  Main loop            : 0.40
% 3.35/1.48  Inferencing          : 0.17
% 3.35/1.48  Reduction            : 0.11
% 3.35/1.48  Demodulation         : 0.08
% 3.35/1.48  BG Simplification    : 0.02
% 3.35/1.48  Subsumption          : 0.08
% 3.35/1.48  Abstraction          : 0.02
% 3.35/1.48  MUC search           : 0.00
% 3.35/1.48  Cooper               : 0.00
% 3.35/1.48  Total                : 0.74
% 3.35/1.48  Index Insertion      : 0.00
% 3.35/1.48  Index Deletion       : 0.00
% 3.35/1.48  Index Matching       : 0.00
% 3.35/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
