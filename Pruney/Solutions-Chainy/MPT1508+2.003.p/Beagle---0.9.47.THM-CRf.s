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
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 203 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 ( 939 expanded)
%              Number of equality atoms :   13 (  51 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

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

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_159,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_139,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    k16_lattice3('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

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
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_57,plain,(
    ! [A_35] :
      ( l2_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_44,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    ! [D_23,B_19,C_20] :
      ( r2_hidden(D_23,a_2_1_lattice3(B_19,C_20))
      | ~ r3_lattice3(B_19,D_23,C_20)
      | ~ m1_subset_1(D_23,u1_struct_0(B_19))
      | ~ l3_lattices(B_19)
      | v2_struct_0(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k16_lattice3(A_16,B_17),u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( k15_lattice3(A_13,a_2_1_lattice3(A_13,B_15)) = k16_lattice3(A_13,B_15)
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_118,plain,(
    ! [A_65,B_66,C_67] :
      ( r3_lattices(A_65,B_66,k15_lattice3(A_65,C_67))
      | ~ r2_hidden(B_66,C_67)
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l3_lattices(A_65)
      | ~ v4_lattice3(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_220,plain,(
    ! [A_84,B_85,B_86] :
      ( r3_lattices(A_84,B_85,k16_lattice3(A_84,B_86))
      | ~ r2_hidden(B_85,a_2_1_lattice3(A_84,B_86))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l3_lattices(A_84)
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | v2_struct_0(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_118])).

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

tff(c_488,plain,(
    ! [A_131,B_132,B_133] :
      ( r1_lattices(A_131,B_132,k16_lattice3(A_131,B_133))
      | ~ m1_subset_1(k16_lattice3(A_131,B_133),u1_struct_0(A_131))
      | ~ v9_lattices(A_131)
      | ~ v8_lattices(A_131)
      | ~ v6_lattices(A_131)
      | ~ r2_hidden(B_132,a_2_1_lattice3(A_131,B_133))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ v4_lattice3(A_131)
      | ~ v10_lattices(A_131)
      | ~ l3_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_220,c_22])).

tff(c_491,plain,(
    ! [A_16,B_132,B_17] :
      ( r1_lattices(A_16,B_132,k16_lattice3(A_16,B_17))
      | ~ v9_lattices(A_16)
      | ~ v8_lattices(A_16)
      | ~ v6_lattices(A_16)
      | ~ r2_hidden(B_132,a_2_1_lattice3(A_16,B_17))
      | ~ m1_subset_1(B_132,u1_struct_0(A_16))
      | ~ v4_lattice3(A_16)
      | ~ v10_lattices(A_16)
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_28,c_488])).

tff(c_38,plain,(
    ! [A_24,C_30,B_28] :
      ( r3_lattices(A_24,k16_lattice3(A_24,C_30),B_28)
      | ~ r2_hidden(B_28,C_30)
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | ~ v4_lattice3(A_24)
      | ~ v10_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

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

tff(c_374,plain,(
    ! [A_111,C_112,B_113] :
      ( r1_lattices(A_111,k16_lattice3(A_111,C_112),B_113)
      | ~ m1_subset_1(k16_lattice3(A_111,C_112),u1_struct_0(A_111))
      | ~ v9_lattices(A_111)
      | ~ v8_lattices(A_111)
      | ~ v6_lattices(A_111)
      | ~ r2_hidden(B_113,C_112)
      | ~ m1_subset_1(B_113,u1_struct_0(A_111))
      | ~ l3_lattices(A_111)
      | ~ v4_lattice3(A_111)
      | ~ v10_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_387,plain,(
    ! [A_116,B_117,B_118] :
      ( r1_lattices(A_116,k16_lattice3(A_116,B_117),B_118)
      | ~ v9_lattices(A_116)
      | ~ v8_lattices(A_116)
      | ~ v6_lattices(A_116)
      | ~ r2_hidden(B_118,B_117)
      | ~ m1_subset_1(B_118,u1_struct_0(A_116))
      | ~ v4_lattice3(A_116)
      | ~ v10_lattices(A_116)
      | ~ l3_lattices(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_28,c_374])).

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

tff(c_556,plain,(
    ! [A_150,B_151,B_152] :
      ( k16_lattice3(A_150,B_151) = B_152
      | ~ r1_lattices(A_150,B_152,k16_lattice3(A_150,B_151))
      | ~ m1_subset_1(k16_lattice3(A_150,B_151),u1_struct_0(A_150))
      | ~ l2_lattices(A_150)
      | ~ v4_lattices(A_150)
      | ~ v9_lattices(A_150)
      | ~ v8_lattices(A_150)
      | ~ v6_lattices(A_150)
      | ~ r2_hidden(B_152,B_151)
      | ~ m1_subset_1(B_152,u1_struct_0(A_150))
      | ~ v4_lattice3(A_150)
      | ~ v10_lattices(A_150)
      | ~ l3_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_387,c_24])).

tff(c_564,plain,(
    ! [A_153,B_154,B_155] :
      ( k16_lattice3(A_153,B_154) = B_155
      | ~ m1_subset_1(k16_lattice3(A_153,B_154),u1_struct_0(A_153))
      | ~ l2_lattices(A_153)
      | ~ v4_lattices(A_153)
      | ~ r2_hidden(B_155,B_154)
      | ~ v9_lattices(A_153)
      | ~ v8_lattices(A_153)
      | ~ v6_lattices(A_153)
      | ~ r2_hidden(B_155,a_2_1_lattice3(A_153,B_154))
      | ~ m1_subset_1(B_155,u1_struct_0(A_153))
      | ~ v4_lattice3(A_153)
      | ~ v10_lattices(A_153)
      | ~ l3_lattices(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_491,c_556])).

tff(c_579,plain,(
    ! [A_159,B_160,B_161] :
      ( k16_lattice3(A_159,B_160) = B_161
      | ~ l2_lattices(A_159)
      | ~ v4_lattices(A_159)
      | ~ r2_hidden(B_161,B_160)
      | ~ v9_lattices(A_159)
      | ~ v8_lattices(A_159)
      | ~ v6_lattices(A_159)
      | ~ r2_hidden(B_161,a_2_1_lattice3(A_159,B_160))
      | ~ m1_subset_1(B_161,u1_struct_0(A_159))
      | ~ v4_lattice3(A_159)
      | ~ v10_lattices(A_159)
      | ~ l3_lattices(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_28,c_564])).

tff(c_584,plain,(
    ! [B_162,C_163,D_164] :
      ( k16_lattice3(B_162,C_163) = D_164
      | ~ l2_lattices(B_162)
      | ~ v4_lattices(B_162)
      | ~ r2_hidden(D_164,C_163)
      | ~ v9_lattices(B_162)
      | ~ v8_lattices(B_162)
      | ~ v6_lattices(B_162)
      | ~ v4_lattice3(B_162)
      | ~ v10_lattices(B_162)
      | ~ r3_lattice3(B_162,D_164,C_163)
      | ~ m1_subset_1(D_164,u1_struct_0(B_162))
      | ~ l3_lattices(B_162)
      | v2_struct_0(B_162) ) ),
    inference(resolution,[status(thm)],[c_30,c_579])).

tff(c_588,plain,
    ( k16_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ l2_lattices('#skF_2')
    | ~ v4_lattices('#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v9_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | ~ v4_lattice3('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_584])).

tff(c_592,plain,
    ( k16_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ v4_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_54,c_52,c_153,c_175,c_164,c_46,c_61,c_588])).

tff(c_593,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_42,c_592])).

tff(c_596,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_593])).

tff(c_599,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_596])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.54  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.32/1.54  
% 3.32/1.54  %Foreground sorts:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Background operators:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Foreground operators:
% 3.32/1.54  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.32/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.54  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.32/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.54  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.54  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.32/1.54  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.32/1.54  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.32/1.54  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.32/1.54  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.32/1.54  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.32/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.54  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.32/1.54  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 3.32/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.54  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.32/1.54  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.32/1.54  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.54  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.54  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.32/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.54  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.32/1.54  
% 3.32/1.56  tff(f_159, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 3.32/1.56  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 3.32/1.56  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.32/1.56  tff(f_53, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.32/1.56  tff(f_120, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 3.32/1.56  tff(f_106, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 3.32/1.56  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 3.32/1.56  tff(f_139, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 3.32/1.56  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 3.32/1.56  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_50, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_54, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.56  tff(c_42, plain, (k16_lattice3('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_52, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.56  tff(c_130, plain, (![A_74, B_75, C_76]: (r3_lattices(A_74, B_75, C_76) | ~r1_lattices(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v9_lattices(A_74) | ~v8_lattices(A_74) | ~v6_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.56  tff(c_136, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_130])).
% 3.32/1.56  tff(c_141, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_136])).
% 3.32/1.56  tff(c_142, plain, (![B_75]: (r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_141])).
% 3.32/1.56  tff(c_143, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_142])).
% 3.32/1.56  tff(c_146, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_143])).
% 3.32/1.56  tff(c_149, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_146])).
% 3.32/1.56  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_149])).
% 3.32/1.56  tff(c_153, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_142])).
% 3.32/1.56  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.56  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.56  tff(c_152, plain, (![B_75]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_142])).
% 3.32/1.56  tff(c_154, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_152])).
% 3.32/1.56  tff(c_157, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_154])).
% 3.32/1.56  tff(c_160, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_157])).
% 3.32/1.56  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_160])).
% 3.32/1.56  tff(c_163, plain, (![B_75]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_75, '#skF_3') | ~r1_lattices('#skF_2', B_75, '#skF_3') | ~m1_subset_1(B_75, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_152])).
% 3.32/1.56  tff(c_165, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_163])).
% 3.32/1.56  tff(c_168, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_165])).
% 3.32/1.56  tff(c_171, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_168])).
% 3.32/1.56  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_171])).
% 3.32/1.56  tff(c_175, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_163])).
% 3.32/1.56  tff(c_164, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 3.32/1.56  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_57, plain, (![A_35]: (l2_lattices(A_35) | ~l3_lattices(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.56  tff(c_61, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_50, c_57])).
% 3.32/1.56  tff(c_44, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.32/1.56  tff(c_30, plain, (![D_23, B_19, C_20]: (r2_hidden(D_23, a_2_1_lattice3(B_19, C_20)) | ~r3_lattice3(B_19, D_23, C_20) | ~m1_subset_1(D_23, u1_struct_0(B_19)) | ~l3_lattices(B_19) | v2_struct_0(B_19))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.32/1.56  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(k16_lattice3(A_16, B_17), u1_struct_0(A_16)) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.56  tff(c_26, plain, (![A_13, B_15]: (k15_lattice3(A_13, a_2_1_lattice3(A_13, B_15))=k16_lattice3(A_13, B_15) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.32/1.56  tff(c_118, plain, (![A_65, B_66, C_67]: (r3_lattices(A_65, B_66, k15_lattice3(A_65, C_67)) | ~r2_hidden(B_66, C_67) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l3_lattices(A_65) | ~v4_lattice3(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.32/1.56  tff(c_220, plain, (![A_84, B_85, B_86]: (r3_lattices(A_84, B_85, k16_lattice3(A_84, B_86)) | ~r2_hidden(B_85, a_2_1_lattice3(A_84, B_86)) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l3_lattices(A_84) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | v2_struct_0(A_84) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_26, c_118])).
% 3.32/1.56  tff(c_22, plain, (![A_3, B_4, C_5]: (r1_lattices(A_3, B_4, C_5) | ~r3_lattices(A_3, B_4, C_5) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l3_lattices(A_3) | ~v9_lattices(A_3) | ~v8_lattices(A_3) | ~v6_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.56  tff(c_488, plain, (![A_131, B_132, B_133]: (r1_lattices(A_131, B_132, k16_lattice3(A_131, B_133)) | ~m1_subset_1(k16_lattice3(A_131, B_133), u1_struct_0(A_131)) | ~v9_lattices(A_131) | ~v8_lattices(A_131) | ~v6_lattices(A_131) | ~r2_hidden(B_132, a_2_1_lattice3(A_131, B_133)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~v4_lattice3(A_131) | ~v10_lattices(A_131) | ~l3_lattices(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_220, c_22])).
% 3.32/1.56  tff(c_491, plain, (![A_16, B_132, B_17]: (r1_lattices(A_16, B_132, k16_lattice3(A_16, B_17)) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | ~v6_lattices(A_16) | ~r2_hidden(B_132, a_2_1_lattice3(A_16, B_17)) | ~m1_subset_1(B_132, u1_struct_0(A_16)) | ~v4_lattice3(A_16) | ~v10_lattices(A_16) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_28, c_488])).
% 3.32/1.56  tff(c_38, plain, (![A_24, C_30, B_28]: (r3_lattices(A_24, k16_lattice3(A_24, C_30), B_28) | ~r2_hidden(B_28, C_30) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l3_lattices(A_24) | ~v4_lattice3(A_24) | ~v10_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.32/1.56  tff(c_123, plain, (![A_71, B_72, C_73]: (r1_lattices(A_71, B_72, C_73) | ~r3_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v9_lattices(A_71) | ~v8_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.56  tff(c_374, plain, (![A_111, C_112, B_113]: (r1_lattices(A_111, k16_lattice3(A_111, C_112), B_113) | ~m1_subset_1(k16_lattice3(A_111, C_112), u1_struct_0(A_111)) | ~v9_lattices(A_111) | ~v8_lattices(A_111) | ~v6_lattices(A_111) | ~r2_hidden(B_113, C_112) | ~m1_subset_1(B_113, u1_struct_0(A_111)) | ~l3_lattices(A_111) | ~v4_lattice3(A_111) | ~v10_lattices(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_38, c_123])).
% 3.32/1.56  tff(c_387, plain, (![A_116, B_117, B_118]: (r1_lattices(A_116, k16_lattice3(A_116, B_117), B_118) | ~v9_lattices(A_116) | ~v8_lattices(A_116) | ~v6_lattices(A_116) | ~r2_hidden(B_118, B_117) | ~m1_subset_1(B_118, u1_struct_0(A_116)) | ~v4_lattice3(A_116) | ~v10_lattices(A_116) | ~l3_lattices(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_28, c_374])).
% 3.32/1.56  tff(c_24, plain, (![C_12, B_10, A_6]: (C_12=B_10 | ~r1_lattices(A_6, C_12, B_10) | ~r1_lattices(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l2_lattices(A_6) | ~v4_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.32/1.56  tff(c_556, plain, (![A_150, B_151, B_152]: (k16_lattice3(A_150, B_151)=B_152 | ~r1_lattices(A_150, B_152, k16_lattice3(A_150, B_151)) | ~m1_subset_1(k16_lattice3(A_150, B_151), u1_struct_0(A_150)) | ~l2_lattices(A_150) | ~v4_lattices(A_150) | ~v9_lattices(A_150) | ~v8_lattices(A_150) | ~v6_lattices(A_150) | ~r2_hidden(B_152, B_151) | ~m1_subset_1(B_152, u1_struct_0(A_150)) | ~v4_lattice3(A_150) | ~v10_lattices(A_150) | ~l3_lattices(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_387, c_24])).
% 3.32/1.56  tff(c_564, plain, (![A_153, B_154, B_155]: (k16_lattice3(A_153, B_154)=B_155 | ~m1_subset_1(k16_lattice3(A_153, B_154), u1_struct_0(A_153)) | ~l2_lattices(A_153) | ~v4_lattices(A_153) | ~r2_hidden(B_155, B_154) | ~v9_lattices(A_153) | ~v8_lattices(A_153) | ~v6_lattices(A_153) | ~r2_hidden(B_155, a_2_1_lattice3(A_153, B_154)) | ~m1_subset_1(B_155, u1_struct_0(A_153)) | ~v4_lattice3(A_153) | ~v10_lattices(A_153) | ~l3_lattices(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_491, c_556])).
% 3.32/1.56  tff(c_579, plain, (![A_159, B_160, B_161]: (k16_lattice3(A_159, B_160)=B_161 | ~l2_lattices(A_159) | ~v4_lattices(A_159) | ~r2_hidden(B_161, B_160) | ~v9_lattices(A_159) | ~v8_lattices(A_159) | ~v6_lattices(A_159) | ~r2_hidden(B_161, a_2_1_lattice3(A_159, B_160)) | ~m1_subset_1(B_161, u1_struct_0(A_159)) | ~v4_lattice3(A_159) | ~v10_lattices(A_159) | ~l3_lattices(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_28, c_564])).
% 3.32/1.56  tff(c_584, plain, (![B_162, C_163, D_164]: (k16_lattice3(B_162, C_163)=D_164 | ~l2_lattices(B_162) | ~v4_lattices(B_162) | ~r2_hidden(D_164, C_163) | ~v9_lattices(B_162) | ~v8_lattices(B_162) | ~v6_lattices(B_162) | ~v4_lattice3(B_162) | ~v10_lattices(B_162) | ~r3_lattice3(B_162, D_164, C_163) | ~m1_subset_1(D_164, u1_struct_0(B_162)) | ~l3_lattices(B_162) | v2_struct_0(B_162))), inference(resolution, [status(thm)], [c_30, c_579])).
% 3.32/1.56  tff(c_588, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3' | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | ~r2_hidden('#skF_3', '#skF_4') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_584])).
% 3.32/1.56  tff(c_592, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3' | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_54, c_52, c_153, c_175, c_164, c_46, c_61, c_588])).
% 3.32/1.56  tff(c_593, plain, (~v4_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_42, c_592])).
% 3.32/1.56  tff(c_596, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_593])).
% 3.32/1.56  tff(c_599, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_596])).
% 3.32/1.56  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_599])).
% 3.32/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  Inference rules
% 3.32/1.56  ----------------------
% 3.32/1.56  #Ref     : 0
% 3.32/1.56  #Sup     : 104
% 3.32/1.56  #Fact    : 0
% 3.32/1.56  #Define  : 0
% 3.32/1.56  #Split   : 4
% 3.32/1.56  #Chain   : 0
% 3.32/1.56  #Close   : 0
% 3.32/1.56  
% 3.32/1.56  Ordering : KBO
% 3.32/1.56  
% 3.32/1.56  Simplification rules
% 3.32/1.56  ----------------------
% 3.32/1.56  #Subsume      : 18
% 3.32/1.56  #Demod        : 114
% 3.32/1.56  #Tautology    : 30
% 3.32/1.56  #SimpNegUnit  : 34
% 3.32/1.56  #BackRed      : 0
% 3.32/1.56  
% 3.32/1.56  #Partial instantiations: 0
% 3.32/1.56  #Strategies tried      : 1
% 3.32/1.56  
% 3.32/1.56  Timing (in seconds)
% 3.32/1.56  ----------------------
% 3.32/1.56  Preprocessing        : 0.34
% 3.32/1.56  Parsing              : 0.19
% 3.32/1.56  CNF conversion       : 0.03
% 3.32/1.56  Main loop            : 0.40
% 3.32/1.56  Inferencing          : 0.17
% 3.32/1.56  Reduction            : 0.11
% 3.32/1.56  Demodulation         : 0.07
% 3.32/1.56  BG Simplification    : 0.02
% 3.32/1.56  Subsumption          : 0.08
% 3.32/1.56  Abstraction          : 0.02
% 3.32/1.56  MUC search           : 0.00
% 3.32/1.56  Cooper               : 0.00
% 3.32/1.56  Total                : 0.78
% 3.32/1.56  Index Insertion      : 0.00
% 3.32/1.56  Index Deletion       : 0.00
% 3.32/1.56  Index Matching       : 0.00
% 3.32/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
