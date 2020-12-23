%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:14 EST 2020

% Result     : Theorem 10.29s
% Output     : CNFRefutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :  227 (3104 expanded)
%              Number of leaves         :   38 (1087 expanded)
%              Depth                    :   20
%              Number of atoms          :  519 (13849 expanded)
%              Number of equality atoms :  153 (3143 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

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

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v11_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( k4_lattices(A,B,C) = k4_lattices(A,B,D)
                        & k3_lattices(A,B,C) = k3_lattices(A,B,D) )
                     => C = D ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

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

tff(f_107,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v11_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => k3_lattices(A,B,k4_lattices(A,C,D)) = k4_lattices(A,k3_lattices(A,B,C),k3_lattices(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_54,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_58] :
      ( l2_lattices(A_58)
      | ~ l3_lattices(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_65,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_61])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_44,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_159,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k3_lattices(A_74,B_75,C_76),u1_struct_0(A_74))
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l2_lattices(A_74)
      | ~ v4_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_164,plain,
    ( m1_subset_1(k3_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_159])).

tff(c_167,plain,
    ( m1_subset_1(k3_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_52,c_50,c_164])).

tff(c_168,plain,
    ( m1_subset_1(k3_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v4_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_167])).

tff(c_173,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_176,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_179,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_176])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_179])).

tff(c_183,plain,(
    v4_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_423,plain,(
    ! [A_86,B_87,C_88] :
      ( k3_lattices(A_86,B_87,C_88) = k1_lattices(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l2_lattices(A_86)
      | ~ v4_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_435,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_5') = k1_lattices('#skF_3',B_87,'#skF_5')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_423])).

tff(c_451,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_5') = k1_lattices('#skF_3',B_87,'#skF_5')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_435])).

tff(c_905,plain,(
    ! [B_98] :
      ( k3_lattices('#skF_3',B_98,'#skF_5') = k1_lattices('#skF_3',B_98,'#skF_5')
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_451])).

tff(c_951,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_5') = k1_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_905])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k3_lattices(A_19,B_20,C_21),u1_struct_0(A_19))
      | ~ m1_subset_1(C_21,u1_struct_0(A_19))
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l2_lattices(A_19)
      | ~ v4_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_966,plain,
    ( m1_subset_1(k1_lattices('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_28])).

tff(c_970,plain,
    ( m1_subset_1(k1_lattices('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_48,c_50,c_966])).

tff(c_971,plain,(
    m1_subset_1(k1_lattices('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_970])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [A_69,B_70] :
      ( k1_lattices(A_69,B_70,B_70) = B_70
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v9_lattices(A_69)
      | ~ v8_lattices(A_69)
      | ~ v6_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_94,plain,
    ( k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_88])).

tff(c_103,plain,
    ( k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_94])).

tff(c_104,plain,
    ( k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_103])).

tff(c_113,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_126,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_129,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_126])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_129])).

tff(c_133,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_66,plain,(
    ! [A_59] :
      ( l1_lattices(A_59)
      | ~ l3_lattices(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_437,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_6') = k1_lattices('#skF_3',B_87,'#skF_6')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_423])).

tff(c_455,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_6') = k1_lattices('#skF_3',B_87,'#skF_6')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_437])).

tff(c_556,plain,(
    ! [B_90] :
      ( k3_lattices('#skF_3',B_90,'#skF_6') = k1_lattices('#skF_3',B_90,'#skF_6')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_455])).

tff(c_598,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_6') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_556])).

tff(c_182,plain,(
    m1_subset_1(k3_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_615,plain,(
    m1_subset_1(k1_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_182])).

tff(c_861,plain,(
    ! [A_95,B_96,C_97] :
      ( k4_lattices(A_95,B_96,C_97) = k2_lattices(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_lattices(A_95)
      | ~ v6_lattices(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_865,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',B_96,k1_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_615,c_861])).

tff(c_884,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',B_96,k1_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_865])).

tff(c_5378,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_3',B_153,k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',B_153,k1_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_884])).

tff(c_5430,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_971,c_5378])).

tff(c_206,plain,(
    ! [A_77,C_78,B_79] :
      ( k3_lattices(A_77,C_78,B_79) = k3_lattices(A_77,B_79,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_77))
      | ~ m1_subset_1(B_79,u1_struct_0(A_77))
      | ~ l2_lattices(A_77)
      | ~ v4_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_216,plain,(
    ! [B_79] :
      ( k3_lattices('#skF_3',B_79,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_206])).

tff(c_230,plain,(
    ! [B_79] :
      ( k3_lattices('#skF_3',B_79,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_216])).

tff(c_274,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_3',B_83,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_230])).

tff(c_295,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_274])).

tff(c_315,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_295])).

tff(c_613,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_315])).

tff(c_433,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_4') = k1_lattices('#skF_3',B_87,'#skF_4')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_423])).

tff(c_447,plain,(
    ! [B_87] :
      ( k3_lattices('#skF_3',B_87,'#skF_4') = k1_lattices('#skF_3',B_87,'#skF_4')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_433])).

tff(c_1294,plain,(
    ! [B_105] :
      ( k3_lattices('#skF_3',B_105,'#skF_4') = k1_lattices('#skF_3',B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_447])).

tff(c_1318,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1294])).

tff(c_1339,plain,(
    k1_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_1318])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,
    ( ~ v8_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_134,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_140,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_143,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_140])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_143])).

tff(c_147,plain,(
    v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_240,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_lattices(A_80,B_81,k1_lattices(A_80,B_81,C_82)) = B_81
      | ~ m1_subset_1(C_82,u1_struct_0(A_80))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ v9_lattices(A_80)
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_250,plain,(
    ! [B_81] :
      ( k2_lattices('#skF_3',B_81,k1_lattices('#skF_3',B_81,'#skF_4')) = B_81
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_240])).

tff(c_264,plain,(
    ! [B_81] :
      ( k2_lattices('#skF_3',B_81,k1_lattices('#skF_3',B_81,'#skF_4')) = B_81
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_147,c_250])).

tff(c_1372,plain,(
    ! [B_106] :
      ( k2_lattices('#skF_3',B_106,k1_lattices('#skF_3',B_106,'#skF_4')) = B_106
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_264])).

tff(c_1389,plain,(
    k2_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_5','#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_1372])).

tff(c_1409,plain,(
    k2_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1389])).

tff(c_5420,plain,(
    k4_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_5378])).

tff(c_5448,plain,(
    k4_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_5420])).

tff(c_875,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_5') = k2_lattices('#skF_3',B_96,'#skF_5')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_861])).

tff(c_895,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_5') = k2_lattices('#skF_3',B_96,'#skF_5')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_875])).

tff(c_1481,plain,(
    ! [B_108] :
      ( k4_lattices('#skF_3',B_108,'#skF_5') = k2_lattices('#skF_3',B_108,'#skF_5')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_895])).

tff(c_1510,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_615,c_1481])).

tff(c_669,plain,(
    ! [A_91,C_92,B_93] :
      ( k4_lattices(A_91,C_92,B_93) = k4_lattices(A_91,B_93,C_92)
      | ~ m1_subset_1(C_92,u1_struct_0(A_91))
      | ~ m1_subset_1(B_93,u1_struct_0(A_91))
      | ~ l1_lattices(A_91)
      | ~ v6_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_683,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_669])).

tff(c_703,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_683])).

tff(c_1625,plain,(
    ! [B_110] :
      ( k4_lattices('#skF_3',B_110,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_110)
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_703])).

tff(c_1654,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = k4_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_615,c_1625])).

tff(c_2390,plain,(
    k4_lattices('#skF_3','#skF_5',k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1654])).

tff(c_5456,plain,(
    k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5448,c_2390])).

tff(c_877,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_6') = k2_lattices('#skF_3',B_96,'#skF_6')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_861])).

tff(c_899,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_6') = k2_lattices('#skF_3',B_96,'#skF_6')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_877])).

tff(c_1565,plain,(
    ! [B_109] :
      ( k4_lattices('#skF_3',B_109,'#skF_6') = k2_lattices('#skF_3',B_109,'#skF_6')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_899])).

tff(c_1607,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1565])).

tff(c_1523,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_1481])).

tff(c_873,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_4') = k2_lattices('#skF_3',B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_861])).

tff(c_891,plain,(
    ! [B_96] :
      ( k4_lattices('#skF_3',B_96,'#skF_4') = k2_lattices('#skF_3',B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_873])).

tff(c_1220,plain,(
    ! [B_104] :
      ( k4_lattices('#skF_3',B_104,'#skF_4') = k2_lattices('#skF_3',B_104,'#skF_4')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_891])).

tff(c_1264,plain,(
    k4_lattices('#skF_3','#skF_6','#skF_4') = k2_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1220])).

tff(c_685,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_6') = k4_lattices('#skF_3','#skF_6',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_669])).

tff(c_707,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_6') = k4_lattices('#skF_3','#skF_6',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_685])).

tff(c_811,plain,(
    ! [B_94] :
      ( k4_lattices('#skF_3',B_94,'#skF_6') = k4_lattices('#skF_3','#skF_6',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_707])).

tff(c_853,plain,(
    k4_lattices('#skF_3','#skF_6','#skF_4') = k4_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_811])).

tff(c_1269,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_853])).

tff(c_46,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k4_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1279,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_46])).

tff(c_1531,plain,(
    k2_lattices('#skF_3','#skF_6','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1279])).

tff(c_1543,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1269])).

tff(c_1620,plain,(
    k2_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1607,c_1543])).

tff(c_1681,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1523])).

tff(c_56,plain,(
    v11_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,
    ( ~ v8_lattices('#skF_3')
    | k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_148,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_151,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_154,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_151])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_154])).

tff(c_158,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_96,plain,
    ( k1_lattices('#skF_3','#skF_5','#skF_5') = '#skF_5'
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_107,plain,
    ( k1_lattices('#skF_3','#skF_5','#skF_5') = '#skF_5'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_96])).

tff(c_108,plain,
    ( k1_lattices('#skF_3','#skF_5','#skF_5') = '#skF_5'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_107])).

tff(c_185,plain,(
    k1_lattices('#skF_3','#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_158,c_147,c_108])).

tff(c_929,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_5') = k1_lattices('#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_905])).

tff(c_950,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_929])).

tff(c_1063,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k4_lattices(A_99,k3_lattices(A_99,B_100,C_101),k3_lattices(A_99,B_100,D_102)) = k3_lattices(A_99,B_100,k4_lattices(A_99,C_101,D_102))
      | ~ m1_subset_1(D_102,u1_struct_0(A_99))
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l3_lattices(A_99)
      | ~ v11_lattices(A_99)
      | ~ v10_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1087,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_101),'#skF_5') = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_101,'#skF_5'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_1063])).

tff(c_1136,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_101),'#skF_5') = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_101,'#skF_5'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_50,c_1087])).

tff(c_5171,plain,(
    ! [C_148] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_148),'#skF_5') = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_148,'#skF_5'))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1136])).

tff(c_5210,plain,(
    k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_4'),'#skF_5') = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_5171])).

tff(c_5240,plain,(
    k3_lattices('#skF_3','#skF_5',k2_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1681,c_613,c_5210])).

tff(c_5539,plain,(
    k3_lattices('#skF_3','#skF_5',k2_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5456,c_5240])).

tff(c_1544,plain,(
    k4_lattices('#skF_3','#skF_6','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1264])).

tff(c_1677,plain,(
    k4_lattices('#skF_3','#skF_6','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1544])).

tff(c_599,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_6') = k1_lattices('#skF_3','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_556])).

tff(c_220,plain,(
    ! [B_79] :
      ( k3_lattices('#skF_3',B_79,'#skF_6') = k3_lattices('#skF_3','#skF_6',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_206])).

tff(c_238,plain,(
    ! [B_79] :
      ( k3_lattices('#skF_3',B_79,'#skF_6') = k3_lattices('#skF_3','#skF_6',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_65,c_220])).

tff(c_465,plain,(
    ! [B_89] :
      ( k3_lattices('#skF_3',B_89,'#skF_6') = k3_lattices('#skF_3','#skF_6',B_89)
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_238])).

tff(c_505,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_6') = k3_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_465])).

tff(c_710,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_5') = k1_lattices('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_505])).

tff(c_962,plain,(
    k1_lattices('#skF_3','#skF_5','#skF_6') = k1_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_710])).

tff(c_1042,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_6') = k1_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_599])).

tff(c_1093,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_101),k1_lattices('#skF_3','#skF_4','#skF_6')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_101,'#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_1063])).

tff(c_1142,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_101),k1_lattices('#skF_3','#skF_4','#skF_6')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_101,'#skF_4'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_52,c_1093])).

tff(c_11758,plain,(
    ! [C_217] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_217),k1_lattices('#skF_3','#skF_4','#skF_6')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_217,'#skF_4'))
      | ~ m1_subset_1(C_217,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1142])).

tff(c_11779,plain,
    ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_6','#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_11758])).

tff(c_11795,plain,(
    k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5430,c_5539,c_1677,c_11779])).

tff(c_11805,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11795,c_5430])).

tff(c_316,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_274])).

tff(c_612,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_316])).

tff(c_1321,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_4') = k1_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1294])).

tff(c_1341,plain,(
    k1_lattices('#skF_3','#skF_6','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_1321])).

tff(c_1410,plain,(
    k2_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_6','#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_1372])).

tff(c_1428,plain,(
    k2_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1410])).

tff(c_5423,plain,(
    k4_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_5378])).

tff(c_5450,plain,(
    k4_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_5423])).

tff(c_1594,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_615,c_1565])).

tff(c_840,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = k4_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_615,c_811])).

tff(c_2562,plain,(
    k4_lattices('#skF_3','#skF_6',k1_lattices('#skF_3','#skF_4','#skF_6')) = k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1594,c_840])).

tff(c_5534,plain,(
    k2_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5450,c_2562])).

tff(c_5841,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5534,c_1594])).

tff(c_98,plain,
    ( k1_lattices('#skF_3','#skF_6','#skF_6') = '#skF_6'
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_111,plain,
    ( k1_lattices('#skF_3','#skF_6','#skF_6') = '#skF_6'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_98])).

tff(c_112,plain,
    ( k1_lattices('#skF_3','#skF_6','#skF_6') = '#skF_6'
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_111])).

tff(c_197,plain,(
    k1_lattices('#skF_3','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_158,c_147,c_112])).

tff(c_583,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_6') = k1_lattices('#skF_3','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_556])).

tff(c_601,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_583])).

tff(c_1117,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_6',C_101),'#skF_6') = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3',C_101,'#skF_6'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_1063])).

tff(c_1166,plain,(
    ! [C_101] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_6',C_101),'#skF_6') = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3',C_101,'#skF_6'))
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_48,c_48,c_1117])).

tff(c_5890,plain,(
    ! [C_158] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_6',C_158),'#skF_6') = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3',C_158,'#skF_6'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1166])).

tff(c_5929,plain,(
    k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_4'),'#skF_6') = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_5890])).

tff(c_5959,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = k3_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1607,c_612,c_5929])).

tff(c_6016,plain,(
    k3_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5841,c_5959])).

tff(c_1263,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1220])).

tff(c_681,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_669])).

tff(c_699,plain,(
    ! [B_93] :
      ( k4_lattices('#skF_3',B_93,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_681])).

tff(c_1168,plain,(
    ! [B_103] :
      ( k4_lattices('#skF_3',B_103,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_699])).

tff(c_1192,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k4_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1168])).

tff(c_1213,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k4_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1192])).

tff(c_1274,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1213])).

tff(c_1284,plain,(
    k2_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_1274])).

tff(c_1285,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1263])).

tff(c_1541,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1285])).

tff(c_1679,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1541])).

tff(c_1078,plain,(
    ! [D_102] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k3_lattices('#skF_3','#skF_6',D_102)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5',D_102))
      | ~ m1_subset_1(D_102,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_1063])).

tff(c_1127,plain,(
    ! [D_102] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k3_lattices('#skF_3','#skF_6',D_102)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5',D_102))
      | ~ m1_subset_1(D_102,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_48,c_50,c_1078])).

tff(c_12209,plain,(
    ! [D_218] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k3_lattices('#skF_3','#skF_6',D_218)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5',D_218))
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1127])).

tff(c_12236,plain,
    ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_5'),k1_lattices('#skF_3','#skF_4','#skF_6')) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_12209])).

tff(c_12253,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11805,c_6016,c_1679,c_12236])).

tff(c_12255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_12253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.29/3.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/3.51  
% 10.39/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/3.51  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 10.39/3.51  
% 10.39/3.51  %Foreground sorts:
% 10.39/3.51  
% 10.39/3.51  
% 10.39/3.51  %Background operators:
% 10.39/3.51  
% 10.39/3.51  
% 10.39/3.51  %Foreground operators:
% 10.39/3.51  tff(l3_lattices, type, l3_lattices: $i > $o).
% 10.39/3.51  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 10.39/3.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.39/3.51  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 10.39/3.51  tff(l2_lattices, type, l2_lattices: $i > $o).
% 10.39/3.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.39/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.39/3.51  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 10.39/3.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.39/3.51  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 10.39/3.51  tff(l1_lattices, type, l1_lattices: $i > $o).
% 10.39/3.51  tff('#skF_5', type, '#skF_5': $i).
% 10.39/3.51  tff(v4_lattices, type, v4_lattices: $i > $o).
% 10.39/3.51  tff('#skF_6', type, '#skF_6': $i).
% 10.39/3.51  tff(v6_lattices, type, v6_lattices: $i > $o).
% 10.39/3.51  tff(v9_lattices, type, v9_lattices: $i > $o).
% 10.39/3.51  tff('#skF_3', type, '#skF_3': $i).
% 10.39/3.51  tff(v5_lattices, type, v5_lattices: $i > $o).
% 10.39/3.51  tff(v10_lattices, type, v10_lattices: $i > $o).
% 10.39/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.39/3.51  tff('#skF_4', type, '#skF_4': $i).
% 10.39/3.51  tff(v11_lattices, type, v11_lattices: $i > $o).
% 10.39/3.51  tff(v8_lattices, type, v8_lattices: $i > $o).
% 10.39/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.39/3.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.39/3.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.39/3.51  tff(v7_lattices, type, v7_lattices: $i > $o).
% 10.39/3.51  
% 10.61/3.54  tff(f_194, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 10.61/3.54  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 10.61/3.54  tff(f_107, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 10.61/3.54  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattices)).
% 10.61/3.54  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 10.61/3.54  tff(f_149, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 10.61/3.54  tff(f_133, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 10.61/3.54  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 10.61/3.54  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 10.61/3.54  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 10.61/3.54  tff(f_169, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_lattices(A, B, k4_lattices(A, C, D)) = k4_lattices(A, k3_lattices(A, B, C), k3_lattices(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 10.61/3.54  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_54, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_58, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/3.54  tff(c_61, plain, (![A_58]: (l2_lattices(A_58) | ~l3_lattices(A_58))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.61/3.54  tff(c_65, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_54, c_61])).
% 10.61/3.54  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_44, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_159, plain, (![A_74, B_75, C_76]: (m1_subset_1(k3_lattices(A_74, B_75, C_76), u1_struct_0(A_74)) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l2_lattices(A_74) | ~v4_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.61/3.54  tff(c_164, plain, (m1_subset_1(k3_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_159])).
% 10.61/3.54  tff(c_167, plain, (m1_subset_1(k3_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_52, c_50, c_164])).
% 10.61/3.54  tff(c_168, plain, (m1_subset_1(k3_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_167])).
% 10.61/3.54  tff(c_173, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 10.61/3.54  tff(c_176, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_173])).
% 10.61/3.54  tff(c_179, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_176])).
% 10.61/3.54  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_179])).
% 10.61/3.54  tff(c_183, plain, (v4_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 10.61/3.54  tff(c_423, plain, (![A_86, B_87, C_88]: (k3_lattices(A_86, B_87, C_88)=k1_lattices(A_86, B_87, C_88) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l2_lattices(A_86) | ~v4_lattices(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.61/3.54  tff(c_435, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_5')=k1_lattices('#skF_3', B_87, '#skF_5') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_423])).
% 10.61/3.54  tff(c_451, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_5')=k1_lattices('#skF_3', B_87, '#skF_5') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_435])).
% 10.61/3.54  tff(c_905, plain, (![B_98]: (k3_lattices('#skF_3', B_98, '#skF_5')=k1_lattices('#skF_3', B_98, '#skF_5') | ~m1_subset_1(B_98, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_451])).
% 10.61/3.54  tff(c_951, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_5')=k1_lattices('#skF_3', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_905])).
% 10.61/3.54  tff(c_28, plain, (![A_19, B_20, C_21]: (m1_subset_1(k3_lattices(A_19, B_20, C_21), u1_struct_0(A_19)) | ~m1_subset_1(C_21, u1_struct_0(A_19)) | ~m1_subset_1(B_20, u1_struct_0(A_19)) | ~l2_lattices(A_19) | ~v4_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.61/3.54  tff(c_966, plain, (m1_subset_1(k1_lattices('#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_951, c_28])).
% 10.61/3.54  tff(c_970, plain, (m1_subset_1(k1_lattices('#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_48, c_50, c_966])).
% 10.61/3.54  tff(c_971, plain, (m1_subset_1(k1_lattices('#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_970])).
% 10.61/3.54  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/3.54  tff(c_88, plain, (![A_69, B_70]: (k1_lattices(A_69, B_70, B_70)=B_70 | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v9_lattices(A_69) | ~v8_lattices(A_69) | ~v6_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.61/3.54  tff(c_94, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_88])).
% 10.61/3.54  tff(c_103, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_94])).
% 10.61/3.54  tff(c_104, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_103])).
% 10.61/3.54  tff(c_113, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_104])).
% 10.61/3.54  tff(c_126, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_113])).
% 10.61/3.54  tff(c_129, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_126])).
% 10.61/3.54  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_129])).
% 10.61/3.54  tff(c_133, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_104])).
% 10.61/3.54  tff(c_66, plain, (![A_59]: (l1_lattices(A_59) | ~l3_lattices(A_59))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.61/3.54  tff(c_70, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_54, c_66])).
% 10.61/3.54  tff(c_437, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_6')=k1_lattices('#skF_3', B_87, '#skF_6') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_423])).
% 10.61/3.54  tff(c_455, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_6')=k1_lattices('#skF_3', B_87, '#skF_6') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_437])).
% 10.61/3.54  tff(c_556, plain, (![B_90]: (k3_lattices('#skF_3', B_90, '#skF_6')=k1_lattices('#skF_3', B_90, '#skF_6') | ~m1_subset_1(B_90, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_455])).
% 10.61/3.54  tff(c_598, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_6')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_556])).
% 10.61/3.54  tff(c_182, plain, (m1_subset_1(k3_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_168])).
% 10.61/3.54  tff(c_615, plain, (m1_subset_1(k1_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_598, c_182])).
% 10.61/3.54  tff(c_861, plain, (![A_95, B_96, C_97]: (k4_lattices(A_95, B_96, C_97)=k2_lattices(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_lattices(A_95) | ~v6_lattices(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.61/3.54  tff(c_865, plain, (![B_96]: (k4_lattices('#skF_3', B_96, k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', B_96, k1_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_615, c_861])).
% 10.61/3.54  tff(c_884, plain, (![B_96]: (k4_lattices('#skF_3', B_96, k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', B_96, k1_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_865])).
% 10.61/3.54  tff(c_5378, plain, (![B_153]: (k4_lattices('#skF_3', B_153, k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', B_153, k1_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_153, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_884])).
% 10.61/3.54  tff(c_5430, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_971, c_5378])).
% 10.61/3.54  tff(c_206, plain, (![A_77, C_78, B_79]: (k3_lattices(A_77, C_78, B_79)=k3_lattices(A_77, B_79, C_78) | ~m1_subset_1(C_78, u1_struct_0(A_77)) | ~m1_subset_1(B_79, u1_struct_0(A_77)) | ~l2_lattices(A_77) | ~v4_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.61/3.54  tff(c_216, plain, (![B_79]: (k3_lattices('#skF_3', B_79, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_206])).
% 10.61/3.54  tff(c_230, plain, (![B_79]: (k3_lattices('#skF_3', B_79, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_216])).
% 10.61/3.54  tff(c_274, plain, (![B_83]: (k3_lattices('#skF_3', B_83, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_230])).
% 10.61/3.54  tff(c_295, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_274])).
% 10.61/3.54  tff(c_315, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_295])).
% 10.61/3.54  tff(c_613, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_315])).
% 10.61/3.54  tff(c_433, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_4')=k1_lattices('#skF_3', B_87, '#skF_4') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_423])).
% 10.61/3.54  tff(c_447, plain, (![B_87]: (k3_lattices('#skF_3', B_87, '#skF_4')=k1_lattices('#skF_3', B_87, '#skF_4') | ~m1_subset_1(B_87, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_433])).
% 10.61/3.54  tff(c_1294, plain, (![B_105]: (k3_lattices('#skF_3', B_105, '#skF_4')=k1_lattices('#skF_3', B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_447])).
% 10.61/3.54  tff(c_1318, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1294])).
% 10.61/3.54  tff(c_1339, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_1318])).
% 10.61/3.54  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/3.54  tff(c_132, plain, (~v8_lattices('#skF_3') | ~v9_lattices('#skF_3') | k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_104])).
% 10.61/3.54  tff(c_134, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_132])).
% 10.61/3.54  tff(c_140, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_134])).
% 10.61/3.54  tff(c_143, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_140])).
% 10.61/3.54  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_143])).
% 10.61/3.54  tff(c_147, plain, (v9_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_132])).
% 10.61/3.54  tff(c_240, plain, (![A_80, B_81, C_82]: (k2_lattices(A_80, B_81, k1_lattices(A_80, B_81, C_82))=B_81 | ~m1_subset_1(C_82, u1_struct_0(A_80)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~v9_lattices(A_80) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.61/3.54  tff(c_250, plain, (![B_81]: (k2_lattices('#skF_3', B_81, k1_lattices('#skF_3', B_81, '#skF_4'))=B_81 | ~m1_subset_1(B_81, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_240])).
% 10.61/3.54  tff(c_264, plain, (![B_81]: (k2_lattices('#skF_3', B_81, k1_lattices('#skF_3', B_81, '#skF_4'))=B_81 | ~m1_subset_1(B_81, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_147, c_250])).
% 10.61/3.54  tff(c_1372, plain, (![B_106]: (k2_lattices('#skF_3', B_106, k1_lattices('#skF_3', B_106, '#skF_4'))=B_106 | ~m1_subset_1(B_106, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_264])).
% 10.61/3.54  tff(c_1389, plain, (k2_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_5', '#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_50, c_1372])).
% 10.61/3.54  tff(c_1409, plain, (k2_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1389])).
% 10.61/3.54  tff(c_5420, plain, (k4_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_5378])).
% 10.61/3.54  tff(c_5448, plain, (k4_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_5420])).
% 10.61/3.54  tff(c_875, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_5')=k2_lattices('#skF_3', B_96, '#skF_5') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_861])).
% 10.61/3.54  tff(c_895, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_5')=k2_lattices('#skF_3', B_96, '#skF_5') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_875])).
% 10.61/3.54  tff(c_1481, plain, (![B_108]: (k4_lattices('#skF_3', B_108, '#skF_5')=k2_lattices('#skF_3', B_108, '#skF_5') | ~m1_subset_1(B_108, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_895])).
% 10.61/3.54  tff(c_1510, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_615, c_1481])).
% 10.61/3.54  tff(c_669, plain, (![A_91, C_92, B_93]: (k4_lattices(A_91, C_92, B_93)=k4_lattices(A_91, B_93, C_92) | ~m1_subset_1(C_92, u1_struct_0(A_91)) | ~m1_subset_1(B_93, u1_struct_0(A_91)) | ~l1_lattices(A_91) | ~v6_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.61/3.54  tff(c_683, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_669])).
% 10.61/3.54  tff(c_703, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_683])).
% 10.61/3.54  tff(c_1625, plain, (![B_110]: (k4_lattices('#skF_3', B_110, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_110) | ~m1_subset_1(B_110, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_703])).
% 10.61/3.54  tff(c_1654, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')=k4_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_615, c_1625])).
% 10.61/3.54  tff(c_2390, plain, (k4_lattices('#skF_3', '#skF_5', k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1654])).
% 10.61/3.54  tff(c_5456, plain, (k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5448, c_2390])).
% 10.61/3.54  tff(c_877, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_6')=k2_lattices('#skF_3', B_96, '#skF_6') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_861])).
% 10.61/3.54  tff(c_899, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_6')=k2_lattices('#skF_3', B_96, '#skF_6') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_877])).
% 10.61/3.54  tff(c_1565, plain, (![B_109]: (k4_lattices('#skF_3', B_109, '#skF_6')=k2_lattices('#skF_3', B_109, '#skF_6') | ~m1_subset_1(B_109, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_899])).
% 10.61/3.54  tff(c_1607, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_1565])).
% 10.61/3.54  tff(c_1523, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_1481])).
% 10.61/3.54  tff(c_873, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_4')=k2_lattices('#skF_3', B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_861])).
% 10.61/3.54  tff(c_891, plain, (![B_96]: (k4_lattices('#skF_3', B_96, '#skF_4')=k2_lattices('#skF_3', B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_873])).
% 10.61/3.54  tff(c_1220, plain, (![B_104]: (k4_lattices('#skF_3', B_104, '#skF_4')=k2_lattices('#skF_3', B_104, '#skF_4') | ~m1_subset_1(B_104, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_891])).
% 10.61/3.54  tff(c_1264, plain, (k4_lattices('#skF_3', '#skF_6', '#skF_4')=k2_lattices('#skF_3', '#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_1220])).
% 10.61/3.54  tff(c_685, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_6')=k4_lattices('#skF_3', '#skF_6', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_669])).
% 10.61/3.54  tff(c_707, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_6')=k4_lattices('#skF_3', '#skF_6', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_685])).
% 10.61/3.54  tff(c_811, plain, (![B_94]: (k4_lattices('#skF_3', B_94, '#skF_6')=k4_lattices('#skF_3', '#skF_6', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_707])).
% 10.61/3.54  tff(c_853, plain, (k4_lattices('#skF_3', '#skF_6', '#skF_4')=k4_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_811])).
% 10.61/3.54  tff(c_1269, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_853])).
% 10.61/3.54  tff(c_46, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k4_lattices('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_1279, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_46])).
% 10.61/3.54  tff(c_1531, plain, (k2_lattices('#skF_3', '#skF_6', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1279])).
% 10.61/3.54  tff(c_1543, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1269])).
% 10.61/3.54  tff(c_1620, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1607, c_1543])).
% 10.61/3.54  tff(c_1681, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1523])).
% 10.61/3.54  tff(c_56, plain, (v11_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.61/3.54  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.61/3.54  tff(c_146, plain, (~v8_lattices('#skF_3') | k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_132])).
% 10.61/3.54  tff(c_148, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 10.61/3.54  tff(c_151, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_148])).
% 10.61/3.54  tff(c_154, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_151])).
% 10.61/3.54  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_154])).
% 10.61/3.54  tff(c_158, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 10.61/3.54  tff(c_96, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_5')='#skF_5' | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_88])).
% 10.61/3.54  tff(c_107, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_5')='#skF_5' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_96])).
% 10.61/3.54  tff(c_108, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_5')='#skF_5' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_107])).
% 10.61/3.54  tff(c_185, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_158, c_147, c_108])).
% 10.61/3.54  tff(c_929, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_5')=k1_lattices('#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_905])).
% 10.61/3.54  tff(c_950, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_929])).
% 10.61/3.54  tff(c_1063, plain, (![A_99, B_100, C_101, D_102]: (k4_lattices(A_99, k3_lattices(A_99, B_100, C_101), k3_lattices(A_99, B_100, D_102))=k3_lattices(A_99, B_100, k4_lattices(A_99, C_101, D_102)) | ~m1_subset_1(D_102, u1_struct_0(A_99)) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l3_lattices(A_99) | ~v11_lattices(A_99) | ~v10_lattices(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.61/3.54  tff(c_1087, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_101), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_101, '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_950, c_1063])).
% 10.61/3.54  tff(c_1136, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_101), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_101, '#skF_5')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_50, c_1087])).
% 10.61/3.54  tff(c_5171, plain, (![C_148]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_148), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_148, '#skF_5')) | ~m1_subset_1(C_148, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1136])).
% 10.61/3.54  tff(c_5210, plain, (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', '#skF_4'), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_5171])).
% 10.61/3.54  tff(c_5240, plain, (k3_lattices('#skF_3', '#skF_5', k2_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1681, c_613, c_5210])).
% 10.61/3.54  tff(c_5539, plain, (k3_lattices('#skF_3', '#skF_5', k2_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5456, c_5240])).
% 10.61/3.54  tff(c_1544, plain, (k4_lattices('#skF_3', '#skF_6', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1264])).
% 10.61/3.54  tff(c_1677, plain, (k4_lattices('#skF_3', '#skF_6', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1544])).
% 10.61/3.54  tff(c_599, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_6')=k1_lattices('#skF_3', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_556])).
% 10.61/3.54  tff(c_220, plain, (![B_79]: (k3_lattices('#skF_3', B_79, '#skF_6')=k3_lattices('#skF_3', '#skF_6', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_206])).
% 10.61/3.54  tff(c_238, plain, (![B_79]: (k3_lattices('#skF_3', B_79, '#skF_6')=k3_lattices('#skF_3', '#skF_6', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_65, c_220])).
% 10.61/3.54  tff(c_465, plain, (![B_89]: (k3_lattices('#skF_3', B_89, '#skF_6')=k3_lattices('#skF_3', '#skF_6', B_89) | ~m1_subset_1(B_89, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_238])).
% 10.61/3.54  tff(c_505, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_6')=k3_lattices('#skF_3', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_465])).
% 10.61/3.54  tff(c_710, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_5')=k1_lattices('#skF_3', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_505])).
% 10.61/3.54  tff(c_962, plain, (k1_lattices('#skF_3', '#skF_5', '#skF_6')=k1_lattices('#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_951, c_710])).
% 10.61/3.54  tff(c_1042, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_6')=k1_lattices('#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_962, c_599])).
% 10.61/3.54  tff(c_1093, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_101), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_101, '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_1063])).
% 10.61/3.54  tff(c_1142, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_101), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_101, '#skF_4')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_52, c_1093])).
% 10.61/3.54  tff(c_11758, plain, (![C_217]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_217), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_217, '#skF_4')) | ~m1_subset_1(C_217, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1142])).
% 10.61/3.54  tff(c_11779, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', '#skF_6', '#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_11758])).
% 10.61/3.54  tff(c_11795, plain, (k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5430, c_5539, c_1677, c_11779])).
% 10.61/3.54  tff(c_11805, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11795, c_5430])).
% 10.61/3.54  tff(c_316, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_274])).
% 10.61/3.54  tff(c_612, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_316])).
% 10.61/3.54  tff(c_1321, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_4')=k1_lattices('#skF_3', '#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_1294])).
% 10.61/3.54  tff(c_1341, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_1321])).
% 10.61/3.54  tff(c_1410, plain, (k2_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_6', '#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_48, c_1372])).
% 10.61/3.54  tff(c_1428, plain, (k2_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1410])).
% 10.61/3.54  tff(c_5423, plain, (k4_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_5378])).
% 10.61/3.54  tff(c_5450, plain, (k4_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_5423])).
% 10.61/3.54  tff(c_1594, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_615, c_1565])).
% 10.61/3.54  tff(c_840, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')=k4_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_615, c_811])).
% 10.61/3.54  tff(c_2562, plain, (k4_lattices('#skF_3', '#skF_6', k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1594, c_840])).
% 10.61/3.54  tff(c_5534, plain, (k2_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5450, c_2562])).
% 10.61/3.54  tff(c_5841, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5534, c_1594])).
% 10.61/3.54  tff(c_98, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_6')='#skF_6' | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_88])).
% 10.61/3.54  tff(c_111, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_6')='#skF_6' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_98])).
% 10.61/3.54  tff(c_112, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_6')='#skF_6' | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_111])).
% 10.61/3.54  tff(c_197, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_158, c_147, c_112])).
% 10.61/3.54  tff(c_583, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_6')=k1_lattices('#skF_3', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_556])).
% 10.61/3.54  tff(c_601, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_583])).
% 10.61/3.54  tff(c_1117, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_6', C_101), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', C_101, '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_601, c_1063])).
% 10.61/3.54  tff(c_1166, plain, (![C_101]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_6', C_101), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', C_101, '#skF_6')) | ~m1_subset_1(C_101, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_48, c_48, c_1117])).
% 10.61/3.54  tff(c_5890, plain, (![C_158]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_6', C_158), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', C_158, '#skF_6')) | ~m1_subset_1(C_158, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1166])).
% 10.61/3.54  tff(c_5929, plain, (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_6', '#skF_4'), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_5890])).
% 10.61/3.54  tff(c_5959, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1607, c_612, c_5929])).
% 10.61/3.54  tff(c_6016, plain, (k3_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5841, c_5959])).
% 10.61/3.54  tff(c_1263, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1220])).
% 10.61/3.54  tff(c_681, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_669])).
% 10.61/3.54  tff(c_699, plain, (![B_93]: (k4_lattices('#skF_3', B_93, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_681])).
% 10.61/3.54  tff(c_1168, plain, (![B_103]: (k4_lattices('#skF_3', B_103, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_699])).
% 10.61/3.54  tff(c_1192, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k4_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_1168])).
% 10.61/3.54  tff(c_1213, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k4_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1192])).
% 10.61/3.54  tff(c_1274, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1213])).
% 10.61/3.54  tff(c_1284, plain, (k2_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_1274])).
% 10.61/3.54  tff(c_1285, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1263])).
% 10.61/3.54  tff(c_1541, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1285])).
% 10.61/3.54  tff(c_1679, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1541])).
% 10.61/3.54  tff(c_1078, plain, (![D_102]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k3_lattices('#skF_3', '#skF_6', D_102))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_5', D_102)) | ~m1_subset_1(D_102, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_951, c_1063])).
% 10.61/3.54  tff(c_1127, plain, (![D_102]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k3_lattices('#skF_3', '#skF_6', D_102))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_5', D_102)) | ~m1_subset_1(D_102, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_48, c_50, c_1078])).
% 10.61/3.54  tff(c_12209, plain, (![D_218]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k3_lattices('#skF_3', '#skF_6', D_218))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_5', D_218)) | ~m1_subset_1(D_218, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1127])).
% 10.61/3.54  tff(c_12236, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_5'), k1_lattices('#skF_3', '#skF_4', '#skF_6'))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_612, c_12209])).
% 10.61/3.54  tff(c_12253, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11805, c_6016, c_1679, c_12236])).
% 10.61/3.54  tff(c_12255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_12253])).
% 10.61/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/3.54  
% 10.61/3.54  Inference rules
% 10.61/3.54  ----------------------
% 10.61/3.54  #Ref     : 0
% 10.61/3.54  #Sup     : 2622
% 10.61/3.54  #Fact    : 0
% 10.61/3.54  #Define  : 0
% 10.61/3.54  #Split   : 7
% 10.61/3.54  #Chain   : 0
% 10.61/3.54  #Close   : 0
% 10.61/3.54  
% 10.61/3.54  Ordering : KBO
% 10.61/3.54  
% 10.61/3.54  Simplification rules
% 10.61/3.54  ----------------------
% 10.61/3.54  #Subsume      : 106
% 10.61/3.54  #Demod        : 4434
% 10.61/3.54  #Tautology    : 916
% 10.61/3.54  #SimpNegUnit  : 924
% 10.61/3.54  #BackRed      : 84
% 10.61/3.54  
% 10.61/3.54  #Partial instantiations: 0
% 10.61/3.54  #Strategies tried      : 1
% 10.61/3.54  
% 10.61/3.54  Timing (in seconds)
% 10.61/3.54  ----------------------
% 10.61/3.54  Preprocessing        : 0.36
% 10.61/3.54  Parsing              : 0.19
% 10.61/3.54  CNF conversion       : 0.03
% 10.61/3.54  Main loop            : 2.38
% 10.61/3.54  Inferencing          : 0.57
% 10.61/3.54  Reduction            : 1.00
% 10.61/3.54  Demodulation         : 0.77
% 10.61/3.54  BG Simplification    : 0.08
% 10.61/3.55  Subsumption          : 0.56
% 10.61/3.55  Abstraction          : 0.15
% 10.61/3.55  MUC search           : 0.00
% 10.61/3.55  Cooper               : 0.00
% 10.61/3.55  Total                : 2.81
% 10.61/3.55  Index Insertion      : 0.00
% 10.61/3.55  Index Deletion       : 0.00
% 10.61/3.55  Index Matching       : 0.00
% 10.61/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
