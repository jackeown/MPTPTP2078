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
% DateTime   : Thu Dec  3 10:20:19 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 706 expanded)
%              Number of leaves         :   40 ( 260 expanded)
%              Depth                    :   19
%              Number of atoms          :  375 (2958 expanded)
%              Number of equality atoms :   51 ( 211 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

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

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

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

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
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
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_90,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_135,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_171,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_lattices(A,k3_lattices(A,B,C)) = k4_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_58,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_81,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_lattices(A_59,k2_lattices(A_59,B_60,C_61),C_61) = C_61
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ v8_lattices(A_59)
      | ~ l3_lattices(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ! [B_60] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_60,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_97,plain,(
    ! [B_60] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_60,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89])).

tff(c_98,plain,(
    ! [B_60] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_60,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_97])).

tff(c_103,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_106,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_109,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_109])).

tff(c_113,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_589,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_lattices(A_85,B_86,C_87)
      | k2_lattices(A_85,B_86,C_87) != B_86
      | ~ m1_subset_1(C_87,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l3_lattices(A_85)
      | ~ v9_lattices(A_85)
      | ~ v8_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_597,plain,(
    ! [B_86] :
      ( r1_lattices('#skF_3',B_86,'#skF_5')
      | k2_lattices('#skF_3',B_86,'#skF_5') != B_86
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_589])).

tff(c_605,plain,(
    ! [B_86] :
      ( r1_lattices('#skF_3',B_86,'#skF_5')
      | k2_lattices('#skF_3',B_86,'#skF_5') != B_86
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_54,c_597])).

tff(c_606,plain,(
    ! [B_86] :
      ( r1_lattices('#skF_3',B_86,'#skF_5')
      | k2_lattices('#skF_3',B_86,'#skF_5') != B_86
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_605])).

tff(c_615,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_618,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_615])).

tff(c_621,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_618])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_621])).

tff(c_625,plain,(
    v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_46] :
      ( l1_lattices(A_46)
      | ~ l3_lattices(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_65,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_61])).

tff(c_225,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_lattices(A_67,B_68,C_69) = k2_lattices(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_lattices(A_67)
      | ~ v6_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_233,plain,(
    ! [B_68] :
      ( k4_lattices('#skF_3',B_68,'#skF_5') = k2_lattices('#skF_3',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_225])).

tff(c_241,plain,(
    ! [B_68] :
      ( k4_lattices('#skF_3',B_68,'#skF_5') = k2_lattices('#skF_3',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_233])).

tff(c_242,plain,(
    ! [B_68] :
      ( k4_lattices('#skF_3',B_68,'#skF_5') = k2_lattices('#skF_3',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_241])).

tff(c_251,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_254,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_251])).

tff(c_257,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_257])).

tff(c_261,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_48,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_665,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_lattices(A_89,B_90,C_91)
      | ~ r3_lattices(A_89,B_90,C_91)
      | ~ m1_subset_1(C_91,u1_struct_0(A_89))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l3_lattices(A_89)
      | ~ v9_lattices(A_89)
      | ~ v8_lattices(A_89)
      | ~ v6_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_667,plain,
    ( r1_lattices('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_665])).

tff(c_670,plain,
    ( r1_lattices('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_113,c_625,c_54,c_52,c_50,c_667])).

tff(c_671,plain,(
    r1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_670])).

tff(c_42,plain,(
    ! [A_28,B_32,C_34] :
      ( k2_lattices(A_28,B_32,C_34) = B_32
      | ~ r1_lattices(A_28,B_32,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(B_32,u1_struct_0(A_28))
      | ~ l3_lattices(A_28)
      | ~ v9_lattices(A_28)
      | ~ v8_lattices(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_673,plain,
    ( k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_671,c_42])).

tff(c_676,plain,
    ( k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_625,c_54,c_52,c_50,c_673])).

tff(c_677,plain,(
    k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_676])).

tff(c_136,plain,(
    ! [B_65] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_65,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_168,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_679,plain,(
    k1_lattices('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_168])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [A_47] :
      ( l2_lattices(A_47)
      | ~ l3_lattices(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_114,plain,(
    ! [A_62,B_63,C_64] :
      ( k3_lattices(A_62,B_63,C_64) = k1_lattices(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l2_lattices(A_62)
      | ~ v4_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_122,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_3',B_63,'#skF_5') = k1_lattices('#skF_3',B_63,'#skF_5')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_114])).

tff(c_130,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_3',B_63,'#skF_5') = k1_lattices('#skF_3',B_63,'#skF_5')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_122])).

tff(c_131,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_3',B_63,'#skF_5') = k1_lattices('#skF_3',B_63,'#skF_5')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_130])).

tff(c_177,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_180,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_177])).

tff(c_183,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_180])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_183])).

tff(c_188,plain,(
    ! [B_66] :
      ( k3_lattices('#skF_3',B_66,'#skF_5') = k1_lattices('#skF_3',B_66,'#skF_5')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_220,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_188])).

tff(c_187,plain,(
    v4_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_301,plain,(
    ! [A_71,C_72,B_73] :
      ( k3_lattices(A_71,C_72,B_73) = k3_lattices(A_71,B_73,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(A_71))
      | ~ m1_subset_1(B_73,u1_struct_0(A_71))
      | ~ l2_lattices(A_71)
      | ~ v4_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,(
    ! [B_73] :
      ( k3_lattices('#skF_3',B_73,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_73)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_301])).

tff(c_317,plain,(
    ! [B_73] :
      ( k3_lattices('#skF_3',B_73,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_73)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_70,c_309])).

tff(c_372,plain,(
    ! [B_75] :
      ( k3_lattices('#skF_3',B_75,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_75)
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_317])).

tff(c_390,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_372])).

tff(c_406,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_390])).

tff(c_691,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_406])).

tff(c_56,plain,(
    v17_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k7_lattices(A_16,B_17),u1_struct_0(A_16))
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_710,plain,(
    ! [A_92,B_93,C_94] :
      ( r3_lattices(A_92,B_93,C_94)
      | ~ r1_lattices(A_92,B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l3_lattices(A_92)
      | ~ v9_lattices(A_92)
      | ~ v8_lattices(A_92)
      | ~ v6_lattices(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1749,plain,(
    ! [A_168,B_169,B_170] :
      ( r3_lattices(A_168,B_169,k7_lattices(A_168,B_170))
      | ~ r1_lattices(A_168,B_169,k7_lattices(A_168,B_170))
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ v9_lattices(A_168)
      | ~ v8_lattices(A_168)
      | ~ v6_lattices(A_168)
      | ~ m1_subset_1(B_170,u1_struct_0(A_168))
      | ~ l3_lattices(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_26,c_710])).

tff(c_46,plain,(
    ~ r3_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1754,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1749,c_46])).

tff(c_1758,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_261,c_113,c_625,c_1754])).

tff(c_1759,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1758])).

tff(c_1760,plain,(
    ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_1763,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1760])).

tff(c_1766,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1763])).

tff(c_1768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1766])).

tff(c_1770,plain,(
    m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_236,plain,(
    ! [A_16,B_68,B_17] :
      ( k4_lattices(A_16,B_68,k7_lattices(A_16,B_17)) = k2_lattices(A_16,B_68,k7_lattices(A_16,B_17))
      | ~ m1_subset_1(B_68,u1_struct_0(A_16))
      | ~ l1_lattices(A_16)
      | ~ v6_lattices(A_16)
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_225])).

tff(c_1778,plain,(
    ! [B_17] :
      ( k4_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_17)) = k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_17))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1770,c_236])).

tff(c_1871,plain,(
    ! [B_17] :
      ( k4_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_17)) = k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_17))
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_261,c_65,c_1778])).

tff(c_2568,plain,(
    ! [B_187] :
      ( k4_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_187)) = k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_187))
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1871])).

tff(c_44,plain,(
    ! [A_35,B_39,C_41] :
      ( k4_lattices(A_35,k7_lattices(A_35,B_39),k7_lattices(A_35,C_41)) = k7_lattices(A_35,k3_lattices(A_35,B_39,C_41))
      | ~ m1_subset_1(C_41,u1_struct_0(A_35))
      | ~ m1_subset_1(B_39,u1_struct_0(A_35))
      | ~ l3_lattices(A_35)
      | ~ v17_lattices(A_35)
      | ~ v10_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2577,plain,(
    ! [B_187] :
      ( k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_187)) = k7_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',B_187))
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v17_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2568,c_44])).

tff(c_2592,plain,(
    ! [B_187] :
      ( k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_187)) = k7_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',B_187))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_2577])).

tff(c_2617,plain,(
    ! [B_190] :
      ( k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3',B_190)) = k7_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',B_190))
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2592])).

tff(c_600,plain,(
    ! [A_16,B_86,B_17] :
      ( r1_lattices(A_16,B_86,k7_lattices(A_16,B_17))
      | k2_lattices(A_16,B_86,k7_lattices(A_16,B_17)) != B_86
      | ~ m1_subset_1(B_86,u1_struct_0(A_16))
      | ~ v9_lattices(A_16)
      | ~ v8_lattices(A_16)
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_589])).

tff(c_1769,plain,(
    ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_1964,plain,
    ( k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) != k7_lattices('#skF_3','#skF_5')
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_600,c_1769])).

tff(c_1967,plain,
    ( k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) != k7_lattices('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_113,c_625,c_1770,c_1964])).

tff(c_1968,plain,(
    k2_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) != k7_lattices('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1967])).

tff(c_2630,plain,
    ( k7_lattices('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_4')) != k7_lattices('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2617,c_1968])).

tff(c_2647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_691,c_2630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.03  
% 5.16/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.03  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 5.16/2.03  
% 5.16/2.03  %Foreground sorts:
% 5.16/2.03  
% 5.16/2.03  
% 5.16/2.03  %Background operators:
% 5.16/2.03  
% 5.16/2.03  
% 5.16/2.03  %Foreground operators:
% 5.16/2.03  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.16/2.03  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 5.16/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.16/2.03  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 5.16/2.03  tff(l2_lattices, type, l2_lattices: $i > $o).
% 5.16/2.03  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.16/2.03  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.03  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 5.16/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.16/2.03  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 5.16/2.03  tff(l1_lattices, type, l1_lattices: $i > $o).
% 5.16/2.03  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.16/2.03  tff(v17_lattices, type, v17_lattices: $i > $o).
% 5.16/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.16/2.03  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.16/2.03  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.16/2.03  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.16/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.16/2.03  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.16/2.03  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.16/2.03  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.03  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 5.16/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.16/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/2.03  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.16/2.03  
% 5.45/2.05  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 5.45/2.05  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.45/2.05  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 5.45/2.05  tff(f_154, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 5.45/2.05  tff(f_90, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 5.45/2.05  tff(f_116, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 5.45/2.05  tff(f_135, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.45/2.05  tff(f_103, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 5.45/2.05  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 5.45/2.05  tff(f_84, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 5.45/2.05  tff(f_171, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 5.45/2.05  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_54, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_58, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.45/2.05  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_81, plain, (![A_59, B_60, C_61]: (k1_lattices(A_59, k2_lattices(A_59, B_60, C_61), C_61)=C_61 | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~v8_lattices(A_59) | ~l3_lattices(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.45/2.05  tff(c_89, plain, (![B_60]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_60, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_60, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_81])).
% 5.45/2.05  tff(c_97, plain, (![B_60]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_60, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_60, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89])).
% 5.45/2.05  tff(c_98, plain, (![B_60]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_60, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_60, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_97])).
% 5.45/2.05  tff(c_103, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_98])).
% 5.45/2.05  tff(c_106, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_103])).
% 5.45/2.05  tff(c_109, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_106])).
% 5.45/2.05  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_109])).
% 5.45/2.05  tff(c_113, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 5.45/2.05  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.45/2.05  tff(c_589, plain, (![A_85, B_86, C_87]: (r1_lattices(A_85, B_86, C_87) | k2_lattices(A_85, B_86, C_87)!=B_86 | ~m1_subset_1(C_87, u1_struct_0(A_85)) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l3_lattices(A_85) | ~v9_lattices(A_85) | ~v8_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.05  tff(c_597, plain, (![B_86]: (r1_lattices('#skF_3', B_86, '#skF_5') | k2_lattices('#skF_3', B_86, '#skF_5')!=B_86 | ~m1_subset_1(B_86, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_589])).
% 5.45/2.05  tff(c_605, plain, (![B_86]: (r1_lattices('#skF_3', B_86, '#skF_5') | k2_lattices('#skF_3', B_86, '#skF_5')!=B_86 | ~m1_subset_1(B_86, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_54, c_597])).
% 5.45/2.05  tff(c_606, plain, (![B_86]: (r1_lattices('#skF_3', B_86, '#skF_5') | k2_lattices('#skF_3', B_86, '#skF_5')!=B_86 | ~m1_subset_1(B_86, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_605])).
% 5.45/2.05  tff(c_615, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_606])).
% 5.45/2.05  tff(c_618, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_615])).
% 5.45/2.05  tff(c_621, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_618])).
% 5.45/2.05  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_621])).
% 5.45/2.05  tff(c_625, plain, (v9_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_606])).
% 5.45/2.05  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.45/2.05  tff(c_61, plain, (![A_46]: (l1_lattices(A_46) | ~l3_lattices(A_46))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.45/2.05  tff(c_65, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_54, c_61])).
% 5.45/2.05  tff(c_225, plain, (![A_67, B_68, C_69]: (k4_lattices(A_67, B_68, C_69)=k2_lattices(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_lattices(A_67) | ~v6_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.45/2.05  tff(c_233, plain, (![B_68]: (k4_lattices('#skF_3', B_68, '#skF_5')=k2_lattices('#skF_3', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_225])).
% 5.45/2.05  tff(c_241, plain, (![B_68]: (k4_lattices('#skF_3', B_68, '#skF_5')=k2_lattices('#skF_3', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_233])).
% 5.45/2.05  tff(c_242, plain, (![B_68]: (k4_lattices('#skF_3', B_68, '#skF_5')=k2_lattices('#skF_3', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_241])).
% 5.45/2.05  tff(c_251, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_242])).
% 5.45/2.05  tff(c_254, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_251])).
% 5.45/2.05  tff(c_257, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_254])).
% 5.45/2.05  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_257])).
% 5.45/2.05  tff(c_261, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_242])).
% 5.45/2.05  tff(c_48, plain, (r3_lattices('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_665, plain, (![A_89, B_90, C_91]: (r1_lattices(A_89, B_90, C_91) | ~r3_lattices(A_89, B_90, C_91) | ~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l3_lattices(A_89) | ~v9_lattices(A_89) | ~v8_lattices(A_89) | ~v6_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.45/2.05  tff(c_667, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_665])).
% 5.45/2.05  tff(c_670, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_113, c_625, c_54, c_52, c_50, c_667])).
% 5.45/2.05  tff(c_671, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_670])).
% 5.45/2.05  tff(c_42, plain, (![A_28, B_32, C_34]: (k2_lattices(A_28, B_32, C_34)=B_32 | ~r1_lattices(A_28, B_32, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(B_32, u1_struct_0(A_28)) | ~l3_lattices(A_28) | ~v9_lattices(A_28) | ~v8_lattices(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.45/2.05  tff(c_673, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_671, c_42])).
% 5.45/2.05  tff(c_676, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_625, c_54, c_52, c_50, c_673])).
% 5.45/2.05  tff(c_677, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_676])).
% 5.45/2.05  tff(c_136, plain, (![B_65]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_65, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_98])).
% 5.45/2.05  tff(c_168, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_52, c_136])).
% 5.45/2.05  tff(c_679, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_168])).
% 5.45/2.05  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.45/2.05  tff(c_66, plain, (![A_47]: (l2_lattices(A_47) | ~l3_lattices(A_47))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.45/2.05  tff(c_70, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_54, c_66])).
% 5.45/2.05  tff(c_114, plain, (![A_62, B_63, C_64]: (k3_lattices(A_62, B_63, C_64)=k1_lattices(A_62, B_63, C_64) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l2_lattices(A_62) | ~v4_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.45/2.05  tff(c_122, plain, (![B_63]: (k3_lattices('#skF_3', B_63, '#skF_5')=k1_lattices('#skF_3', B_63, '#skF_5') | ~m1_subset_1(B_63, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_114])).
% 5.45/2.05  tff(c_130, plain, (![B_63]: (k3_lattices('#skF_3', B_63, '#skF_5')=k1_lattices('#skF_3', B_63, '#skF_5') | ~m1_subset_1(B_63, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_122])).
% 5.45/2.05  tff(c_131, plain, (![B_63]: (k3_lattices('#skF_3', B_63, '#skF_5')=k1_lattices('#skF_3', B_63, '#skF_5') | ~m1_subset_1(B_63, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_130])).
% 5.45/2.05  tff(c_177, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_131])).
% 5.45/2.05  tff(c_180, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_177])).
% 5.45/2.05  tff(c_183, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_180])).
% 5.45/2.05  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_183])).
% 5.45/2.05  tff(c_188, plain, (![B_66]: (k3_lattices('#skF_3', B_66, '#skF_5')=k1_lattices('#skF_3', B_66, '#skF_5') | ~m1_subset_1(B_66, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_131])).
% 5.45/2.05  tff(c_220, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_188])).
% 5.45/2.05  tff(c_187, plain, (v4_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_131])).
% 5.45/2.05  tff(c_301, plain, (![A_71, C_72, B_73]: (k3_lattices(A_71, C_72, B_73)=k3_lattices(A_71, B_73, C_72) | ~m1_subset_1(C_72, u1_struct_0(A_71)) | ~m1_subset_1(B_73, u1_struct_0(A_71)) | ~l2_lattices(A_71) | ~v4_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.45/2.05  tff(c_309, plain, (![B_73]: (k3_lattices('#skF_3', B_73, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_73) | ~m1_subset_1(B_73, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_301])).
% 5.45/2.05  tff(c_317, plain, (![B_73]: (k3_lattices('#skF_3', B_73, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_73) | ~m1_subset_1(B_73, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_70, c_309])).
% 5.45/2.05  tff(c_372, plain, (![B_75]: (k3_lattices('#skF_3', B_75, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_75) | ~m1_subset_1(B_75, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_317])).
% 5.45/2.05  tff(c_390, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_372])).
% 5.45/2.05  tff(c_406, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_390])).
% 5.45/2.05  tff(c_691, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_679, c_406])).
% 5.45/2.05  tff(c_56, plain, (v17_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(k7_lattices(A_16, B_17), u1_struct_0(A_16)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.45/2.05  tff(c_710, plain, (![A_92, B_93, C_94]: (r3_lattices(A_92, B_93, C_94) | ~r1_lattices(A_92, B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0(A_92)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l3_lattices(A_92) | ~v9_lattices(A_92) | ~v8_lattices(A_92) | ~v6_lattices(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.45/2.05  tff(c_1749, plain, (![A_168, B_169, B_170]: (r3_lattices(A_168, B_169, k7_lattices(A_168, B_170)) | ~r1_lattices(A_168, B_169, k7_lattices(A_168, B_170)) | ~m1_subset_1(B_169, u1_struct_0(A_168)) | ~v9_lattices(A_168) | ~v8_lattices(A_168) | ~v6_lattices(A_168) | ~m1_subset_1(B_170, u1_struct_0(A_168)) | ~l3_lattices(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_26, c_710])).
% 5.45/2.05  tff(c_46, plain, (~r3_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.45/2.05  tff(c_1754, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1749, c_46])).
% 5.45/2.05  tff(c_1758, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_261, c_113, c_625, c_1754])).
% 5.45/2.05  tff(c_1759, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1758])).
% 5.45/2.05  tff(c_1760, plain, (~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1759])).
% 5.45/2.05  tff(c_1763, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1760])).
% 5.45/2.05  tff(c_1766, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1763])).
% 5.45/2.05  tff(c_1768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1766])).
% 5.45/2.05  tff(c_1770, plain, (m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1759])).
% 5.45/2.05  tff(c_236, plain, (![A_16, B_68, B_17]: (k4_lattices(A_16, B_68, k7_lattices(A_16, B_17))=k2_lattices(A_16, B_68, k7_lattices(A_16, B_17)) | ~m1_subset_1(B_68, u1_struct_0(A_16)) | ~l1_lattices(A_16) | ~v6_lattices(A_16) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_26, c_225])).
% 5.45/2.05  tff(c_1778, plain, (![B_17]: (k4_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_17))=k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_17)) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~m1_subset_1(B_17, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1770, c_236])).
% 5.45/2.05  tff(c_1871, plain, (![B_17]: (k4_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_17))=k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_17)) | ~m1_subset_1(B_17, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_261, c_65, c_1778])).
% 5.45/2.05  tff(c_2568, plain, (![B_187]: (k4_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_187))=k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_187)) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1871])).
% 5.45/2.05  tff(c_44, plain, (![A_35, B_39, C_41]: (k4_lattices(A_35, k7_lattices(A_35, B_39), k7_lattices(A_35, C_41))=k7_lattices(A_35, k3_lattices(A_35, B_39, C_41)) | ~m1_subset_1(C_41, u1_struct_0(A_35)) | ~m1_subset_1(B_39, u1_struct_0(A_35)) | ~l3_lattices(A_35) | ~v17_lattices(A_35) | ~v10_lattices(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.45/2.05  tff(c_2577, plain, (![B_187]: (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_187))=k7_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', B_187)) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v17_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_187, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2568, c_44])).
% 5.45/2.05  tff(c_2592, plain, (![B_187]: (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_187))=k7_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', B_187)) | v2_struct_0('#skF_3') | ~m1_subset_1(B_187, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_2577])).
% 5.45/2.05  tff(c_2617, plain, (![B_190]: (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', B_190))=k7_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', B_190)) | ~m1_subset_1(B_190, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2592])).
% 5.45/2.05  tff(c_600, plain, (![A_16, B_86, B_17]: (r1_lattices(A_16, B_86, k7_lattices(A_16, B_17)) | k2_lattices(A_16, B_86, k7_lattices(A_16, B_17))!=B_86 | ~m1_subset_1(B_86, u1_struct_0(A_16)) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_26, c_589])).
% 5.45/2.05  tff(c_1769, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1759])).
% 5.45/2.05  tff(c_1964, plain, (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))!=k7_lattices('#skF_3', '#skF_5') | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_600, c_1769])).
% 5.45/2.05  tff(c_1967, plain, (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))!=k7_lattices('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_113, c_625, c_1770, c_1964])).
% 5.45/2.05  tff(c_1968, plain, (k2_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))!=k7_lattices('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_1967])).
% 5.45/2.05  tff(c_2630, plain, (k7_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', '#skF_4'))!=k7_lattices('#skF_3', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2617, c_1968])).
% 5.45/2.05  tff(c_2647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_691, c_2630])).
% 5.45/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.05  
% 5.45/2.05  Inference rules
% 5.45/2.05  ----------------------
% 5.45/2.05  #Ref     : 0
% 5.45/2.05  #Sup     : 546
% 5.45/2.05  #Fact    : 0
% 5.45/2.05  #Define  : 0
% 5.45/2.05  #Split   : 13
% 5.45/2.05  #Chain   : 0
% 5.45/2.05  #Close   : 0
% 5.45/2.05  
% 5.45/2.05  Ordering : KBO
% 5.45/2.05  
% 5.45/2.05  Simplification rules
% 5.45/2.05  ----------------------
% 5.45/2.05  #Subsume      : 7
% 5.45/2.05  #Demod        : 511
% 5.45/2.05  #Tautology    : 368
% 5.45/2.05  #SimpNegUnit  : 148
% 5.45/2.05  #BackRed      : 18
% 5.45/2.05  
% 5.45/2.05  #Partial instantiations: 0
% 5.45/2.05  #Strategies tried      : 1
% 5.45/2.05  
% 5.45/2.05  Timing (in seconds)
% 5.45/2.05  ----------------------
% 5.45/2.06  Preprocessing        : 0.37
% 5.45/2.06  Parsing              : 0.20
% 5.45/2.06  CNF conversion       : 0.03
% 5.45/2.06  Main loop            : 0.85
% 5.45/2.06  Inferencing          : 0.31
% 5.45/2.06  Reduction            : 0.28
% 5.45/2.06  Demodulation         : 0.19
% 5.45/2.06  BG Simplification    : 0.04
% 5.45/2.06  Subsumption          : 0.17
% 5.45/2.06  Abstraction          : 0.05
% 5.45/2.06  MUC search           : 0.00
% 5.45/2.06  Cooper               : 0.00
% 5.45/2.06  Total                : 1.27
% 5.45/2.06  Index Insertion      : 0.00
% 5.45/2.06  Index Deletion       : 0.00
% 5.45/2.06  Index Matching       : 0.00
% 5.45/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
