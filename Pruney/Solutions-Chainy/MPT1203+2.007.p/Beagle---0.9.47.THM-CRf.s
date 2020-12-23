%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:14 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  178 (1265 expanded)
%              Number of leaves         :   39 ( 445 expanded)
%              Depth                    :   19
%              Number of atoms          :  414 (5751 expanded)
%              Number of equality atoms :  110 (1373 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

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

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_166,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

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

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

tff(f_99,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v11_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k2_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k2_lattices(A,B,C),k2_lattices(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_60,plain,(
    v11_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [A_77,B_78] :
      ( k4_lattices(A_77,B_78,B_78) = B_78
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l3_lattices(A_77)
      | ~ v9_lattices(A_77)
      | ~ v8_lattices(A_77)
      | ~ v6_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_107,plain,
    ( k4_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8'
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_95])).

tff(c_119,plain,
    ( k4_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_107])).

tff(c_120,plain,
    ( k4_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_119])).

tff(c_129,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_132,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_135])).

tff(c_139,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_70,plain,(
    ! [A_64] :
      ( l1_lattices(A_64)
      | ~ l3_lattices(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_74,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_221,plain,(
    ! [A_82,B_83,C_84] :
      ( k4_lattices(A_82,B_83,C_84) = k2_lattices(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_lattices(A_82)
      | ~ v6_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_233,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_8') = k2_lattices('#skF_6',B_83,'#skF_8')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_221])).

tff(c_245,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_8') = k2_lattices('#skF_6',B_83,'#skF_8')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_233])).

tff(c_255,plain,(
    ! [B_85] :
      ( k4_lattices('#skF_6',B_85,'#skF_8') = k2_lattices('#skF_6',B_85,'#skF_8')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_245])).

tff(c_308,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_8') = k2_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_255])).

tff(c_237,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_7') = k2_lattices('#skF_6',B_83,'#skF_7')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_221])).

tff(c_253,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_7') = k2_lattices('#skF_6',B_83,'#skF_7')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_237])).

tff(c_427,plain,(
    ! [B_90] :
      ( k4_lattices('#skF_6',B_90,'#skF_7') = k2_lattices('#skF_6',B_90,'#skF_7')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_253])).

tff(c_477,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_7') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_427])).

tff(c_737,plain,(
    ! [A_97,C_98,B_99] :
      ( k4_lattices(A_97,C_98,B_99) = k4_lattices(A_97,B_99,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_97))
      | ~ m1_subset_1(B_99,u1_struct_0(A_97))
      | ~ l1_lattices(A_97)
      | ~ v6_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_749,plain,(
    ! [B_99] :
      ( k4_lattices('#skF_6',B_99,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_737])).

tff(c_761,plain,(
    ! [B_99] :
      ( k4_lattices('#skF_6',B_99,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_749])).

tff(c_837,plain,(
    ! [B_101] :
      ( k4_lattices('#skF_6',B_101,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_101)
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_761])).

tff(c_866,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_8') = k4_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_837])).

tff(c_892,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_8') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_477,c_866])).

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

tff(c_111,plain,
    ( k4_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_127,plain,
    ( k4_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_111])).

tff(c_128,plain,
    ( k4_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_127])).

tff(c_140,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_140])).

tff(c_143,plain,
    ( ~ v8_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | k4_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_146,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_183,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_186,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_183])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_186])).

tff(c_189,plain,
    ( ~ v8_lattices('#skF_6')
    | k4_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_191,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_197,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_191])).

tff(c_200,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_200])).

tff(c_204,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_393,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_lattices(A_87,k2_lattices(A_87,B_88,C_89),C_89) = C_89
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ v8_lattices(A_87)
      | ~ l3_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_405,plain,(
    ! [B_88] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_88,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_393])).

tff(c_417,plain,(
    ! [B_88] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_88,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_204,c_405])).

tff(c_493,plain,(
    ! [B_91] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_91,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_417])).

tff(c_546,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_56,c_493])).

tff(c_900,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_546])).

tff(c_190,plain,(
    v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_138,plain,
    ( ~ v8_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | k4_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_210,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_204,c_138])).

tff(c_278,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_8') = k2_lattices('#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_255])).

tff(c_306,plain,(
    k2_lattices('#skF_6','#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_278])).

tff(c_1001,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k1_lattices(A_104,k2_lattices(A_104,B_105,C_106),k2_lattices(A_104,B_105,D_107)) = k2_lattices(A_104,B_105,k1_lattices(A_104,C_106,D_107))
      | ~ m1_subset_1(D_107,u1_struct_0(A_104))
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ v11_lattices(A_104)
      | ~ l3_lattices(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1053,plain,(
    ! [C_106] :
      ( k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6',C_106,'#skF_8')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8',C_106),'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ v11_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1001])).

tff(c_1097,plain,(
    ! [C_106] :
      ( k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6',C_106,'#skF_8')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8',C_106),'#skF_8')
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_54,c_54,c_1053])).

tff(c_1407,plain,(
    ! [C_113] :
      ( k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6',C_113,'#skF_8')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8',C_113),'#skF_8')
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1097])).

tff(c_1436,plain,(
    k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6','#skF_7','#skF_8')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_1407])).

tff(c_1462,plain,(
    k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6','#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_1436])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_63] :
      ( l2_lattices(A_63)
      | ~ l3_lattices(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_69,plain,(
    l2_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_613,plain,(
    ! [A_93,B_94,C_95] :
      ( k3_lattices(A_93,B_94,C_95) = k1_lattices(A_93,B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l2_lattices(A_93)
      | ~ v4_lattices(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_629,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_7') = k1_lattices('#skF_6',B_94,'#skF_7')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_613])).

tff(c_645,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_7') = k1_lattices('#skF_6',B_94,'#skF_7')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_629])).

tff(c_646,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_7') = k1_lattices('#skF_6',B_94,'#skF_7')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_645])).

tff(c_726,plain,(
    ~ v4_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_729,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_726])).

tff(c_732,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_729])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_732])).

tff(c_736,plain,(
    v4_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_625,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_8') = k1_lattices('#skF_6',B_94,'#skF_8')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_613])).

tff(c_637,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_8') = k1_lattices('#skF_6',B_94,'#skF_8')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_625])).

tff(c_638,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_8') = k1_lattices('#skF_6',B_94,'#skF_8')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_637])).

tff(c_1234,plain,(
    ! [B_110] :
      ( k3_lattices('#skF_6',B_110,'#skF_8') = k1_lattices('#skF_6',B_110,'#skF_8')
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_638])).

tff(c_1287,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_8') = k1_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_1234])).

tff(c_627,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_9') = k1_lattices('#skF_6',B_94,'#skF_9')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_613])).

tff(c_641,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_9') = k1_lattices('#skF_6',B_94,'#skF_9')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_627])).

tff(c_642,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_6',B_94,'#skF_9') = k1_lattices('#skF_6',B_94,'#skF_9')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_641])).

tff(c_1161,plain,(
    ! [B_109] :
      ( k3_lattices('#skF_6',B_109,'#skF_9') = k1_lattices('#skF_6',B_109,'#skF_9')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_642])).

tff(c_1214,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_1161])).

tff(c_48,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k3_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1223,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_8') = k1_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_48])).

tff(c_1305,plain,(
    k1_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1223])).

tff(c_50,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k4_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_317,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_50])).

tff(c_235,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_9') = k2_lattices('#skF_6',B_83,'#skF_9')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_221])).

tff(c_249,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_6',B_83,'#skF_9') = k2_lattices('#skF_6',B_83,'#skF_9')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_235])).

tff(c_326,plain,(
    ! [B_86] :
      ( k4_lattices('#skF_6',B_86,'#skF_9') = k2_lattices('#skF_6',B_86,'#skF_9')
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_249])).

tff(c_355,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_326])).

tff(c_380,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_355])).

tff(c_407,plain,(
    ! [B_88] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_88,'#skF_9'),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_393])).

tff(c_421,plain,(
    ! [B_88] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_88,'#skF_9'),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_204,c_407])).

tff(c_659,plain,(
    ! [B_96] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_96,'#skF_9'),'#skF_9') = '#skF_9'
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_421])).

tff(c_688,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_56,c_659])).

tff(c_713,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_8'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_688])).

tff(c_899,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_713])).

tff(c_902,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_317])).

tff(c_478,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_7') = k2_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_427])).

tff(c_751,plain,(
    ! [B_99] :
      ( k4_lattices('#skF_6',B_99,'#skF_9') = k4_lattices('#skF_6','#skF_9',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_737])).

tff(c_765,plain,(
    ! [B_99] :
      ( k4_lattices('#skF_6',B_99,'#skF_9') = k4_lattices('#skF_6','#skF_9',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_74,c_751])).

tff(c_925,plain,(
    ! [B_103] :
      ( k4_lattices('#skF_6',B_103,'#skF_9') = k4_lattices('#skF_6','#skF_9',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_765])).

tff(c_954,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k4_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_925])).

tff(c_980,plain,(
    k2_lattices('#skF_6','#skF_9','#skF_7') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_478,c_954])).

tff(c_109,plain,
    ( k4_lattices('#skF_6','#skF_9','#skF_9') = '#skF_9'
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_123,plain,
    ( k4_lattices('#skF_6','#skF_9','#skF_9') = '#skF_9'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109])).

tff(c_124,plain,
    ( k4_lattices('#skF_6','#skF_9','#skF_9') = '#skF_9'
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_123])).

tff(c_216,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_204,c_190,c_124])).

tff(c_352,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_9') = k2_lattices('#skF_6','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_326])).

tff(c_378,plain,(
    k2_lattices('#skF_6','#skF_9','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_352])).

tff(c_1047,plain,(
    ! [C_106] :
      ( k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_106,'#skF_9')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_106),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ v11_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_1001])).

tff(c_1091,plain,(
    ! [C_106] :
      ( k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_106,'#skF_9')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_106),'#skF_9')
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_52,c_52,c_1047])).

tff(c_1315,plain,(
    ! [C_112] :
      ( k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_112,'#skF_9')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_112),'#skF_9')
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1091])).

tff(c_1344,plain,(
    k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7','#skF_9')) = k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9','#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_1315])).

tff(c_1370,plain,(
    k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_899,c_980,c_1344])).

tff(c_307,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_8') = k2_lattices('#skF_6','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_255])).

tff(c_376,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_9') = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_326])).

tff(c_863,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_8') = k4_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_837])).

tff(c_890,plain,(
    k2_lattices('#skF_6','#skF_9','#skF_8') = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_376,c_863])).

tff(c_1014,plain,(
    ! [D_107] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_9',D_107)) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7',D_107))
      | ~ m1_subset_1(D_107,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ v11_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_1001])).

tff(c_1058,plain,(
    ! [D_107] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_9',D_107)) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7',D_107))
      | ~ m1_subset_1(D_107,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_52,c_56,c_1014])).

tff(c_1848,plain,(
    ! [D_120] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_9',D_120)) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7',D_120))
      | ~ m1_subset_1(D_120,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1058])).

tff(c_1872,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_1848])).

tff(c_1883,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1370,c_1872])).

tff(c_18,plain,(
    ! [A_5,B_20,C_24,D_26] :
      ( k1_lattices(A_5,k2_lattices(A_5,B_20,C_24),k2_lattices(A_5,B_20,D_26)) = k2_lattices(A_5,B_20,k1_lattices(A_5,C_24,D_26))
      | ~ m1_subset_1(D_26,u1_struct_0(A_5))
      | ~ m1_subset_1(C_24,u1_struct_0(A_5))
      | ~ m1_subset_1(B_20,u1_struct_0(A_5))
      | ~ v11_lattices(A_5)
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1889,plain,
    ( k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6','#skF_7','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v11_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_18])).

tff(c_1896,plain,
    ( '#skF_9' = '#skF_8'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_54,c_56,c_52,c_1462,c_1305,c_1889])).

tff(c_1898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_1896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:03:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.80  
% 4.20/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.80  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 4.20/1.80  
% 4.20/1.80  %Foreground sorts:
% 4.20/1.80  
% 4.20/1.80  
% 4.20/1.80  %Background operators:
% 4.20/1.80  
% 4.20/1.80  
% 4.20/1.80  %Foreground operators:
% 4.20/1.80  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.20/1.80  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 4.20/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.20/1.80  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 4.20/1.80  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.20/1.80  tff(l2_lattices, type, l2_lattices: $i > $o).
% 4.20/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.20/1.80  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.20/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.80  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 4.20/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.20/1.80  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 4.20/1.80  tff(l1_lattices, type, l1_lattices: $i > $o).
% 4.20/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.80  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.20/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.80  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.20/1.80  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.20/1.80  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.20/1.80  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.20/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.20/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.80  tff(v11_lattices, type, v11_lattices: $i > $o).
% 4.20/1.80  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.20/1.80  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.20/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.80  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.20/1.80  
% 4.20/1.83  tff(f_166, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_lattices)).
% 4.20/1.83  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 4.20/1.83  tff(f_141, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattices)).
% 4.20/1.83  tff(f_99, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 4.20/1.83  tff(f_125, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 4.20/1.83  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 4.20/1.83  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 4.20/1.83  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v11_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k2_lattices(A, B, C), k2_lattices(A, B, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_lattices)).
% 4.20/1.83  tff(f_112, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 4.20/1.83  tff(c_64, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_46, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_58, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_60, plain, (v11_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_54, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_52, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_62, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.20/1.83  tff(c_95, plain, (![A_77, B_78]: (k4_lattices(A_77, B_78, B_78)=B_78 | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l3_lattices(A_77) | ~v9_lattices(A_77) | ~v8_lattices(A_77) | ~v6_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.20/1.83  tff(c_107, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8' | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_95])).
% 4.20/1.83  tff(c_119, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_107])).
% 4.20/1.83  tff(c_120, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_119])).
% 4.20/1.83  tff(c_129, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_120])).
% 4.20/1.83  tff(c_132, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_129])).
% 4.20/1.83  tff(c_135, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_132])).
% 4.20/1.83  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_135])).
% 4.20/1.83  tff(c_139, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 4.20/1.83  tff(c_70, plain, (![A_64]: (l1_lattices(A_64) | ~l3_lattices(A_64))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.20/1.83  tff(c_74, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_58, c_70])).
% 4.20/1.83  tff(c_221, plain, (![A_82, B_83, C_84]: (k4_lattices(A_82, B_83, C_84)=k2_lattices(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_lattices(A_82) | ~v6_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.20/1.83  tff(c_233, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_8')=k2_lattices('#skF_6', B_83, '#skF_8') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_221])).
% 4.20/1.83  tff(c_245, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_8')=k2_lattices('#skF_6', B_83, '#skF_8') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_233])).
% 4.20/1.83  tff(c_255, plain, (![B_85]: (k4_lattices('#skF_6', B_85, '#skF_8')=k2_lattices('#skF_6', B_85, '#skF_8') | ~m1_subset_1(B_85, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_245])).
% 4.20/1.83  tff(c_308, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_8')=k2_lattices('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_255])).
% 4.20/1.83  tff(c_237, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_7')=k2_lattices('#skF_6', B_83, '#skF_7') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_221])).
% 4.20/1.83  tff(c_253, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_7')=k2_lattices('#skF_6', B_83, '#skF_7') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_237])).
% 4.20/1.83  tff(c_427, plain, (![B_90]: (k4_lattices('#skF_6', B_90, '#skF_7')=k2_lattices('#skF_6', B_90, '#skF_7') | ~m1_subset_1(B_90, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_253])).
% 4.20/1.83  tff(c_477, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_7')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_427])).
% 4.20/1.83  tff(c_737, plain, (![A_97, C_98, B_99]: (k4_lattices(A_97, C_98, B_99)=k4_lattices(A_97, B_99, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_97)) | ~m1_subset_1(B_99, u1_struct_0(A_97)) | ~l1_lattices(A_97) | ~v6_lattices(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.83  tff(c_749, plain, (![B_99]: (k4_lattices('#skF_6', B_99, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_737])).
% 4.20/1.83  tff(c_761, plain, (![B_99]: (k4_lattices('#skF_6', B_99, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_749])).
% 4.20/1.83  tff(c_837, plain, (![B_101]: (k4_lattices('#skF_6', B_101, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_101) | ~m1_subset_1(B_101, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_761])).
% 4.20/1.83  tff(c_866, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_8')=k4_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_837])).
% 4.20/1.83  tff(c_892, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_8')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_477, c_866])).
% 4.20/1.83  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.20/1.83  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.20/1.83  tff(c_111, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_95])).
% 4.20/1.83  tff(c_127, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_111])).
% 4.20/1.83  tff(c_128, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_127])).
% 4.20/1.83  tff(c_140, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_128])).
% 4.20/1.83  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_140])).
% 4.20/1.83  tff(c_143, plain, (~v8_lattices('#skF_6') | ~v9_lattices('#skF_6') | k4_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_128])).
% 4.20/1.83  tff(c_146, plain, (~v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_143])).
% 4.20/1.83  tff(c_183, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_2, c_146])).
% 4.20/1.83  tff(c_186, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_183])).
% 4.20/1.83  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_186])).
% 4.20/1.83  tff(c_189, plain, (~v8_lattices('#skF_6') | k4_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_143])).
% 4.20/1.83  tff(c_191, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_189])).
% 4.20/1.83  tff(c_197, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_4, c_191])).
% 4.20/1.83  tff(c_200, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_197])).
% 4.20/1.83  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_200])).
% 4.20/1.83  tff(c_204, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_189])).
% 4.20/1.83  tff(c_393, plain, (![A_87, B_88, C_89]: (k1_lattices(A_87, k2_lattices(A_87, B_88, C_89), C_89)=C_89 | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~v8_lattices(A_87) | ~l3_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.20/1.83  tff(c_405, plain, (![B_88]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_88, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_88, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_393])).
% 4.20/1.83  tff(c_417, plain, (![B_88]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_88, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_88, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_204, c_405])).
% 4.20/1.83  tff(c_493, plain, (![B_91]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_91, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_91, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_417])).
% 4.20/1.83  tff(c_546, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_56, c_493])).
% 4.20/1.83  tff(c_900, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_892, c_546])).
% 4.20/1.83  tff(c_190, plain, (v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_143])).
% 4.20/1.83  tff(c_138, plain, (~v8_lattices('#skF_6') | ~v9_lattices('#skF_6') | k4_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_120])).
% 4.20/1.83  tff(c_210, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_204, c_138])).
% 4.20/1.83  tff(c_278, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_8')=k2_lattices('#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_255])).
% 4.20/1.83  tff(c_306, plain, (k2_lattices('#skF_6', '#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_278])).
% 4.20/1.83  tff(c_1001, plain, (![A_104, B_105, C_106, D_107]: (k1_lattices(A_104, k2_lattices(A_104, B_105, C_106), k2_lattices(A_104, B_105, D_107))=k2_lattices(A_104, B_105, k1_lattices(A_104, C_106, D_107)) | ~m1_subset_1(D_107, u1_struct_0(A_104)) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~v11_lattices(A_104) | ~l3_lattices(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.20/1.83  tff(c_1053, plain, (![C_106]: (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', C_106, '#skF_8'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', C_106), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(C_106, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_1001])).
% 4.20/1.83  tff(c_1097, plain, (![C_106]: (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', C_106, '#skF_8'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', C_106), '#skF_8') | ~m1_subset_1(C_106, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_54, c_54, c_1053])).
% 4.20/1.83  tff(c_1407, plain, (![C_113]: (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', C_113, '#skF_8'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', C_113), '#skF_8') | ~m1_subset_1(C_113, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1097])).
% 4.20/1.83  tff(c_1436, plain, (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', '#skF_7', '#skF_8'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_56, c_1407])).
% 4.20/1.83  tff(c_1462, plain, (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', '#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_900, c_1436])).
% 4.20/1.83  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.20/1.83  tff(c_65, plain, (![A_63]: (l2_lattices(A_63) | ~l3_lattices(A_63))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.20/1.83  tff(c_69, plain, (l2_lattices('#skF_6')), inference(resolution, [status(thm)], [c_58, c_65])).
% 4.20/1.83  tff(c_613, plain, (![A_93, B_94, C_95]: (k3_lattices(A_93, B_94, C_95)=k1_lattices(A_93, B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0(A_93)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l2_lattices(A_93) | ~v4_lattices(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.20/1.83  tff(c_629, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_7')=k1_lattices('#skF_6', B_94, '#skF_7') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_613])).
% 4.20/1.83  tff(c_645, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_7')=k1_lattices('#skF_6', B_94, '#skF_7') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_629])).
% 4.20/1.83  tff(c_646, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_7')=k1_lattices('#skF_6', B_94, '#skF_7') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_645])).
% 4.20/1.83  tff(c_726, plain, (~v4_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_646])).
% 4.20/1.83  tff(c_729, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_12, c_726])).
% 4.20/1.83  tff(c_732, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_729])).
% 4.20/1.83  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_732])).
% 4.20/1.83  tff(c_736, plain, (v4_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_646])).
% 4.20/1.83  tff(c_625, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_8')=k1_lattices('#skF_6', B_94, '#skF_8') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_613])).
% 4.20/1.83  tff(c_637, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_8')=k1_lattices('#skF_6', B_94, '#skF_8') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_625])).
% 4.20/1.83  tff(c_638, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_8')=k1_lattices('#skF_6', B_94, '#skF_8') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_637])).
% 4.20/1.83  tff(c_1234, plain, (![B_110]: (k3_lattices('#skF_6', B_110, '#skF_8')=k1_lattices('#skF_6', B_110, '#skF_8') | ~m1_subset_1(B_110, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_638])).
% 4.20/1.83  tff(c_1287, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_8')=k1_lattices('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_1234])).
% 4.20/1.83  tff(c_627, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_9')=k1_lattices('#skF_6', B_94, '#skF_9') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_613])).
% 4.20/1.83  tff(c_641, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_9')=k1_lattices('#skF_6', B_94, '#skF_9') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_627])).
% 4.20/1.83  tff(c_642, plain, (![B_94]: (k3_lattices('#skF_6', B_94, '#skF_9')=k1_lattices('#skF_6', B_94, '#skF_9') | ~m1_subset_1(B_94, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_641])).
% 4.20/1.83  tff(c_1161, plain, (![B_109]: (k3_lattices('#skF_6', B_109, '#skF_9')=k1_lattices('#skF_6', B_109, '#skF_9') | ~m1_subset_1(B_109, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_642])).
% 4.20/1.83  tff(c_1214, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_56, c_1161])).
% 4.20/1.83  tff(c_48, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k3_lattices('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_1223, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_8')=k1_lattices('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_48])).
% 4.20/1.83  tff(c_1305, plain, (k1_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1287, c_1223])).
% 4.20/1.83  tff(c_50, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k4_lattices('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.20/1.83  tff(c_317, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_50])).
% 4.20/1.83  tff(c_235, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_9')=k2_lattices('#skF_6', B_83, '#skF_9') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_221])).
% 4.20/1.83  tff(c_249, plain, (![B_83]: (k4_lattices('#skF_6', B_83, '#skF_9')=k2_lattices('#skF_6', B_83, '#skF_9') | ~m1_subset_1(B_83, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_235])).
% 4.20/1.83  tff(c_326, plain, (![B_86]: (k4_lattices('#skF_6', B_86, '#skF_9')=k2_lattices('#skF_6', B_86, '#skF_9') | ~m1_subset_1(B_86, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_249])).
% 4.20/1.83  tff(c_355, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_56, c_326])).
% 4.20/1.83  tff(c_380, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_355])).
% 4.20/1.83  tff(c_407, plain, (![B_88]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_88, '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1(B_88, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_393])).
% 4.20/1.83  tff(c_421, plain, (![B_88]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_88, '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1(B_88, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_204, c_407])).
% 4.20/1.83  tff(c_659, plain, (![B_96]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_96, '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1(B_96, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_421])).
% 4.20/1.83  tff(c_688, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_56, c_659])).
% 4.20/1.83  tff(c_713, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_8'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_688])).
% 4.20/1.83  tff(c_899, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_892, c_713])).
% 4.20/1.83  tff(c_902, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_892, c_317])).
% 4.20/1.83  tff(c_478, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_7')=k2_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_427])).
% 4.20/1.83  tff(c_751, plain, (![B_99]: (k4_lattices('#skF_6', B_99, '#skF_9')=k4_lattices('#skF_6', '#skF_9', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_737])).
% 4.20/1.83  tff(c_765, plain, (![B_99]: (k4_lattices('#skF_6', B_99, '#skF_9')=k4_lattices('#skF_6', '#skF_9', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_74, c_751])).
% 4.20/1.83  tff(c_925, plain, (![B_103]: (k4_lattices('#skF_6', B_103, '#skF_9')=k4_lattices('#skF_6', '#skF_9', B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_765])).
% 4.20/1.83  tff(c_954, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k4_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_925])).
% 4.20/1.83  tff(c_980, plain, (k2_lattices('#skF_6', '#skF_9', '#skF_7')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_902, c_478, c_954])).
% 4.20/1.83  tff(c_109, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_9')='#skF_9' | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_95])).
% 4.20/1.83  tff(c_123, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_9')='#skF_9' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109])).
% 4.20/1.83  tff(c_124, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_9')='#skF_9' | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_123])).
% 4.20/1.83  tff(c_216, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_204, c_190, c_124])).
% 4.20/1.83  tff(c_352, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_9')=k2_lattices('#skF_6', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_326])).
% 4.20/1.83  tff(c_378, plain, (k2_lattices('#skF_6', '#skF_9', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_352])).
% 4.20/1.83  tff(c_1047, plain, (![C_106]: (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_106, '#skF_9'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_106), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1(C_106, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_1001])).
% 4.20/1.83  tff(c_1091, plain, (![C_106]: (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_106, '#skF_9'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_106), '#skF_9') | ~m1_subset_1(C_106, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_52, c_52, c_1047])).
% 4.20/1.83  tff(c_1315, plain, (![C_112]: (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_112, '#skF_9'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_112), '#skF_9') | ~m1_subset_1(C_112, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1091])).
% 4.20/1.83  tff(c_1344, plain, (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', '#skF_9'))=k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', '#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_1315])).
% 4.20/1.83  tff(c_1370, plain, (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_899, c_980, c_1344])).
% 4.20/1.83  tff(c_307, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_8')=k2_lattices('#skF_6', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_255])).
% 4.20/1.83  tff(c_376, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_9')=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_54, c_326])).
% 4.20/1.83  tff(c_863, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_8')=k4_lattices('#skF_6', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_837])).
% 4.20/1.83  tff(c_890, plain, (k2_lattices('#skF_6', '#skF_9', '#skF_8')=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_376, c_863])).
% 4.20/1.83  tff(c_1014, plain, (![D_107]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_9', D_107))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', D_107)) | ~m1_subset_1(D_107, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_980, c_1001])).
% 4.20/1.83  tff(c_1058, plain, (![D_107]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_9', D_107))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', D_107)) | ~m1_subset_1(D_107, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_52, c_56, c_1014])).
% 4.20/1.83  tff(c_1848, plain, (![D_120]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_9', D_120))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', D_120)) | ~m1_subset_1(D_120, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1058])).
% 4.20/1.83  tff(c_1872, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_1848])).
% 4.20/1.83  tff(c_1883, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1370, c_1872])).
% 4.20/1.83  tff(c_18, plain, (![A_5, B_20, C_24, D_26]: (k1_lattices(A_5, k2_lattices(A_5, B_20, C_24), k2_lattices(A_5, B_20, D_26))=k2_lattices(A_5, B_20, k1_lattices(A_5, C_24, D_26)) | ~m1_subset_1(D_26, u1_struct_0(A_5)) | ~m1_subset_1(C_24, u1_struct_0(A_5)) | ~m1_subset_1(B_20, u1_struct_0(A_5)) | ~v11_lattices(A_5) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.20/1.83  tff(c_1889, plain, (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', '#skF_7', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1883, c_18])).
% 4.20/1.83  tff(c_1896, plain, ('#skF_9'='#skF_8' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_54, c_56, c_52, c_1462, c_1305, c_1889])).
% 4.20/1.83  tff(c_1898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_1896])).
% 4.20/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.83  
% 4.20/1.83  Inference rules
% 4.20/1.83  ----------------------
% 4.20/1.83  #Ref     : 0
% 4.20/1.83  #Sup     : 372
% 4.20/1.83  #Fact    : 0
% 4.20/1.83  #Define  : 0
% 4.20/1.83  #Split   : 6
% 4.20/1.83  #Chain   : 0
% 4.20/1.83  #Close   : 0
% 4.20/1.83  
% 4.20/1.83  Ordering : KBO
% 4.20/1.83  
% 4.20/1.83  Simplification rules
% 4.20/1.83  ----------------------
% 4.20/1.83  #Subsume      : 0
% 4.20/1.83  #Demod        : 453
% 4.20/1.83  #Tautology    : 239
% 4.20/1.83  #SimpNegUnit  : 149
% 4.20/1.83  #BackRed      : 13
% 4.20/1.83  
% 4.20/1.83  #Partial instantiations: 0
% 4.20/1.83  #Strategies tried      : 1
% 4.20/1.83  
% 4.20/1.83  Timing (in seconds)
% 4.20/1.83  ----------------------
% 4.45/1.83  Preprocessing        : 0.39
% 4.45/1.83  Parsing              : 0.19
% 4.45/1.83  CNF conversion       : 0.03
% 4.45/1.83  Main loop            : 0.56
% 4.45/1.83  Inferencing          : 0.19
% 4.45/1.83  Reduction            : 0.20
% 4.45/1.83  Demodulation         : 0.14
% 4.45/1.83  BG Simplification    : 0.03
% 4.45/1.83  Subsumption          : 0.10
% 4.45/1.83  Abstraction          : 0.03
% 4.45/1.83  MUC search           : 0.00
% 4.45/1.83  Cooper               : 0.00
% 4.45/1.83  Total                : 1.02
% 4.45/1.83  Index Insertion      : 0.00
% 4.45/1.83  Index Deletion       : 0.00
% 4.45/1.83  Index Matching       : 0.00
% 4.45/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
