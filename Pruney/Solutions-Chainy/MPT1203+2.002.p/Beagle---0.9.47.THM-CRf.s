%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 922 expanded)
%              Number of leaves         :   39 ( 326 expanded)
%              Depth                    :   17
%              Number of atoms          :  358 (3817 expanded)
%              Number of equality atoms :   99 ( 925 expanded)
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

tff(f_163,negated_conjecture,(
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

tff(f_106,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_125,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v11_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_4'(A_34),u1_struct_0(A_34))
      | v9_lattices(A_34)
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

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
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_69,plain,(
    l2_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_95,plain,(
    ! [A_77,B_78,C_79] :
      ( k3_lattices(A_77,B_78,C_79) = k1_lattices(A_77,B_78,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l2_lattices(A_77)
      | ~ v4_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_107,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_8') = k1_lattices('#skF_6',B_78,'#skF_8')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_95])).

tff(c_119,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_8') = k1_lattices('#skF_6',B_78,'#skF_8')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_107])).

tff(c_120,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_8') = k1_lattices('#skF_6',B_78,'#skF_8')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_119])).

tff(c_129,plain,(
    ~ v4_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_132,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_135])).

tff(c_146,plain,(
    ! [B_80] :
      ( k3_lattices('#skF_6',B_80,'#skF_8') = k1_lattices('#skF_6',B_80,'#skF_8')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_166,plain,
    ( k3_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8') = k1_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8')
    | v9_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_146])).

tff(c_194,plain,
    ( k3_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8') = k1_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8')
    | v9_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_166])).

tff(c_195,plain,
    ( k3_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8') = k1_lattices('#skF_6','#skF_4'('#skF_6'),'#skF_8')
    | v9_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_194])).

tff(c_315,plain,(
    v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_600,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_lattices(A_94,B_95,k1_lattices(A_94,B_95,C_96)) = B_95
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ v9_lattices(A_94)
      | ~ l3_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_616,plain,(
    ! [B_95] :
      ( k2_lattices('#skF_6',B_95,k1_lattices('#skF_6',B_95,'#skF_7')) = B_95
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_600])).

tff(c_632,plain,(
    ! [B_95] :
      ( k2_lattices('#skF_6',B_95,k1_lattices('#skF_6',B_95,'#skF_7')) = B_95
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_315,c_616])).

tff(c_815,plain,(
    ! [B_101] :
      ( k2_lattices('#skF_6',B_101,k1_lattices('#skF_6',B_101,'#skF_7')) = B_101
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_632])).

tff(c_857,plain,(
    k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6','#skF_8','#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_54,c_815])).

tff(c_198,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_8') = k1_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_146])).

tff(c_139,plain,(
    v4_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_111,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_7') = k1_lattices('#skF_6',B_78,'#skF_7')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_127,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_7') = k1_lattices('#skF_6',B_78,'#skF_7')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_111])).

tff(c_128,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_7') = k1_lattices('#skF_6',B_78,'#skF_7')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_127])).

tff(c_140,plain,(
    ~ v4_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_140])).

tff(c_250,plain,(
    ! [B_84] :
      ( k3_lattices('#skF_6',B_84,'#skF_7') = k1_lattices('#skF_6',B_84,'#skF_7')
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_300,plain,(
    k3_lattices('#skF_6','#skF_8','#skF_7') = k1_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_250])).

tff(c_423,plain,(
    ! [A_89,C_90,B_91] :
      ( k3_lattices(A_89,C_90,B_91) = k3_lattices(A_89,B_91,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(A_89))
      | ~ m1_subset_1(B_91,u1_struct_0(A_89))
      | ~ l2_lattices(A_89)
      | ~ v4_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_435,plain,(
    ! [B_91] :
      ( k3_lattices('#skF_6',B_91,'#skF_8') = k3_lattices('#skF_6','#skF_8',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_423])).

tff(c_447,plain,(
    ! [B_91] :
      ( k3_lattices('#skF_6',B_91,'#skF_8') = k3_lattices('#skF_6','#skF_8',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_69,c_435])).

tff(c_470,plain,(
    ! [B_92] :
      ( k3_lattices('#skF_6',B_92,'#skF_8') = k3_lattices('#skF_6','#skF_8',B_92)
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_447])).

tff(c_499,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_8') = k3_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_470])).

tff(c_525,plain,(
    k1_lattices('#skF_6','#skF_7','#skF_8') = k1_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_300,c_499])).

tff(c_48,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k3_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_237,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_48])).

tff(c_530,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_237])).

tff(c_109,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_9') = k1_lattices('#skF_6',B_78,'#skF_9')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_123,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_9') = k1_lattices('#skF_6',B_78,'#skF_9')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_109])).

tff(c_124,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_6',B_78,'#skF_9') = k1_lattices('#skF_6',B_78,'#skF_9')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_6'))
      | ~ v4_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_123])).

tff(c_936,plain,(
    ! [B_103] :
      ( k3_lattices('#skF_6',B_103,'#skF_9') = k1_lattices('#skF_6',B_103,'#skF_9')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_124])).

tff(c_965,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_936])).

tff(c_989,plain,(
    k1_lattices('#skF_6','#skF_7','#skF_9') = k1_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_965])).

tff(c_301,plain,(
    k3_lattices('#skF_6','#skF_9','#skF_7') = k1_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_250])).

tff(c_439,plain,(
    ! [B_91] :
      ( k3_lattices('#skF_6',B_91,'#skF_7') = k3_lattices('#skF_6','#skF_7',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_423])).

tff(c_455,plain,(
    ! [B_91] :
      ( k3_lattices('#skF_6',B_91,'#skF_7') = k3_lattices('#skF_6','#skF_7',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_69,c_439])).

tff(c_544,plain,(
    ! [B_93] :
      ( k3_lattices('#skF_6',B_93,'#skF_7') = k3_lattices('#skF_6','#skF_7',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_455])).

tff(c_570,plain,(
    k3_lattices('#skF_6','#skF_7','#skF_9') = k3_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_544])).

tff(c_597,plain,(
    k1_lattices('#skF_6','#skF_9','#skF_7') = k1_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_301,c_570])).

tff(c_834,plain,(
    k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_9','#skF_7')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_52,c_815])).

tff(c_859,plain,(
    k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_8','#skF_7')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_834])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_64] :
      ( l1_lattices(A_64)
      | ~ l3_lattices(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_316,plain,(
    ! [A_85,C_86,B_87] :
      ( k4_lattices(A_85,C_86,B_87) = k4_lattices(A_85,B_87,C_86)
      | ~ m1_subset_1(C_86,u1_struct_0(A_85))
      | ~ m1_subset_1(B_87,u1_struct_0(A_85))
      | ~ l1_lattices(A_85)
      | ~ v6_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_332,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_7') = k4_lattices('#skF_6','#skF_7',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_316])).

tff(c_348,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_7') = k4_lattices('#skF_6','#skF_7',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_332])).

tff(c_349,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_7') = k4_lattices('#skF_6','#skF_7',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_348])).

tff(c_353,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_356,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_353])).

tff(c_359,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_356])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_359])).

tff(c_363,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_199,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_lattices(A_81,B_82,C_83) = k2_lattices(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_lattices(A_81)
      | ~ v6_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_215,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_7') = k2_lattices('#skF_6',B_82,'#skF_7')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_199])).

tff(c_231,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_7') = k2_lattices('#skF_6',B_82,'#skF_7')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_215])).

tff(c_232,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_7') = k2_lattices('#skF_6',B_82,'#skF_7')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_231])).

tff(c_1208,plain,(
    ! [B_109] :
      ( k4_lattices('#skF_6',B_109,'#skF_7') = k2_lattices('#skF_6',B_109,'#skF_7')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_232])).

tff(c_1258,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_7') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_1208])).

tff(c_213,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_9') = k2_lattices('#skF_6',B_82,'#skF_9')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_199])).

tff(c_227,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_9') = k2_lattices('#skF_6',B_82,'#skF_9')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_213])).

tff(c_228,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_9') = k2_lattices('#skF_6',B_82,'#skF_9')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_227])).

tff(c_1129,plain,(
    ! [B_108] :
      ( k4_lattices('#skF_6',B_108,'#skF_9') = k2_lattices('#skF_6',B_108,'#skF_9')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_228])).

tff(c_1181,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_1129])).

tff(c_364,plain,(
    ! [B_88] :
      ( k4_lattices('#skF_6',B_88,'#skF_7') = k4_lattices('#skF_6','#skF_7',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_414,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_8') = k4_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_364])).

tff(c_50,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k4_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_418,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k4_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_50])).

tff(c_1197,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_7') = k2_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_418])).

tff(c_1271,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_9') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1197])).

tff(c_1259,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_7') = k2_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_1208])).

tff(c_415,plain,(
    k4_lattices('#skF_6','#skF_7','#skF_9') = k4_lattices('#skF_6','#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_364])).

tff(c_461,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_7') = k4_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_415])).

tff(c_1265,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_7') = k2_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_461])).

tff(c_1302,plain,(
    k2_lattices('#skF_6','#skF_9','#skF_7') = k2_lattices('#skF_6','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_1259,c_1265])).

tff(c_1179,plain,(
    k4_lattices('#skF_6','#skF_8','#skF_9') = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_1129])).

tff(c_328,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_316])).

tff(c_340,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_328])).

tff(c_341,plain,(
    ! [B_87] :
      ( k4_lattices('#skF_6',B_87,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_87)
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_340])).

tff(c_875,plain,(
    ! [B_102] :
      ( k4_lattices('#skF_6',B_102,'#skF_8') = k4_lattices('#skF_6','#skF_8',B_102)
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_341])).

tff(c_927,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_8') = k4_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_875])).

tff(c_1188,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_8') = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_927])).

tff(c_211,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_8') = k2_lattices('#skF_6',B_82,'#skF_8')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_199])).

tff(c_223,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_8') = k2_lattices('#skF_6',B_82,'#skF_8')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_211])).

tff(c_224,plain,(
    ! [B_82] :
      ( k4_lattices('#skF_6',B_82,'#skF_8') = k2_lattices('#skF_6',B_82,'#skF_8')
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_223])).

tff(c_1409,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_6',B_111,'#skF_8') = k2_lattices('#skF_6',B_111,'#skF_8')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_224])).

tff(c_1435,plain,(
    k4_lattices('#skF_6','#skF_9','#skF_8') = k2_lattices('#skF_6','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_1409])).

tff(c_1461,plain,(
    k2_lattices('#skF_6','#skF_9','#skF_8') = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1435])).

tff(c_20,plain,(
    ! [A_8,B_23,C_27,D_29] :
      ( k1_lattices(A_8,k2_lattices(A_8,B_23,C_27),k2_lattices(A_8,B_23,D_29)) = k2_lattices(A_8,B_23,k1_lattices(A_8,C_27,D_29))
      | ~ m1_subset_1(D_29,u1_struct_0(A_8))
      | ~ m1_subset_1(C_27,u1_struct_0(A_8))
      | ~ m1_subset_1(B_23,u1_struct_0(A_8))
      | ~ v11_lattices(A_8)
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1474,plain,(
    ! [C_27] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_27),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_27,'#skF_8'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ v11_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_20])).

tff(c_1481,plain,(
    ! [C_27] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_27),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_27,'#skF_8'))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_52,c_54,c_1474])).

tff(c_1771,plain,(
    ! [C_122] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_9',C_122),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6',C_122,'#skF_8'))
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1481])).

tff(c_1798,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_9',k1_lattices('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_1771])).

tff(c_1819,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_8','#skF_7'),k2_lattices('#skF_6','#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_859,c_525,c_1798])).

tff(c_1823,plain,
    ( k2_lattices('#skF_6','#skF_8',k1_lattices('#skF_6','#skF_7','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v11_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_20])).

tff(c_1830,plain,
    ( '#skF_9' = '#skF_8'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_54,c_56,c_52,c_857,c_989,c_1823])).

tff(c_1832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_1830])).

tff(c_1834,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_1838,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_1834])).

tff(c_1841,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_1838])).

tff(c_1843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  
% 3.87/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 3.87/1.66  
% 3.87/1.66  %Foreground sorts:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Background operators:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Foreground operators:
% 3.87/1.66  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.87/1.66  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.87/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.87/1.66  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.87/1.66  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.87/1.66  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.87/1.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.87/1.66  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.66  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.87/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.66  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.87/1.66  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.87/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.87/1.66  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.87/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.87/1.66  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.87/1.66  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.87/1.66  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.87/1.66  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.87/1.66  tff('#skF_9', type, '#skF_9': $i).
% 3.87/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.66  tff(v11_lattices, type, v11_lattices: $i > $o).
% 3.87/1.66  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.87/1.66  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.66  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.87/1.66  
% 4.15/1.70  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 4.15/1.70  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 4.15/1.70  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 4.15/1.70  tff(f_112, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 4.15/1.70  tff(f_125, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 4.15/1.70  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 4.15/1.70  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 4.15/1.70  tff(f_138, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 4.15/1.70  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v11_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k2_lattices(A, B, C), k2_lattices(A, B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattices)).
% 4.15/1.70  tff(c_64, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_58, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_62, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.15/1.70  tff(c_46, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_60, plain, (v11_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_54, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_52, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_36, plain, (![A_34]: (m1_subset_1('#skF_4'(A_34), u1_struct_0(A_34)) | v9_lattices(A_34) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.70  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.15/1.70  tff(c_65, plain, (![A_63]: (l2_lattices(A_63) | ~l3_lattices(A_63))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.15/1.70  tff(c_69, plain, (l2_lattices('#skF_6')), inference(resolution, [status(thm)], [c_58, c_65])).
% 4.15/1.70  tff(c_95, plain, (![A_77, B_78, C_79]: (k3_lattices(A_77, B_78, C_79)=k1_lattices(A_77, B_78, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l2_lattices(A_77) | ~v4_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.15/1.70  tff(c_107, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_8')=k1_lattices('#skF_6', B_78, '#skF_8') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_95])).
% 4.15/1.70  tff(c_119, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_8')=k1_lattices('#skF_6', B_78, '#skF_8') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_107])).
% 4.15/1.70  tff(c_120, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_8')=k1_lattices('#skF_6', B_78, '#skF_8') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_119])).
% 4.15/1.70  tff(c_129, plain, (~v4_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_120])).
% 4.15/1.70  tff(c_132, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_12, c_129])).
% 4.15/1.70  tff(c_135, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_132])).
% 4.15/1.70  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_135])).
% 4.15/1.70  tff(c_146, plain, (![B_80]: (k3_lattices('#skF_6', B_80, '#skF_8')=k1_lattices('#skF_6', B_80, '#skF_8') | ~m1_subset_1(B_80, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_120])).
% 4.15/1.70  tff(c_166, plain, (k3_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8')=k1_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8') | v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_146])).
% 4.15/1.70  tff(c_194, plain, (k3_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8')=k1_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8') | v9_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_166])).
% 4.15/1.70  tff(c_195, plain, (k3_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8')=k1_lattices('#skF_6', '#skF_4'('#skF_6'), '#skF_8') | v9_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_194])).
% 4.15/1.70  tff(c_315, plain, (v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_195])).
% 4.15/1.70  tff(c_600, plain, (![A_94, B_95, C_96]: (k2_lattices(A_94, B_95, k1_lattices(A_94, B_95, C_96))=B_95 | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~v9_lattices(A_94) | ~l3_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.70  tff(c_616, plain, (![B_95]: (k2_lattices('#skF_6', B_95, k1_lattices('#skF_6', B_95, '#skF_7'))=B_95 | ~m1_subset_1(B_95, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_600])).
% 4.15/1.70  tff(c_632, plain, (![B_95]: (k2_lattices('#skF_6', B_95, k1_lattices('#skF_6', B_95, '#skF_7'))=B_95 | ~m1_subset_1(B_95, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_315, c_616])).
% 4.15/1.70  tff(c_815, plain, (![B_101]: (k2_lattices('#skF_6', B_101, k1_lattices('#skF_6', B_101, '#skF_7'))=B_101 | ~m1_subset_1(B_101, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_632])).
% 4.15/1.70  tff(c_857, plain, (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', '#skF_8', '#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_54, c_815])).
% 4.15/1.70  tff(c_198, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_8')=k1_lattices('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_146])).
% 4.15/1.70  tff(c_139, plain, (v4_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 4.15/1.70  tff(c_111, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_7')=k1_lattices('#skF_6', B_78, '#skF_7') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_95])).
% 4.15/1.70  tff(c_127, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_7')=k1_lattices('#skF_6', B_78, '#skF_7') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_111])).
% 4.15/1.70  tff(c_128, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_7')=k1_lattices('#skF_6', B_78, '#skF_7') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_127])).
% 4.15/1.70  tff(c_140, plain, (~v4_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_128])).
% 4.15/1.70  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_140])).
% 4.15/1.70  tff(c_250, plain, (![B_84]: (k3_lattices('#skF_6', B_84, '#skF_7')=k1_lattices('#skF_6', B_84, '#skF_7') | ~m1_subset_1(B_84, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_128])).
% 4.15/1.70  tff(c_300, plain, (k3_lattices('#skF_6', '#skF_8', '#skF_7')=k1_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_250])).
% 4.15/1.70  tff(c_423, plain, (![A_89, C_90, B_91]: (k3_lattices(A_89, C_90, B_91)=k3_lattices(A_89, B_91, C_90) | ~m1_subset_1(C_90, u1_struct_0(A_89)) | ~m1_subset_1(B_91, u1_struct_0(A_89)) | ~l2_lattices(A_89) | ~v4_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.70  tff(c_435, plain, (![B_91]: (k3_lattices('#skF_6', B_91, '#skF_8')=k3_lattices('#skF_6', '#skF_8', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_423])).
% 4.15/1.70  tff(c_447, plain, (![B_91]: (k3_lattices('#skF_6', B_91, '#skF_8')=k3_lattices('#skF_6', '#skF_8', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_69, c_435])).
% 4.15/1.70  tff(c_470, plain, (![B_92]: (k3_lattices('#skF_6', B_92, '#skF_8')=k3_lattices('#skF_6', '#skF_8', B_92) | ~m1_subset_1(B_92, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_447])).
% 4.15/1.70  tff(c_499, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_8')=k3_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_470])).
% 4.15/1.70  tff(c_525, plain, (k1_lattices('#skF_6', '#skF_7', '#skF_8')=k1_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_300, c_499])).
% 4.15/1.70  tff(c_48, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k3_lattices('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_237, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_48])).
% 4.15/1.70  tff(c_530, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_237])).
% 4.15/1.70  tff(c_109, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_9')=k1_lattices('#skF_6', B_78, '#skF_9') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_95])).
% 4.15/1.70  tff(c_123, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_9')=k1_lattices('#skF_6', B_78, '#skF_9') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_109])).
% 4.15/1.70  tff(c_124, plain, (![B_78]: (k3_lattices('#skF_6', B_78, '#skF_9')=k1_lattices('#skF_6', B_78, '#skF_9') | ~m1_subset_1(B_78, u1_struct_0('#skF_6')) | ~v4_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_123])).
% 4.15/1.70  tff(c_936, plain, (![B_103]: (k3_lattices('#skF_6', B_103, '#skF_9')=k1_lattices('#skF_6', B_103, '#skF_9') | ~m1_subset_1(B_103, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_124])).
% 4.15/1.70  tff(c_965, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_56, c_936])).
% 4.15/1.70  tff(c_989, plain, (k1_lattices('#skF_6', '#skF_7', '#skF_9')=k1_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_530, c_965])).
% 4.15/1.70  tff(c_301, plain, (k3_lattices('#skF_6', '#skF_9', '#skF_7')=k1_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_250])).
% 4.15/1.70  tff(c_439, plain, (![B_91]: (k3_lattices('#skF_6', B_91, '#skF_7')=k3_lattices('#skF_6', '#skF_7', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_423])).
% 4.15/1.70  tff(c_455, plain, (![B_91]: (k3_lattices('#skF_6', B_91, '#skF_7')=k3_lattices('#skF_6', '#skF_7', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_69, c_439])).
% 4.15/1.70  tff(c_544, plain, (![B_93]: (k3_lattices('#skF_6', B_93, '#skF_7')=k3_lattices('#skF_6', '#skF_7', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_455])).
% 4.15/1.70  tff(c_570, plain, (k3_lattices('#skF_6', '#skF_7', '#skF_9')=k3_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_544])).
% 4.15/1.70  tff(c_597, plain, (k1_lattices('#skF_6', '#skF_9', '#skF_7')=k1_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_530, c_301, c_570])).
% 4.15/1.70  tff(c_834, plain, (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_9', '#skF_7'))='#skF_9'), inference(resolution, [status(thm)], [c_52, c_815])).
% 4.15/1.70  tff(c_859, plain, (k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_8', '#skF_7'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_597, c_834])).
% 4.15/1.70  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.15/1.70  tff(c_70, plain, (![A_64]: (l1_lattices(A_64) | ~l3_lattices(A_64))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.15/1.70  tff(c_74, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_58, c_70])).
% 4.15/1.70  tff(c_316, plain, (![A_85, C_86, B_87]: (k4_lattices(A_85, C_86, B_87)=k4_lattices(A_85, B_87, C_86) | ~m1_subset_1(C_86, u1_struct_0(A_85)) | ~m1_subset_1(B_87, u1_struct_0(A_85)) | ~l1_lattices(A_85) | ~v6_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.15/1.70  tff(c_332, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_7')=k4_lattices('#skF_6', '#skF_7', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_316])).
% 4.15/1.70  tff(c_348, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_7')=k4_lattices('#skF_6', '#skF_7', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_332])).
% 4.15/1.70  tff(c_349, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_7')=k4_lattices('#skF_6', '#skF_7', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_348])).
% 4.15/1.70  tff(c_353, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_349])).
% 4.15/1.70  tff(c_356, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_353])).
% 4.15/1.70  tff(c_359, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_356])).
% 4.15/1.70  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_359])).
% 4.15/1.70  tff(c_363, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_349])).
% 4.15/1.70  tff(c_199, plain, (![A_81, B_82, C_83]: (k4_lattices(A_81, B_82, C_83)=k2_lattices(A_81, B_82, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_lattices(A_81) | ~v6_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.70  tff(c_215, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_7')=k2_lattices('#skF_6', B_82, '#skF_7') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_199])).
% 4.15/1.70  tff(c_231, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_7')=k2_lattices('#skF_6', B_82, '#skF_7') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_215])).
% 4.15/1.70  tff(c_232, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_7')=k2_lattices('#skF_6', B_82, '#skF_7') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_231])).
% 4.15/1.70  tff(c_1208, plain, (![B_109]: (k4_lattices('#skF_6', B_109, '#skF_7')=k2_lattices('#skF_6', B_109, '#skF_7') | ~m1_subset_1(B_109, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_232])).
% 4.15/1.70  tff(c_1258, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_7')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_1208])).
% 4.15/1.70  tff(c_213, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_9')=k2_lattices('#skF_6', B_82, '#skF_9') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_199])).
% 4.15/1.70  tff(c_227, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_9')=k2_lattices('#skF_6', B_82, '#skF_9') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_213])).
% 4.15/1.70  tff(c_228, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_9')=k2_lattices('#skF_6', B_82, '#skF_9') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_227])).
% 4.15/1.70  tff(c_1129, plain, (![B_108]: (k4_lattices('#skF_6', B_108, '#skF_9')=k2_lattices('#skF_6', B_108, '#skF_9') | ~m1_subset_1(B_108, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_228])).
% 4.15/1.70  tff(c_1181, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_56, c_1129])).
% 4.15/1.70  tff(c_364, plain, (![B_88]: (k4_lattices('#skF_6', B_88, '#skF_7')=k4_lattices('#skF_6', '#skF_7', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_349])).
% 4.15/1.70  tff(c_414, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_8')=k4_lattices('#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_364])).
% 4.15/1.70  tff(c_50, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k4_lattices('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.15/1.70  tff(c_418, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k4_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_50])).
% 4.15/1.70  tff(c_1197, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_7')=k2_lattices('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_418])).
% 4.15/1.70  tff(c_1271, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_9')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1197])).
% 4.15/1.70  tff(c_1259, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_7')=k2_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_1208])).
% 4.15/1.70  tff(c_415, plain, (k4_lattices('#skF_6', '#skF_7', '#skF_9')=k4_lattices('#skF_6', '#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_364])).
% 4.15/1.70  tff(c_461, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_7')=k4_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_415])).
% 4.15/1.70  tff(c_1265, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_7')=k2_lattices('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_461])).
% 4.15/1.70  tff(c_1302, plain, (k2_lattices('#skF_6', '#skF_9', '#skF_7')=k2_lattices('#skF_6', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_1259, c_1265])).
% 4.15/1.70  tff(c_1179, plain, (k4_lattices('#skF_6', '#skF_8', '#skF_9')=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_54, c_1129])).
% 4.15/1.70  tff(c_328, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_316])).
% 4.15/1.70  tff(c_340, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_328])).
% 4.15/1.70  tff(c_341, plain, (![B_87]: (k4_lattices('#skF_6', B_87, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_87) | ~m1_subset_1(B_87, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_340])).
% 4.15/1.70  tff(c_875, plain, (![B_102]: (k4_lattices('#skF_6', B_102, '#skF_8')=k4_lattices('#skF_6', '#skF_8', B_102) | ~m1_subset_1(B_102, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_341])).
% 4.15/1.70  tff(c_927, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_8')=k4_lattices('#skF_6', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_875])).
% 4.15/1.70  tff(c_1188, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_8')=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_927])).
% 4.15/1.70  tff(c_211, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_8')=k2_lattices('#skF_6', B_82, '#skF_8') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_199])).
% 4.15/1.70  tff(c_223, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_8')=k2_lattices('#skF_6', B_82, '#skF_8') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_211])).
% 4.15/1.70  tff(c_224, plain, (![B_82]: (k4_lattices('#skF_6', B_82, '#skF_8')=k2_lattices('#skF_6', B_82, '#skF_8') | ~m1_subset_1(B_82, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_223])).
% 4.15/1.70  tff(c_1409, plain, (![B_111]: (k4_lattices('#skF_6', B_111, '#skF_8')=k2_lattices('#skF_6', B_111, '#skF_8') | ~m1_subset_1(B_111, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_224])).
% 4.15/1.70  tff(c_1435, plain, (k4_lattices('#skF_6', '#skF_9', '#skF_8')=k2_lattices('#skF_6', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_1409])).
% 4.15/1.70  tff(c_1461, plain, (k2_lattices('#skF_6', '#skF_9', '#skF_8')=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1435])).
% 4.15/1.70  tff(c_20, plain, (![A_8, B_23, C_27, D_29]: (k1_lattices(A_8, k2_lattices(A_8, B_23, C_27), k2_lattices(A_8, B_23, D_29))=k2_lattices(A_8, B_23, k1_lattices(A_8, C_27, D_29)) | ~m1_subset_1(D_29, u1_struct_0(A_8)) | ~m1_subset_1(C_27, u1_struct_0(A_8)) | ~m1_subset_1(B_23, u1_struct_0(A_8)) | ~v11_lattices(A_8) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.15/1.70  tff(c_1474, plain, (![C_27]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_27), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_27, '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(C_27, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1461, c_20])).
% 4.15/1.70  tff(c_1481, plain, (![C_27]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_27), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_27, '#skF_8')) | ~m1_subset_1(C_27, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_52, c_54, c_1474])).
% 4.15/1.70  tff(c_1771, plain, (![C_122]: (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_9', C_122), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', C_122, '#skF_8')) | ~m1_subset_1(C_122, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1481])).
% 4.15/1.70  tff(c_1798, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_9', k1_lattices('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_1771])).
% 4.15/1.70  tff(c_1819, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_8', '#skF_7'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_859, c_525, c_1798])).
% 4.15/1.70  tff(c_1823, plain, (k2_lattices('#skF_6', '#skF_8', k1_lattices('#skF_6', '#skF_7', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v11_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1819, c_20])).
% 4.15/1.70  tff(c_1830, plain, ('#skF_9'='#skF_8' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_54, c_56, c_52, c_857, c_989, c_1823])).
% 4.15/1.70  tff(c_1832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_1830])).
% 4.15/1.70  tff(c_1834, plain, (~v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_195])).
% 4.15/1.70  tff(c_1838, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_2, c_1834])).
% 4.15/1.70  tff(c_1841, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_1838])).
% 4.15/1.70  tff(c_1843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1841])).
% 4.15/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.70  
% 4.15/1.70  Inference rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Ref     : 0
% 4.15/1.70  #Sup     : 374
% 4.15/1.70  #Fact    : 0
% 4.15/1.70  #Define  : 0
% 4.15/1.70  #Split   : 5
% 4.15/1.70  #Chain   : 0
% 4.15/1.70  #Close   : 0
% 4.15/1.70  
% 4.15/1.70  Ordering : KBO
% 4.15/1.70  
% 4.15/1.70  Simplification rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Subsume      : 0
% 4.15/1.70  #Demod        : 439
% 4.15/1.70  #Tautology    : 245
% 4.15/1.70  #SimpNegUnit  : 144
% 4.15/1.70  #BackRed      : 19
% 4.15/1.70  
% 4.15/1.70  #Partial instantiations: 0
% 4.15/1.70  #Strategies tried      : 1
% 4.15/1.70  
% 4.15/1.70  Timing (in seconds)
% 4.15/1.70  ----------------------
% 4.15/1.70  Preprocessing        : 0.36
% 4.15/1.70  Parsing              : 0.19
% 4.15/1.70  CNF conversion       : 0.03
% 4.15/1.70  Main loop            : 0.54
% 4.15/1.70  Inferencing          : 0.18
% 4.15/1.70  Reduction            : 0.20
% 4.15/1.70  Demodulation         : 0.14
% 4.15/1.70  BG Simplification    : 0.03
% 4.15/1.70  Subsumption          : 0.10
% 4.15/1.70  Abstraction          : 0.03
% 4.15/1.70  MUC search           : 0.00
% 4.15/1.70  Cooper               : 0.00
% 4.15/1.70  Total                : 0.97
% 4.15/1.70  Index Insertion      : 0.00
% 4.15/1.70  Index Deletion       : 0.00
% 4.15/1.70  Index Matching       : 0.00
% 4.15/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
