%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:14 EST 2020

% Result     : Theorem 51.39s
% Output     : CNFRefutation 51.54s
% Verified   : 
% Statistics : Number of formulae       :  161 (1479 expanded)
%              Number of leaves         :   36 ( 533 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (6318 expanded)
%              Number of equality atoms :   98 (1422 expanded)
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

tff(f_165,negated_conjecture,(
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

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_120,axiom,(
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
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_53] :
      ( l1_lattices(A_53)
      | ~ l3_lattices(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_66,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_42,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k4_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_84,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k4_lattices(A_63,B_64,C_65),u1_struct_0(A_63))
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_lattices(A_63)
      | ~ v6_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_87,plain,
    ( m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_89,plain,
    ( m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48,c_46,c_87])).

tff(c_90,plain,
    ( m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_89])).

tff(c_91,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_122,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_125,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_125])).

tff(c_129,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_482,plain,(
    ! [A_82,B_83,C_84] :
      ( k4_lattices(A_82,B_83,C_84) = k2_lattices(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_lattices(A_82)
      | ~ v6_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_494,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_3',B_83,'#skF_6') = k2_lattices('#skF_3',B_83,'#skF_6')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_482])).

tff(c_510,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_3',B_83,'#skF_6') = k2_lattices('#skF_3',B_83,'#skF_6')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_66,c_494])).

tff(c_1083,plain,(
    ! [B_91] :
      ( k4_lattices('#skF_3',B_91,'#skF_6') = k2_lattices('#skF_3',B_91,'#skF_6')
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_510])).

tff(c_1143,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1083])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_52] :
      ( l2_lattices(A_52)
      | ~ l3_lattices(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_130,plain,(
    ! [A_69,C_70,B_71] :
      ( k3_lattices(A_69,C_70,B_71) = k3_lattices(A_69,B_71,C_70)
      | ~ m1_subset_1(C_70,u1_struct_0(A_69))
      | ~ m1_subset_1(B_71,u1_struct_0(A_69))
      | ~ l2_lattices(A_69)
      | ~ v4_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_154,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_140])).

tff(c_155,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_154])).

tff(c_164,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_167,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_164])).

tff(c_170,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_167])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_170])).

tff(c_174,plain,(
    v4_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_128,plain,(
    m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_222,plain,(
    ! [A_73,B_74,C_75] :
      ( k3_lattices(A_73,B_74,C_75) = k1_lattices(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l2_lattices(A_73)
      | ~ v4_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_224,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6')) = k1_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_222])).

tff(c_239,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6')) = k1_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_61,c_224])).

tff(c_240,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6')) = k1_lattices('#skF_3',B_74,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_239])).

tff(c_3536,plain,(
    ! [B_108] :
      ( k3_lattices('#skF_3',B_108,k2_lattices('#skF_3','#skF_4','#skF_6')) = k1_lattices('#skF_3',B_108,k2_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1143,c_240])).

tff(c_3636,plain,(
    k3_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) = k1_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_3536])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_370,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_lattices(A_78,k2_lattices(A_78,B_79,C_80),C_80) = C_80
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ v8_lattices(A_78)
      | ~ l3_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_382,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_370])).

tff(c_398,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_382])).

tff(c_399,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_398])).

tff(c_1144,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_1147,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1144])).

tff(c_1150,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_1147])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1150])).

tff(c_1349,plain,(
    ! [B_92] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_92,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_1417,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_1349])).

tff(c_234,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_6') = k1_lattices('#skF_3',B_74,'#skF_6')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_222])).

tff(c_250,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_6') = k1_lattices('#skF_3',B_74,'#skF_6')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_61,c_234])).

tff(c_416,plain,(
    ! [B_81] :
      ( k3_lattices('#skF_3',B_81,'#skF_6') = k1_lattices('#skF_3',B_81,'#skF_6')
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_250])).

tff(c_441,plain,(
    k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = k1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_128,c_416])).

tff(c_1996,plain,(
    k3_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_1143,c_1143,c_441])).

tff(c_132,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),B_71) = k3_lattices('#skF_3',B_71,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_130])).

tff(c_147,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),B_71) = k3_lattices('#skF_3',B_71,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_132])).

tff(c_148,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),B_71) = k3_lattices('#skF_3',B_71,k4_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_147])).

tff(c_7954,plain,(
    ! [B_140] :
      ( k3_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),B_140) = k3_lattices('#skF_3',B_140,k2_lattices('#skF_3','#skF_4','#skF_6'))
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_1143,c_1143,c_148])).

tff(c_8054,plain,(
    k3_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),'#skF_6') = k3_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_7954])).

tff(c_8104,plain,(
    k1_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3636,c_1996,c_8054])).

tff(c_8107,plain,(
    k3_lattices('#skF_3','#skF_6',k2_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8104,c_3636])).

tff(c_492,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_3',B_83,'#skF_5') = k2_lattices('#skF_3',B_83,'#skF_5')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_482])).

tff(c_506,plain,(
    ! [B_83] :
      ( k4_lattices('#skF_3',B_83,'#skF_5') = k2_lattices('#skF_3',B_83,'#skF_5')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_66,c_492])).

tff(c_524,plain,(
    ! [B_85] :
      ( k4_lattices('#skF_3',B_85,'#skF_5') = k2_lattices('#skF_3',B_85,'#skF_5')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_506])).

tff(c_564,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_524])).

tff(c_619,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_6') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_42])).

tff(c_1279,plain,(
    k2_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_619])).

tff(c_1343,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_564])).

tff(c_232,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_5') = k1_lattices('#skF_3',B_74,'#skF_5')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_222])).

tff(c_246,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_5') = k1_lattices('#skF_3',B_74,'#skF_5')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_61,c_232])).

tff(c_260,plain,(
    ! [B_76] :
      ( k3_lattices('#skF_3',B_76,'#skF_5') = k1_lattices('#skF_3',B_76,'#skF_5')
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_246])).

tff(c_299,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_5') = k1_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_260])).

tff(c_236,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_4') = k1_lattices('#skF_3',B_74,'#skF_4')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_222])).

tff(c_254,plain,(
    ! [B_74] :
      ( k3_lattices('#skF_3',B_74,'#skF_4') = k1_lattices('#skF_3',B_74,'#skF_4')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_61,c_236])).

tff(c_328,plain,(
    ! [B_77] :
      ( k3_lattices('#skF_3',B_77,'#skF_4') = k1_lattices('#skF_3',B_77,'#skF_4')
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_254])).

tff(c_368,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_4') = k1_lattices('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_328])).

tff(c_457,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_6') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_416])).

tff(c_144,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_130])).

tff(c_162,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_144])).

tff(c_163,plain,(
    ! [B_71] :
      ( k3_lattices('#skF_3',B_71,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_162])).

tff(c_1566,plain,(
    ! [B_94] :
      ( k3_lattices('#skF_3',B_94,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_163])).

tff(c_1608,plain,(
    k3_lattices('#skF_3','#skF_6','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1566])).

tff(c_1635,plain,(
    k1_lattices('#skF_3','#skF_6','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_457,c_1608])).

tff(c_52,plain,(
    v11_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_728,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k4_lattices(A_86,k3_lattices(A_86,B_87,C_88),k3_lattices(A_86,B_87,D_89)) = k3_lattices(A_86,B_87,k4_lattices(A_86,C_88,D_89))
      | ~ m1_subset_1(D_89,u1_struct_0(A_86))
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l3_lattices(A_86)
      | ~ v11_lattices(A_86)
      | ~ v10_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_764,plain,(
    ! [D_89] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_4'),k3_lattices('#skF_3','#skF_6',D_89)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4',D_89))
      | ~ m1_subset_1(D_89,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_728])).

tff(c_819,plain,(
    ! [D_89] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_4'),k3_lattices('#skF_3','#skF_6',D_89)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4',D_89))
      | ~ m1_subset_1(D_89,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_44,c_48,c_764])).

tff(c_820,plain,(
    ! [D_89] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_6','#skF_4'),k3_lattices('#skF_3','#skF_6',D_89)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4',D_89))
      | ~ m1_subset_1(D_89,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_819])).

tff(c_62304,plain,(
    ! [D_371] :
      ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),k3_lattices('#skF_3','#skF_6',D_371)) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4',D_371))
      | ~ m1_subset_1(D_371,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_820])).

tff(c_62493,plain,
    ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),k1_lattices('#skF_3','#skF_6','#skF_5')) = k3_lattices('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_62304])).

tff(c_62638,plain,(
    k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),k1_lattices('#skF_3','#skF_6','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8107,c_1343,c_62493])).

tff(c_175,plain,(
    ! [B_72] :
      ( k3_lattices('#skF_3',B_72,'#skF_5') = k3_lattices('#skF_3','#skF_5',B_72)
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_200,plain,(
    k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_128,c_175])).

tff(c_1962,plain,(
    k3_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = k3_lattices('#skF_3','#skF_5',k2_lattices('#skF_3','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1143,c_200])).

tff(c_1154,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_380,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_370])).

tff(c_394,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_380])).

tff(c_395,plain,(
    ! [B_79] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_79,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_394])).

tff(c_1769,plain,(
    ! [B_96] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_96,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_395])).

tff(c_1814,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_1769])).

tff(c_1838,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_1814])).

tff(c_285,plain,(
    k3_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') = k1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_260])).

tff(c_2013,plain,(
    k3_lattices('#skF_3','#skF_5',k2_lattices('#skF_3','#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_1838,c_1143,c_1143,c_285])).

tff(c_300,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_260])).

tff(c_40,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_310,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_6') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_40])).

tff(c_466,plain,(
    k1_lattices('#skF_3','#skF_4','#skF_5') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_310])).

tff(c_199,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_175])).

tff(c_217,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k3_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_199])).

tff(c_319,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_217])).

tff(c_472,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_4') = k1_lattices('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_319])).

tff(c_215,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_6') = k3_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_175])).

tff(c_305,plain,(
    k3_lattices('#skF_3','#skF_5','#skF_6') = k1_lattices('#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_215])).

tff(c_779,plain,(
    ! [C_88] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_88),k1_lattices('#skF_3','#skF_6','#skF_5')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_88,'#skF_6'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v11_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_728])).

tff(c_834,plain,(
    ! [C_88] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_88),k1_lattices('#skF_3','#skF_6','#skF_5')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_88,'#skF_6'))
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_44,c_779])).

tff(c_86879,plain,(
    ! [C_404] :
      ( k4_lattices('#skF_3',k3_lattices('#skF_3','#skF_5',C_404),k1_lattices('#skF_3','#skF_6','#skF_5')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3',C_404,'#skF_6'))
      | ~ m1_subset_1(C_404,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_834])).

tff(c_87086,plain,
    ( k4_lattices('#skF_3',k1_lattices('#skF_3','#skF_4','#skF_6'),k1_lattices('#skF_3','#skF_6','#skF_5')) = k3_lattices('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_86879])).

tff(c_87247,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62638,c_2013,c_1143,c_87086])).

tff(c_87249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_87247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 51.39/39.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.54/39.33  
% 51.54/39.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.54/39.34  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 51.54/39.34  
% 51.54/39.34  %Foreground sorts:
% 51.54/39.34  
% 51.54/39.34  
% 51.54/39.34  %Background operators:
% 51.54/39.34  
% 51.54/39.34  
% 51.54/39.34  %Foreground operators:
% 51.54/39.34  tff(l3_lattices, type, l3_lattices: $i > $o).
% 51.54/39.34  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 51.54/39.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 51.54/39.34  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 51.54/39.34  tff(l2_lattices, type, l2_lattices: $i > $o).
% 51.54/39.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 51.54/39.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 51.54/39.34  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 51.54/39.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 51.54/39.34  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 51.54/39.34  tff(l1_lattices, type, l1_lattices: $i > $o).
% 51.54/39.34  tff('#skF_5', type, '#skF_5': $i).
% 51.54/39.34  tff(v4_lattices, type, v4_lattices: $i > $o).
% 51.54/39.34  tff('#skF_6', type, '#skF_6': $i).
% 51.54/39.34  tff(v6_lattices, type, v6_lattices: $i > $o).
% 51.54/39.34  tff(v9_lattices, type, v9_lattices: $i > $o).
% 51.54/39.34  tff('#skF_3', type, '#skF_3': $i).
% 51.54/39.34  tff(v5_lattices, type, v5_lattices: $i > $o).
% 51.54/39.34  tff(v10_lattices, type, v10_lattices: $i > $o).
% 51.54/39.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 51.54/39.34  tff('#skF_4', type, '#skF_4': $i).
% 51.54/39.34  tff(v11_lattices, type, v11_lattices: $i > $o).
% 51.54/39.34  tff(v8_lattices, type, v8_lattices: $i > $o).
% 51.54/39.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 51.54/39.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 51.54/39.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 51.54/39.34  tff(v7_lattices, type, v7_lattices: $i > $o).
% 51.54/39.34  
% 51.54/39.36  tff(f_165, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_lattices)).
% 51.54/39.36  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 51.54/39.36  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 51.54/39.36  tff(f_88, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattices)).
% 51.54/39.36  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 51.54/39.36  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 51.54/39.36  tff(f_107, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 51.54/39.36  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 51.54/39.36  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k3_lattices(A, B, k4_lattices(A, C, D)) = k4_lattices(A, k3_lattices(A, B, C), k3_lattices(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_lattices)).
% 51.54/39.36  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_50, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_54, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 51.54/39.36  tff(c_62, plain, (![A_53]: (l1_lattices(A_53) | ~l3_lattices(A_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.54/39.36  tff(c_66, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_50, c_62])).
% 51.54/39.36  tff(c_42, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k4_lattices('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_84, plain, (![A_63, B_64, C_65]: (m1_subset_1(k4_lattices(A_63, B_64, C_65), u1_struct_0(A_63)) | ~m1_subset_1(C_65, u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_lattices(A_63) | ~v6_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_88])).
% 51.54/39.36  tff(c_87, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_84])).
% 51.54/39.36  tff(c_89, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_48, c_46, c_87])).
% 51.54/39.36  tff(c_90, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_89])).
% 51.54/39.36  tff(c_91, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_90])).
% 51.54/39.36  tff(c_122, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_91])).
% 51.54/39.36  tff(c_125, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_122])).
% 51.54/39.36  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_125])).
% 51.54/39.36  tff(c_129, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_90])).
% 51.54/39.36  tff(c_482, plain, (![A_82, B_83, C_84]: (k4_lattices(A_82, B_83, C_84)=k2_lattices(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_lattices(A_82) | ~v6_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_120])).
% 51.54/39.36  tff(c_494, plain, (![B_83]: (k4_lattices('#skF_3', B_83, '#skF_6')=k2_lattices('#skF_3', B_83, '#skF_6') | ~m1_subset_1(B_83, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_482])).
% 51.54/39.36  tff(c_510, plain, (![B_83]: (k4_lattices('#skF_3', B_83, '#skF_6')=k2_lattices('#skF_3', B_83, '#skF_6') | ~m1_subset_1(B_83, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_66, c_494])).
% 51.54/39.36  tff(c_1083, plain, (![B_91]: (k4_lattices('#skF_3', B_91, '#skF_6')=k2_lattices('#skF_3', B_91, '#skF_6') | ~m1_subset_1(B_91, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_510])).
% 51.54/39.36  tff(c_1143, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_1083])).
% 51.54/39.36  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 51.54/39.36  tff(c_57, plain, (![A_52]: (l2_lattices(A_52) | ~l3_lattices(A_52))), inference(cnfTransformation, [status(thm)], [f_94])).
% 51.54/39.36  tff(c_61, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_50, c_57])).
% 51.54/39.36  tff(c_130, plain, (![A_69, C_70, B_71]: (k3_lattices(A_69, C_70, B_71)=k3_lattices(A_69, B_71, C_70) | ~m1_subset_1(C_70, u1_struct_0(A_69)) | ~m1_subset_1(B_71, u1_struct_0(A_69)) | ~l2_lattices(A_69) | ~v4_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_60])).
% 51.54/39.36  tff(c_140, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_130])).
% 51.54/39.36  tff(c_154, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_140])).
% 51.54/39.36  tff(c_155, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_154])).
% 51.54/39.36  tff(c_164, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_155])).
% 51.54/39.36  tff(c_167, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_164])).
% 51.54/39.36  tff(c_170, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_167])).
% 51.54/39.36  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_170])).
% 51.54/39.36  tff(c_174, plain, (v4_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_155])).
% 51.54/39.36  tff(c_128, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 51.54/39.36  tff(c_222, plain, (![A_73, B_74, C_75]: (k3_lattices(A_73, B_74, C_75)=k1_lattices(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l2_lattices(A_73) | ~v4_lattices(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_107])).
% 51.54/39.36  tff(c_224, plain, (![B_74]: (k3_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6'))=k1_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_128, c_222])).
% 51.54/39.36  tff(c_239, plain, (![B_74]: (k3_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6'))=k1_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_61, c_224])).
% 51.54/39.36  tff(c_240, plain, (![B_74]: (k3_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6'))=k1_lattices('#skF_3', B_74, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_74, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_239])).
% 51.54/39.36  tff(c_3536, plain, (![B_108]: (k3_lattices('#skF_3', B_108, k2_lattices('#skF_3', '#skF_4', '#skF_6'))=k1_lattices('#skF_3', B_108, k2_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_108, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1143, c_240])).
% 51.54/39.36  tff(c_3636, plain, (k3_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))=k1_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_3536])).
% 51.54/39.36  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 51.54/39.36  tff(c_370, plain, (![A_78, B_79, C_80]: (k1_lattices(A_78, k2_lattices(A_78, B_79, C_80), C_80)=C_80 | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~v8_lattices(A_78) | ~l3_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 51.54/39.36  tff(c_382, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_370])).
% 51.54/39.36  tff(c_398, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_382])).
% 51.54/39.36  tff(c_399, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_398])).
% 51.54/39.36  tff(c_1144, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_399])).
% 51.54/39.36  tff(c_1147, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1144])).
% 51.54/39.36  tff(c_1150, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_1147])).
% 51.54/39.36  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1150])).
% 51.54/39.36  tff(c_1349, plain, (![B_92]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_92, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_92, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_399])).
% 51.54/39.36  tff(c_1417, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_1349])).
% 51.54/39.36  tff(c_234, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_6')=k1_lattices('#skF_3', B_74, '#skF_6') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_222])).
% 51.54/39.36  tff(c_250, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_6')=k1_lattices('#skF_3', B_74, '#skF_6') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_61, c_234])).
% 51.54/39.36  tff(c_416, plain, (![B_81]: (k3_lattices('#skF_3', B_81, '#skF_6')=k1_lattices('#skF_3', B_81, '#skF_6') | ~m1_subset_1(B_81, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_250])).
% 51.54/39.36  tff(c_441, plain, (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')=k1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_128, c_416])).
% 51.54/39.36  tff(c_1996, plain, (k3_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_1143, c_1143, c_441])).
% 51.54/39.36  tff(c_132, plain, (![B_71]: (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), B_71)=k3_lattices('#skF_3', B_71, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_128, c_130])).
% 51.54/39.36  tff(c_147, plain, (![B_71]: (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), B_71)=k3_lattices('#skF_3', B_71, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_132])).
% 51.54/39.36  tff(c_148, plain, (![B_71]: (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), B_71)=k3_lattices('#skF_3', B_71, k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_147])).
% 51.54/39.36  tff(c_7954, plain, (![B_140]: (k3_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), B_140)=k3_lattices('#skF_3', B_140, k2_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1(B_140, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_1143, c_1143, c_148])).
% 51.54/39.36  tff(c_8054, plain, (k3_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_6')=k3_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_7954])).
% 51.54/39.36  tff(c_8104, plain, (k1_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3636, c_1996, c_8054])).
% 51.54/39.36  tff(c_8107, plain, (k3_lattices('#skF_3', '#skF_6', k2_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8104, c_3636])).
% 51.54/39.36  tff(c_492, plain, (![B_83]: (k4_lattices('#skF_3', B_83, '#skF_5')=k2_lattices('#skF_3', B_83, '#skF_5') | ~m1_subset_1(B_83, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_482])).
% 51.54/39.36  tff(c_506, plain, (![B_83]: (k4_lattices('#skF_3', B_83, '#skF_5')=k2_lattices('#skF_3', B_83, '#skF_5') | ~m1_subset_1(B_83, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_66, c_492])).
% 51.54/39.36  tff(c_524, plain, (![B_85]: (k4_lattices('#skF_3', B_85, '#skF_5')=k2_lattices('#skF_3', B_85, '#skF_5') | ~m1_subset_1(B_85, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_506])).
% 51.54/39.36  tff(c_564, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_524])).
% 51.54/39.36  tff(c_619, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_6')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_42])).
% 51.54/39.36  tff(c_1279, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_619])).
% 51.54/39.36  tff(c_1343, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_564])).
% 51.54/39.36  tff(c_232, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_5')=k1_lattices('#skF_3', B_74, '#skF_5') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_222])).
% 51.54/39.36  tff(c_246, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_5')=k1_lattices('#skF_3', B_74, '#skF_5') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_61, c_232])).
% 51.54/39.36  tff(c_260, plain, (![B_76]: (k3_lattices('#skF_3', B_76, '#skF_5')=k1_lattices('#skF_3', B_76, '#skF_5') | ~m1_subset_1(B_76, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_246])).
% 51.54/39.36  tff(c_299, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_5')=k1_lattices('#skF_3', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_260])).
% 51.54/39.36  tff(c_236, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_4')=k1_lattices('#skF_3', B_74, '#skF_4') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_222])).
% 51.54/39.36  tff(c_254, plain, (![B_74]: (k3_lattices('#skF_3', B_74, '#skF_4')=k1_lattices('#skF_3', B_74, '#skF_4') | ~m1_subset_1(B_74, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_61, c_236])).
% 51.54/39.36  tff(c_328, plain, (![B_77]: (k3_lattices('#skF_3', B_77, '#skF_4')=k1_lattices('#skF_3', B_77, '#skF_4') | ~m1_subset_1(B_77, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_254])).
% 51.54/39.36  tff(c_368, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_4')=k1_lattices('#skF_3', '#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_328])).
% 51.54/39.36  tff(c_457, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_6')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_416])).
% 51.54/39.36  tff(c_144, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_130])).
% 51.54/39.36  tff(c_162, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_144])).
% 51.54/39.36  tff(c_163, plain, (![B_71]: (k3_lattices('#skF_3', B_71, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_162])).
% 51.54/39.36  tff(c_1566, plain, (![B_94]: (k3_lattices('#skF_3', B_94, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_163])).
% 51.54/39.36  tff(c_1608, plain, (k3_lattices('#skF_3', '#skF_6', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_1566])).
% 51.54/39.36  tff(c_1635, plain, (k1_lattices('#skF_3', '#skF_6', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_457, c_1608])).
% 51.54/39.36  tff(c_52, plain, (v11_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_728, plain, (![A_86, B_87, C_88, D_89]: (k4_lattices(A_86, k3_lattices(A_86, B_87, C_88), k3_lattices(A_86, B_87, D_89))=k3_lattices(A_86, B_87, k4_lattices(A_86, C_88, D_89)) | ~m1_subset_1(D_89, u1_struct_0(A_86)) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l3_lattices(A_86) | ~v11_lattices(A_86) | ~v10_lattices(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_140])).
% 51.54/39.36  tff(c_764, plain, (![D_89]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_4'), k3_lattices('#skF_3', '#skF_6', D_89))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', D_89)) | ~m1_subset_1(D_89, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_368, c_728])).
% 51.54/39.36  tff(c_819, plain, (![D_89]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_4'), k3_lattices('#skF_3', '#skF_6', D_89))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', D_89)) | ~m1_subset_1(D_89, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_44, c_48, c_764])).
% 51.54/39.36  tff(c_820, plain, (![D_89]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_6', '#skF_4'), k3_lattices('#skF_3', '#skF_6', D_89))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', D_89)) | ~m1_subset_1(D_89, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_819])).
% 51.54/39.36  tff(c_62304, plain, (![D_371]: (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), k3_lattices('#skF_3', '#skF_6', D_371))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', D_371)) | ~m1_subset_1(D_371, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1635, c_820])).
% 51.54/39.36  tff(c_62493, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), k1_lattices('#skF_3', '#skF_6', '#skF_5'))=k3_lattices('#skF_3', '#skF_6', k4_lattices('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_62304])).
% 51.54/39.36  tff(c_62638, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), k1_lattices('#skF_3', '#skF_6', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8107, c_1343, c_62493])).
% 51.54/39.36  tff(c_175, plain, (![B_72]: (k3_lattices('#skF_3', B_72, '#skF_5')=k3_lattices('#skF_3', '#skF_5', B_72) | ~m1_subset_1(B_72, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_155])).
% 51.54/39.36  tff(c_200, plain, (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_128, c_175])).
% 51.54/39.36  tff(c_1962, plain, (k3_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')=k3_lattices('#skF_3', '#skF_5', k2_lattices('#skF_3', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1143, c_200])).
% 51.54/39.36  tff(c_1154, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_399])).
% 51.54/39.36  tff(c_380, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_370])).
% 51.54/39.36  tff(c_394, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_380])).
% 51.54/39.36  tff(c_395, plain, (![B_79]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_79, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_79, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_394])).
% 51.54/39.36  tff(c_1769, plain, (![B_96]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_96, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_96, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1154, c_395])).
% 51.54/39.36  tff(c_1814, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_48, c_1769])).
% 51.54/39.36  tff(c_1838, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_1814])).
% 51.54/39.36  tff(c_285, plain, (k3_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')=k1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_128, c_260])).
% 51.54/39.36  tff(c_2013, plain, (k3_lattices('#skF_3', '#skF_5', k2_lattices('#skF_3', '#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1962, c_1838, c_1143, c_1143, c_285])).
% 51.54/39.36  tff(c_300, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_260])).
% 51.54/39.36  tff(c_40, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 51.54/39.36  tff(c_310, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_6')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_40])).
% 51.54/39.36  tff(c_466, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_5')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_310])).
% 51.54/39.36  tff(c_199, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_175])).
% 51.54/39.36  tff(c_217, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k3_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_199])).
% 51.54/39.36  tff(c_319, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_217])).
% 51.54/39.36  tff(c_472, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_4')=k1_lattices('#skF_3', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_319])).
% 51.54/39.36  tff(c_215, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_6')=k3_lattices('#skF_3', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_175])).
% 51.54/39.36  tff(c_305, plain, (k3_lattices('#skF_3', '#skF_5', '#skF_6')=k1_lattices('#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_215])).
% 51.54/39.36  tff(c_779, plain, (![C_88]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_88), k1_lattices('#skF_3', '#skF_6', '#skF_5'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_88, '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(C_88, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v11_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_305, c_728])).
% 51.54/39.36  tff(c_834, plain, (![C_88]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_88), k1_lattices('#skF_3', '#skF_6', '#skF_5'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_88, '#skF_6')) | ~m1_subset_1(C_88, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_44, c_779])).
% 51.54/39.36  tff(c_86879, plain, (![C_404]: (k4_lattices('#skF_3', k3_lattices('#skF_3', '#skF_5', C_404), k1_lattices('#skF_3', '#skF_6', '#skF_5'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', C_404, '#skF_6')) | ~m1_subset_1(C_404, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_834])).
% 51.54/39.36  tff(c_87086, plain, (k4_lattices('#skF_3', k1_lattices('#skF_3', '#skF_4', '#skF_6'), k1_lattices('#skF_3', '#skF_6', '#skF_5'))=k3_lattices('#skF_3', '#skF_5', k4_lattices('#skF_3', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_472, c_86879])).
% 51.54/39.36  tff(c_87247, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62638, c_2013, c_1143, c_87086])).
% 51.54/39.36  tff(c_87249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_87247])).
% 51.54/39.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.54/39.36  
% 51.54/39.36  Inference rules
% 51.54/39.36  ----------------------
% 51.54/39.36  #Ref     : 0
% 51.54/39.36  #Sup     : 18619
% 51.54/39.36  #Fact    : 0
% 51.54/39.36  #Define  : 0
% 51.54/39.36  #Split   : 5
% 51.54/39.36  #Chain   : 0
% 51.54/39.36  #Close   : 0
% 51.54/39.36  
% 51.54/39.36  Ordering : KBO
% 51.54/39.36  
% 51.54/39.36  Simplification rules
% 51.54/39.36  ----------------------
% 51.54/39.36  #Subsume      : 1519
% 51.54/39.36  #Demod        : 55669
% 51.54/39.36  #Tautology    : 3520
% 51.54/39.36  #SimpNegUnit  : 7242
% 51.54/39.36  #BackRed      : 77
% 51.54/39.36  
% 51.54/39.36  #Partial instantiations: 0
% 51.54/39.36  #Strategies tried      : 1
% 51.54/39.36  
% 51.54/39.36  Timing (in seconds)
% 51.54/39.36  ----------------------
% 51.54/39.36  Preprocessing        : 0.34
% 51.54/39.36  Parsing              : 0.18
% 51.54/39.36  CNF conversion       : 0.03
% 51.54/39.36  Main loop            : 38.23
% 51.54/39.36  Inferencing          : 3.27
% 51.54/39.36  Reduction            : 24.71
% 51.54/39.36  Demodulation         : 22.90
% 51.54/39.36  BG Simplification    : 0.50
% 51.54/39.36  Subsumption          : 8.74
% 51.54/39.36  Abstraction          : 1.15
% 51.54/39.36  MUC search           : 0.00
% 51.54/39.36  Cooper               : 0.00
% 51.54/39.36  Total                : 38.62
% 51.54/39.36  Index Insertion      : 0.00
% 51.54/39.36  Index Deletion       : 0.00
% 51.54/39.36  Index Matching       : 0.00
% 51.54/39.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
