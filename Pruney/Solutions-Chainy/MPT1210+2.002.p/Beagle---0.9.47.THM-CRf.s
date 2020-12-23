%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:18 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 433 expanded)
%              Number of leaves         :   35 ( 164 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 (1569 expanded)
%              Number of equality atoms :   32 ( 137 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

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

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,B,k6_lattices(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattices)).

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v14_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k6_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k1_lattices(A,B,C) = B
                    & k1_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

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

tff(f_81,axiom,(
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

tff(f_132,axiom,(
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

tff(f_113,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    ! [A_37] :
      ( l2_lattices(A_37)
      | ~ l3_lattices(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_66,plain,(
    l2_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_52,plain,(
    v14_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_32,plain,(
    ! [A_23] :
      ( m1_subset_1(k6_lattices(A_23),u1_struct_0(A_23))
      | ~ l2_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_78,plain,(
    ! [A_50,C_51] :
      ( k1_lattices(A_50,k6_lattices(A_50),C_51) = k6_lattices(A_50)
      | ~ m1_subset_1(C_51,u1_struct_0(A_50))
      | ~ m1_subset_1(k6_lattices(A_50),u1_struct_0(A_50))
      | ~ v14_lattices(A_50)
      | ~ l2_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_88,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v14_lattices('#skF_4')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_95,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_52,c_88])).

tff(c_96,plain,
    ( k1_lattices('#skF_4',k6_lattices('#skF_4'),'#skF_5') = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_95])).

tff(c_97,plain,(
    ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_100,plain,
    ( ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_103,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_100])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_103])).

tff(c_107,plain,(
    m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_200,plain,(
    ! [A_56,C_57] :
      ( k1_lattices(A_56,C_57,k6_lattices(A_56)) = k6_lattices(A_56)
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ m1_subset_1(k6_lattices(A_56),u1_struct_0(A_56))
      | ~ v14_lattices(A_56)
      | ~ l2_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_212,plain,
    ( k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4')
    | ~ m1_subset_1(k6_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v14_lattices('#skF_4')
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_200])).

tff(c_223,plain,
    ( k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_52,c_107,c_212])).

tff(c_224,plain,(
    k1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = k6_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_223])).

tff(c_54,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_lattices(A_52,B_53,k1_lattices(A_52,B_53,C_54)) = B_53
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ v9_lattices(A_52)
      | ~ l3_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_126,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,'#skF_5')) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_137,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,'#skF_5')) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_126])).

tff(c_138,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,'#skF_5')) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_137])).

tff(c_147,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_151,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_154,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_151])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_154])).

tff(c_158,plain,(
    v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_116,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,k6_lattices('#skF_4'))) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_107,c_114])).

tff(c_129,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,k6_lattices('#skF_4'))) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_130,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_4',B_53,k1_lattices('#skF_4',B_53,k6_lattices('#skF_4'))) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_129])).

tff(c_235,plain,(
    ! [B_58] :
      ( k2_lattices('#skF_4',B_58,k1_lattices('#skF_4',B_58,k6_lattices('#skF_4'))) = B_58
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_130])).

tff(c_244,plain,
    ( k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_235])).

tff(c_251,plain,(
    k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_244])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_376,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_lattices(A_70,B_71,C_72)
      | k2_lattices(A_70,B_71,C_72) != B_71
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | ~ v9_lattices(A_70)
      | ~ v8_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_388,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,'#skF_5')
      | k2_lattices('#skF_4',B_71,'#skF_5') != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_376])).

tff(c_399,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,'#skF_5')
      | k2_lattices('#skF_4',B_71,'#skF_5') != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_50,c_388])).

tff(c_400,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,'#skF_5')
      | k2_lattices('#skF_4',B_71,'#skF_5') != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_399])).

tff(c_401,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_404,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_401])).

tff(c_407,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_404])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_407])).

tff(c_411,plain,(
    v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_378,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,k6_lattices('#skF_4'))
      | k2_lattices('#skF_4',B_71,k6_lattices('#skF_4')) != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_107,c_376])).

tff(c_391,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,k6_lattices('#skF_4'))
      | k2_lattices('#skF_4',B_71,k6_lattices('#skF_4')) != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_50,c_378])).

tff(c_392,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,k6_lattices('#skF_4'))
      | k2_lattices('#skF_4',B_71,k6_lattices('#skF_4')) != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_391])).

tff(c_457,plain,(
    ! [B_71] :
      ( r1_lattices('#skF_4',B_71,k6_lattices('#skF_4'))
      | k2_lattices('#skF_4',B_71,k6_lattices('#skF_4')) != B_71
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_392])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_510,plain,(
    ! [A_82,B_83,C_84] :
      ( r3_lattices(A_82,B_83,C_84)
      | ~ r1_lattices(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l3_lattices(A_82)
      | ~ v9_lattices(A_82)
      | ~ v8_lattices(A_82)
      | ~ v6_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_522,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,'#skF_5')
      | ~ r1_lattices('#skF_4',B_83,'#skF_5')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_510])).

tff(c_533,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,'#skF_5')
      | ~ r1_lattices('#skF_4',B_83,'#skF_5')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_158,c_50,c_522])).

tff(c_534,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,'#skF_5')
      | ~ r1_lattices('#skF_4',B_83,'#skF_5')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_533])).

tff(c_535,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_538,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_541,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_538])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_541])).

tff(c_545,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_512,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ r1_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_107,c_510])).

tff(c_525,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ r1_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_158,c_50,c_512])).

tff(c_526,plain,(
    ! [B_83] :
      ( r3_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ r1_lattices('#skF_4',B_83,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_4'))
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_525])).

tff(c_548,plain,(
    ! [B_85] :
      ( r3_lattices('#skF_4',B_85,k6_lattices('#skF_4'))
      | ~ r1_lattices('#skF_4',B_85,k6_lattices('#skF_4'))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_526])).

tff(c_46,plain,(
    ~ r3_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_553,plain,
    ( ~ r1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_548,c_46])).

tff(c_560,plain,(
    ~ r1_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_553])).

tff(c_563,plain,
    ( k2_lattices('#skF_4','#skF_5',k6_lattices('#skF_4')) != '#skF_5'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_457,c_560])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_251,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:46:56 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.77/1.40  
% 2.77/1.40  %Foreground sorts:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Background operators:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Foreground operators:
% 2.77/1.40  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.77/1.40  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.77/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.40  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.77/1.40  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.77/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.77/1.40  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.40  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.77/1.40  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.77/1.40  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.77/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.40  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.77/1.40  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.77/1.40  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.77/1.40  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.77/1.40  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.40  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.77/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.77/1.40  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.40  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.77/1.40  
% 2.77/1.42  tff(f_147, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, B, k6_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattices)).
% 2.77/1.42  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.77/1.42  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.77/1.42  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattices)).
% 2.77/1.42  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.77/1.42  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 2.77/1.42  tff(f_132, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.77/1.42  tff(f_113, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.77/1.42  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_50, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_62, plain, (![A_37]: (l2_lattices(A_37) | ~l3_lattices(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.77/1.42  tff(c_66, plain, (l2_lattices('#skF_4')), inference(resolution, [status(thm)], [c_50, c_62])).
% 2.77/1.42  tff(c_52, plain, (v14_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_32, plain, (![A_23]: (m1_subset_1(k6_lattices(A_23), u1_struct_0(A_23)) | ~l2_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.42  tff(c_78, plain, (![A_50, C_51]: (k1_lattices(A_50, k6_lattices(A_50), C_51)=k6_lattices(A_50) | ~m1_subset_1(C_51, u1_struct_0(A_50)) | ~m1_subset_1(k6_lattices(A_50), u1_struct_0(A_50)) | ~v14_lattices(A_50) | ~l2_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.42  tff(c_88, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v14_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_78])).
% 2.77/1.42  tff(c_95, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_52, c_88])).
% 2.77/1.42  tff(c_96, plain, (k1_lattices('#skF_4', k6_lattices('#skF_4'), '#skF_5')=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_95])).
% 2.77/1.42  tff(c_97, plain, (~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.77/1.42  tff(c_100, plain, (~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_97])).
% 2.77/1.42  tff(c_103, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_100])).
% 2.77/1.42  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_103])).
% 2.77/1.42  tff(c_107, plain, (m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_96])).
% 2.77/1.42  tff(c_200, plain, (![A_56, C_57]: (k1_lattices(A_56, C_57, k6_lattices(A_56))=k6_lattices(A_56) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~m1_subset_1(k6_lattices(A_56), u1_struct_0(A_56)) | ~v14_lattices(A_56) | ~l2_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.42  tff(c_212, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4') | ~m1_subset_1(k6_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v14_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_200])).
% 2.77/1.42  tff(c_223, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_52, c_107, c_212])).
% 2.77/1.42  tff(c_224, plain, (k1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))=k6_lattices('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_223])).
% 2.77/1.42  tff(c_54, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.42  tff(c_114, plain, (![A_52, B_53, C_54]: (k2_lattices(A_52, B_53, k1_lattices(A_52, B_53, C_54))=B_53 | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~v9_lattices(A_52) | ~l3_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.77/1.42  tff(c_126, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, '#skF_5'))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_114])).
% 2.77/1.42  tff(c_137, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, '#skF_5'))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_126])).
% 2.77/1.42  tff(c_138, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, '#skF_5'))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_137])).
% 2.77/1.42  tff(c_147, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_138])).
% 2.77/1.42  tff(c_151, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.77/1.42  tff(c_154, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_151])).
% 2.77/1.42  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_154])).
% 2.77/1.42  tff(c_158, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_138])).
% 2.77/1.42  tff(c_116, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, k6_lattices('#skF_4')))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_107, c_114])).
% 2.77/1.42  tff(c_129, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, k6_lattices('#skF_4')))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_116])).
% 2.77/1.42  tff(c_130, plain, (![B_53]: (k2_lattices('#skF_4', B_53, k1_lattices('#skF_4', B_53, k6_lattices('#skF_4')))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_129])).
% 2.77/1.42  tff(c_235, plain, (![B_58]: (k2_lattices('#skF_4', B_58, k1_lattices('#skF_4', B_58, k6_lattices('#skF_4')))=B_58 | ~m1_subset_1(B_58, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_130])).
% 2.77/1.42  tff(c_244, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_235])).
% 2.77/1.42  tff(c_251, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_244])).
% 2.77/1.42  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.42  tff(c_376, plain, (![A_70, B_71, C_72]: (r1_lattices(A_70, B_71, C_72) | k2_lattices(A_70, B_71, C_72)!=B_71 | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l3_lattices(A_70) | ~v9_lattices(A_70) | ~v8_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.42  tff(c_388, plain, (![B_71]: (r1_lattices('#skF_4', B_71, '#skF_5') | k2_lattices('#skF_4', B_71, '#skF_5')!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_376])).
% 2.77/1.42  tff(c_399, plain, (![B_71]: (r1_lattices('#skF_4', B_71, '#skF_5') | k2_lattices('#skF_4', B_71, '#skF_5')!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_50, c_388])).
% 2.77/1.42  tff(c_400, plain, (![B_71]: (r1_lattices('#skF_4', B_71, '#skF_5') | k2_lattices('#skF_4', B_71, '#skF_5')!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_399])).
% 2.77/1.42  tff(c_401, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_400])).
% 2.77/1.42  tff(c_404, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_4, c_401])).
% 2.77/1.42  tff(c_407, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_404])).
% 2.77/1.42  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_407])).
% 2.77/1.42  tff(c_411, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_400])).
% 2.77/1.42  tff(c_378, plain, (![B_71]: (r1_lattices('#skF_4', B_71, k6_lattices('#skF_4')) | k2_lattices('#skF_4', B_71, k6_lattices('#skF_4'))!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_107, c_376])).
% 2.77/1.42  tff(c_391, plain, (![B_71]: (r1_lattices('#skF_4', B_71, k6_lattices('#skF_4')) | k2_lattices('#skF_4', B_71, k6_lattices('#skF_4'))!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_50, c_378])).
% 2.77/1.42  tff(c_392, plain, (![B_71]: (r1_lattices('#skF_4', B_71, k6_lattices('#skF_4')) | k2_lattices('#skF_4', B_71, k6_lattices('#skF_4'))!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_391])).
% 2.77/1.42  tff(c_457, plain, (![B_71]: (r1_lattices('#skF_4', B_71, k6_lattices('#skF_4')) | k2_lattices('#skF_4', B_71, k6_lattices('#skF_4'))!=B_71 | ~m1_subset_1(B_71, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_392])).
% 2.77/1.42  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.42  tff(c_510, plain, (![A_82, B_83, C_84]: (r3_lattices(A_82, B_83, C_84) | ~r1_lattices(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l3_lattices(A_82) | ~v9_lattices(A_82) | ~v8_lattices(A_82) | ~v6_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.42  tff(c_522, plain, (![B_83]: (r3_lattices('#skF_4', B_83, '#skF_5') | ~r1_lattices('#skF_4', B_83, '#skF_5') | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_510])).
% 2.77/1.42  tff(c_533, plain, (![B_83]: (r3_lattices('#skF_4', B_83, '#skF_5') | ~r1_lattices('#skF_4', B_83, '#skF_5') | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_158, c_50, c_522])).
% 2.77/1.42  tff(c_534, plain, (![B_83]: (r3_lattices('#skF_4', B_83, '#skF_5') | ~r1_lattices('#skF_4', B_83, '#skF_5') | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_533])).
% 2.77/1.42  tff(c_535, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_534])).
% 2.77/1.42  tff(c_538, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_535])).
% 2.77/1.42  tff(c_541, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_538])).
% 2.77/1.42  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_541])).
% 2.77/1.42  tff(c_545, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_534])).
% 2.77/1.42  tff(c_512, plain, (![B_83]: (r3_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~r1_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_107, c_510])).
% 2.77/1.42  tff(c_525, plain, (![B_83]: (r3_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~r1_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_158, c_50, c_512])).
% 2.77/1.42  tff(c_526, plain, (![B_83]: (r3_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~r1_lattices('#skF_4', B_83, k6_lattices('#skF_4')) | ~m1_subset_1(B_83, u1_struct_0('#skF_4')) | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_525])).
% 2.77/1.42  tff(c_548, plain, (![B_85]: (r3_lattices('#skF_4', B_85, k6_lattices('#skF_4')) | ~r1_lattices('#skF_4', B_85, k6_lattices('#skF_4')) | ~m1_subset_1(B_85, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_526])).
% 2.77/1.42  tff(c_46, plain, (~r3_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.77/1.42  tff(c_553, plain, (~r1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_548, c_46])).
% 2.77/1.42  tff(c_560, plain, (~r1_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_553])).
% 2.77/1.42  tff(c_563, plain, (k2_lattices('#skF_4', '#skF_5', k6_lattices('#skF_4'))!='#skF_5' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_457, c_560])).
% 2.77/1.42  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_251, c_563])).
% 2.77/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  Inference rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Ref     : 0
% 2.77/1.42  #Sup     : 99
% 2.77/1.42  #Fact    : 0
% 2.77/1.42  #Define  : 0
% 2.77/1.42  #Split   : 7
% 2.77/1.42  #Chain   : 0
% 2.77/1.42  #Close   : 0
% 2.77/1.42  
% 2.77/1.42  Ordering : KBO
% 2.77/1.42  
% 2.77/1.42  Simplification rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Subsume      : 6
% 2.77/1.42  #Demod        : 113
% 2.77/1.42  #Tautology    : 56
% 2.77/1.42  #SimpNegUnit  : 37
% 2.77/1.42  #BackRed      : 0
% 2.77/1.42  
% 2.77/1.42  #Partial instantiations: 0
% 2.77/1.42  #Strategies tried      : 1
% 2.77/1.42  
% 2.77/1.42  Timing (in seconds)
% 2.77/1.42  ----------------------
% 2.77/1.42  Preprocessing        : 0.31
% 2.77/1.42  Parsing              : 0.16
% 2.77/1.42  CNF conversion       : 0.02
% 2.77/1.42  Main loop            : 0.33
% 2.77/1.42  Inferencing          : 0.12
% 2.77/1.42  Reduction            : 0.09
% 2.77/1.42  Demodulation         : 0.06
% 2.77/1.42  BG Simplification    : 0.02
% 2.77/1.42  Subsumption          : 0.06
% 2.77/1.42  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.68
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
