%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 233 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  193 ( 705 expanded)
%              Number of equality atoms :   35 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

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
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_62,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    k4_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') != k5_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_47,plain,(
    ! [A_25] :
      ( l1_lattices(A_25)
      | ~ l3_lattices(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_42,plain,(
    v13_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    ! [A_36,B_37] :
      ( k3_lattices(A_36,k5_lattices(A_36),B_37) = B_37
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l3_lattices(A_36)
      | ~ v13_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_74,plain,
    ( k3_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v13_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_80,plain,
    ( k3_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_74])).

tff(c_81,plain,(
    k3_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_80])).

tff(c_24,plain,(
    ! [A_13] :
      ( m1_subset_1(k5_lattices(A_13),u1_struct_0(A_13))
      | ~ l1_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [A_26] :
      ( l2_lattices(A_26)
      | ~ l3_lattices(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_96,plain,(
    ! [A_40,B_41,C_42] :
      ( k3_lattices(A_40,B_41,C_42) = k1_lattices(A_40,B_41,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_40))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l2_lattices(A_40)
      | ~ v4_lattices(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_104,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_3',B_41,'#skF_4') = k1_lattices('#skF_3',B_41,'#skF_4')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_110,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_3',B_41,'#skF_4') = k1_lattices('#skF_3',B_41,'#skF_4')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_104])).

tff(c_111,plain,(
    ! [B_41] :
      ( k3_lattices('#skF_3',B_41,'#skF_4') = k1_lattices('#skF_3',B_41,'#skF_4')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_110])).

tff(c_112,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_131,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_134,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_134])).

tff(c_139,plain,(
    ! [B_46] :
      ( k3_lattices('#skF_3',B_46,'#skF_4') = k1_lattices('#skF_3',B_46,'#skF_4')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_151,plain,
    ( k3_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4')
    | ~ l1_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_165,plain,
    ( k1_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_81,c_151])).

tff(c_166,plain,(
    k1_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_165])).

tff(c_20,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_2'(A_2),u1_struct_0(A_2))
      | v9_lattices(A_2)
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_147,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4')
    | v9_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_139])).

tff(c_161,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4')
    | v9_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_147])).

tff(c_162,plain,
    ( k3_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_2'('#skF_3'),'#skF_4')
    | v9_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_161])).

tff(c_176,plain,(
    v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_194,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_lattices(A_50,B_51,k1_lattices(A_50,B_51,C_52)) = B_51
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ v9_lattices(A_50)
      | ~ l3_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,(
    ! [B_51] :
      ( k2_lattices('#skF_3',B_51,k1_lattices('#skF_3',B_51,'#skF_4')) = B_51
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_194])).

tff(c_208,plain,(
    ! [B_51] :
      ( k2_lattices('#skF_3',B_51,k1_lattices('#skF_3',B_51,'#skF_4')) = B_51
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_176,c_202])).

tff(c_210,plain,(
    ! [B_53] :
      ( k2_lattices('#skF_3',B_53,k1_lattices('#skF_3',B_53,'#skF_4')) = B_53
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_208])).

tff(c_219,plain,
    ( k2_lattices('#skF_3',k5_lattices('#skF_3'),k1_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4')) = k5_lattices('#skF_3')
    | ~ l1_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_210])).

tff(c_232,plain,
    ( k2_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = k5_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_166,c_219])).

tff(c_233,plain,(
    k2_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = k5_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_232])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_lattices(A_47,B_48,C_49) = k2_lattices(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_lattices(A_47)
      | ~ v6_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_186,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_3',B_48,'#skF_4') = k2_lattices('#skF_3',B_48,'#skF_4')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_192,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_3',B_48,'#skF_4') = k2_lattices('#skF_3',B_48,'#skF_4')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_186])).

tff(c_193,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_3',B_48,'#skF_4') = k2_lattices('#skF_3',B_48,'#skF_4')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_192])).

tff(c_243,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_246,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_243])).

tff(c_249,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_246])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_249])).

tff(c_254,plain,(
    ! [B_54] :
      ( k4_lattices('#skF_3',B_54,'#skF_4') = k2_lattices('#skF_3',B_54,'#skF_4')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_266,plain,
    ( k4_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = k2_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4')
    | ~ l1_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_254])).

tff(c_280,plain,
    ( k4_lattices('#skF_3',k5_lattices('#skF_3'),'#skF_4') = k5_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_233,c_266])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_280])).

tff(c_284,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_287,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_284])).

tff(c_290,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_287])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:19:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.25  
% 2.33/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.25  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.33/1.25  
% 2.33/1.25  %Foreground sorts:
% 2.33/1.25  
% 2.33/1.25  
% 2.33/1.25  %Background operators:
% 2.33/1.25  
% 2.33/1.25  
% 2.33/1.25  %Foreground operators:
% 2.33/1.25  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.33/1.25  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.33/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.25  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.33/1.25  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.33/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.33/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.25  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.33/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.25  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.33/1.25  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.33/1.25  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.33/1.25  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.33/1.25  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.33/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.25  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.33/1.25  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.33/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.25  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.33/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.25  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.33/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.25  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.33/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.25  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.33/1.25  
% 2.33/1.27  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 2.33/1.27  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.33/1.27  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.33/1.27  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k5_lattices(A), B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_lattices)).
% 2.33/1.27  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.33/1.27  tff(f_88, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.33/1.27  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 2.33/1.27  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.33/1.27  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_40, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_44, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.27  tff(c_36, plain, (k4_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')!=k5_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_47, plain, (![A_25]: (l1_lattices(A_25) | ~l3_lattices(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.27  tff(c_51, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_40, c_47])).
% 2.33/1.27  tff(c_42, plain, (v13_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.27  tff(c_66, plain, (![A_36, B_37]: (k3_lattices(A_36, k5_lattices(A_36), B_37)=B_37 | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l3_lattices(A_36) | ~v13_lattices(A_36) | ~v10_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.33/1.27  tff(c_74, plain, (k3_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')='#skF_4' | ~l3_lattices('#skF_3') | ~v13_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_66])).
% 2.33/1.27  tff(c_80, plain, (k3_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_74])).
% 2.33/1.27  tff(c_81, plain, (k3_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_80])).
% 2.33/1.27  tff(c_24, plain, (![A_13]: (m1_subset_1(k5_lattices(A_13), u1_struct_0(A_13)) | ~l1_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.27  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.27  tff(c_52, plain, (![A_26]: (l2_lattices(A_26) | ~l3_lattices(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.27  tff(c_56, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_40, c_52])).
% 2.33/1.27  tff(c_96, plain, (![A_40, B_41, C_42]: (k3_lattices(A_40, B_41, C_42)=k1_lattices(A_40, B_41, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_40)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l2_lattices(A_40) | ~v4_lattices(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.33/1.27  tff(c_104, plain, (![B_41]: (k3_lattices('#skF_3', B_41, '#skF_4')=k1_lattices('#skF_3', B_41, '#skF_4') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.33/1.27  tff(c_110, plain, (![B_41]: (k3_lattices('#skF_3', B_41, '#skF_4')=k1_lattices('#skF_3', B_41, '#skF_4') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_104])).
% 2.33/1.27  tff(c_111, plain, (![B_41]: (k3_lattices('#skF_3', B_41, '#skF_4')=k1_lattices('#skF_3', B_41, '#skF_4') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_110])).
% 2.33/1.27  tff(c_112, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_111])).
% 2.33/1.27  tff(c_131, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_112])).
% 2.33/1.27  tff(c_134, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_131])).
% 2.33/1.27  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_134])).
% 2.33/1.27  tff(c_139, plain, (![B_46]: (k3_lattices('#skF_3', B_46, '#skF_4')=k1_lattices('#skF_3', B_46, '#skF_4') | ~m1_subset_1(B_46, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_111])).
% 2.33/1.27  tff(c_151, plain, (k3_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4') | ~l1_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_139])).
% 2.33/1.27  tff(c_165, plain, (k1_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_81, c_151])).
% 2.33/1.27  tff(c_166, plain, (k1_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_165])).
% 2.33/1.27  tff(c_20, plain, (![A_2]: (m1_subset_1('#skF_2'(A_2), u1_struct_0(A_2)) | v9_lattices(A_2) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.27  tff(c_147, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4') | v9_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_139])).
% 2.33/1.27  tff(c_161, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4') | v9_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_147])).
% 2.33/1.27  tff(c_162, plain, (k3_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_2'('#skF_3'), '#skF_4') | v9_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_161])).
% 2.33/1.27  tff(c_176, plain, (v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_162])).
% 2.33/1.27  tff(c_194, plain, (![A_50, B_51, C_52]: (k2_lattices(A_50, B_51, k1_lattices(A_50, B_51, C_52))=B_51 | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~v9_lattices(A_50) | ~l3_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.27  tff(c_202, plain, (![B_51]: (k2_lattices('#skF_3', B_51, k1_lattices('#skF_3', B_51, '#skF_4'))=B_51 | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_194])).
% 2.33/1.27  tff(c_208, plain, (![B_51]: (k2_lattices('#skF_3', B_51, k1_lattices('#skF_3', B_51, '#skF_4'))=B_51 | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_176, c_202])).
% 2.33/1.27  tff(c_210, plain, (![B_53]: (k2_lattices('#skF_3', B_53, k1_lattices('#skF_3', B_53, '#skF_4'))=B_53 | ~m1_subset_1(B_53, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_208])).
% 2.33/1.27  tff(c_219, plain, (k2_lattices('#skF_3', k5_lattices('#skF_3'), k1_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4'))=k5_lattices('#skF_3') | ~l1_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_210])).
% 2.33/1.27  tff(c_232, plain, (k2_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')=k5_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_166, c_219])).
% 2.33/1.27  tff(c_233, plain, (k2_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')=k5_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_232])).
% 2.33/1.27  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.27  tff(c_178, plain, (![A_47, B_48, C_49]: (k4_lattices(A_47, B_48, C_49)=k2_lattices(A_47, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_lattices(A_47) | ~v6_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.33/1.27  tff(c_186, plain, (![B_48]: (k4_lattices('#skF_3', B_48, '#skF_4')=k2_lattices('#skF_3', B_48, '#skF_4') | ~m1_subset_1(B_48, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_178])).
% 2.33/1.27  tff(c_192, plain, (![B_48]: (k4_lattices('#skF_3', B_48, '#skF_4')=k2_lattices('#skF_3', B_48, '#skF_4') | ~m1_subset_1(B_48, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_186])).
% 2.33/1.27  tff(c_193, plain, (![B_48]: (k4_lattices('#skF_3', B_48, '#skF_4')=k2_lattices('#skF_3', B_48, '#skF_4') | ~m1_subset_1(B_48, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_192])).
% 2.33/1.27  tff(c_243, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_193])).
% 2.33/1.27  tff(c_246, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_243])).
% 2.33/1.27  tff(c_249, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_246])).
% 2.33/1.27  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_249])).
% 2.33/1.27  tff(c_254, plain, (![B_54]: (k4_lattices('#skF_3', B_54, '#skF_4')=k2_lattices('#skF_3', B_54, '#skF_4') | ~m1_subset_1(B_54, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_193])).
% 2.33/1.27  tff(c_266, plain, (k4_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')=k2_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4') | ~l1_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_254])).
% 2.33/1.27  tff(c_280, plain, (k4_lattices('#skF_3', k5_lattices('#skF_3'), '#skF_4')=k5_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_233, c_266])).
% 2.33/1.27  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_280])).
% 2.33/1.27  tff(c_284, plain, (~v9_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_162])).
% 2.33/1.27  tff(c_287, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_284])).
% 2.33/1.27  tff(c_290, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_287])).
% 2.33/1.27  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_290])).
% 2.33/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  Inference rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Ref     : 0
% 2.33/1.27  #Sup     : 49
% 2.33/1.27  #Fact    : 0
% 2.33/1.27  #Define  : 0
% 2.33/1.27  #Split   : 3
% 2.33/1.27  #Chain   : 0
% 2.33/1.27  #Close   : 0
% 2.33/1.27  
% 2.33/1.27  Ordering : KBO
% 2.33/1.27  
% 2.33/1.27  Simplification rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Subsume      : 2
% 2.33/1.27  #Demod        : 31
% 2.33/1.27  #Tautology    : 22
% 2.33/1.27  #SimpNegUnit  : 17
% 2.33/1.27  #BackRed      : 0
% 2.33/1.27  
% 2.33/1.27  #Partial instantiations: 0
% 2.33/1.27  #Strategies tried      : 1
% 2.33/1.27  
% 2.33/1.27  Timing (in seconds)
% 2.33/1.27  ----------------------
% 2.33/1.27  Preprocessing        : 0.31
% 2.33/1.27  Parsing              : 0.16
% 2.33/1.27  CNF conversion       : 0.02
% 2.33/1.27  Main loop            : 0.21
% 2.33/1.27  Inferencing          : 0.08
% 2.33/1.27  Reduction            : 0.06
% 2.33/1.27  Demodulation         : 0.04
% 2.33/1.27  BG Simplification    : 0.02
% 2.33/1.27  Subsumption          : 0.03
% 2.33/1.27  Abstraction          : 0.02
% 2.33/1.27  MUC search           : 0.00
% 2.33/1.27  Cooper               : 0.00
% 2.33/1.27  Total                : 0.56
% 2.33/1.27  Index Insertion      : 0.00
% 2.33/1.27  Index Deletion       : 0.00
% 2.33/1.27  Index Matching       : 0.00
% 2.33/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
