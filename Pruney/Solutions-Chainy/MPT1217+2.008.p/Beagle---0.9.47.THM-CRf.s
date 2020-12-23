%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:20 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 735 expanded)
%              Number of leaves         :   39 ( 273 expanded)
%              Depth                    :   22
%              Number of atoms          :  323 (3212 expanded)
%              Number of equality atoms :   27 ( 198 expanded)
%              Maximal formula depth    :   17 (   4 average)
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

tff(f_182,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

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

tff(f_62,axiom,(
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

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_109,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_162,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,k4_lattices(A,B,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_52,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k7_lattices(A_13,B_14),u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l3_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_56,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_lattices(A_60,k2_lattices(A_60,B_61,C_62),C_62) = C_62
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ v8_lattices(A_60)
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    ! [B_61] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_61,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_95,plain,(
    ! [B_61] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_61,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87])).

tff(c_96,plain,(
    ! [B_61] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_61,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_95])).

tff(c_101,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_104,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_107,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_107])).

tff(c_111,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_458,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_lattices(A_84,B_85,C_86)
      | k2_lattices(A_84,B_85,C_86) != B_85
      | ~ m1_subset_1(C_86,u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l3_lattices(A_84)
      | ~ v9_lattices(A_84)
      | ~ v8_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_466,plain,(
    ! [B_85] :
      ( r1_lattices('#skF_3',B_85,'#skF_5')
      | k2_lattices('#skF_3',B_85,'#skF_5') != B_85
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_458])).

tff(c_474,plain,(
    ! [B_85] :
      ( r1_lattices('#skF_3',B_85,'#skF_5')
      | k2_lattices('#skF_3',B_85,'#skF_5') != B_85
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52,c_466])).

tff(c_475,plain,(
    ! [B_85] :
      ( r1_lattices('#skF_3',B_85,'#skF_5')
      | k2_lattices('#skF_3',B_85,'#skF_5') != B_85
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_474])).

tff(c_480,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_483,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_480])).

tff(c_486,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_483])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_486])).

tff(c_490,plain,(
    v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_46,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_561,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_563,plain,
    ( r1_lattices('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_561])).

tff(c_566,plain,
    ( r1_lattices('#skF_3','#skF_4','#skF_5')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_490,c_52,c_50,c_48,c_563])).

tff(c_567,plain,
    ( r1_lattices('#skF_3','#skF_4','#skF_5')
    | ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_566])).

tff(c_568,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_571,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_568])).

tff(c_574,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_571])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_574])).

tff(c_578,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_600,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_964,plain,(
    ! [A_131,B_132,B_133] :
      ( r3_lattices(A_131,B_132,k7_lattices(A_131,B_133))
      | ~ r1_lattices(A_131,B_132,k7_lattices(A_131,B_133))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ v9_lattices(A_131)
      | ~ v8_lattices(A_131)
      | ~ v6_lattices(A_131)
      | ~ m1_subset_1(B_133,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_24,c_600])).

tff(c_44,plain,(
    ~ r3_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_969,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_964,c_44])).

tff(c_973,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_578,c_111,c_490,c_969])).

tff(c_974,plain,
    ( ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_973])).

tff(c_975,plain,(
    ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_978,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_975])).

tff(c_981,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_978])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_981])).

tff(c_984,plain,(
    ~ r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_54,plain,(
    v17_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_985,plain,(
    m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_577,plain,(
    r1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_38,plain,(
    ! [A_22,B_26,C_28] :
      ( k2_lattices(A_22,B_26,C_28) = B_26
      | ~ r1_lattices(A_22,B_26,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_22))
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l3_lattices(A_22)
      | ~ v9_lattices(A_22)
      | ~ v8_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_581,plain,
    ( k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_577,c_38])).

tff(c_584,plain,
    ( k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_490,c_52,c_50,c_48,c_581])).

tff(c_585,plain,(
    k2_lattices('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_584])).

tff(c_134,plain,(
    ! [B_66] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_66,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_166,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_134])).

tff(c_586,plain,(
    k1_lattices('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_166])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_48] :
      ( l2_lattices(A_48)
      | ~ l3_lattices(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_112,plain,(
    ! [A_63,B_64,C_65] :
      ( k3_lattices(A_63,B_64,C_65) = k1_lattices(A_63,B_64,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l2_lattices(A_63)
      | ~ v4_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    ! [B_64] :
      ( k3_lattices('#skF_3',B_64,'#skF_5') = k1_lattices('#skF_3',B_64,'#skF_5')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_128,plain,(
    ! [B_64] :
      ( k3_lattices('#skF_3',B_64,'#skF_5') = k1_lattices('#skF_3',B_64,'#skF_5')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_120])).

tff(c_129,plain,(
    ! [B_64] :
      ( k3_lattices('#skF_3',B_64,'#skF_5') = k1_lattices('#skF_3',B_64,'#skF_5')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_128])).

tff(c_175,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_178,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_181,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_181])).

tff(c_186,plain,(
    ! [B_67] :
      ( k3_lattices('#skF_3',B_67,'#skF_5') = k1_lattices('#skF_3',B_67,'#skF_5')
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_218,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = k1_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_186])).

tff(c_591,plain,(
    k3_lattices('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_218])).

tff(c_695,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_lattices(A_97,k7_lattices(A_97,B_98),k7_lattices(A_97,C_99)) = k7_lattices(A_97,k3_lattices(A_97,B_98,C_99))
      | ~ m1_subset_1(C_99,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l3_lattices(A_97)
      | ~ v17_lattices(A_97)
      | ~ v10_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_lattices(A_29,k4_lattices(A_29,B_33,C_35),B_33)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v8_lattices(A_29)
      | ~ v6_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1141,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_lattices(A_138,k7_lattices(A_138,k3_lattices(A_138,B_139,C_140)),k7_lattices(A_138,B_139))
      | ~ m1_subset_1(k7_lattices(A_138,C_140),u1_struct_0(A_138))
      | ~ m1_subset_1(k7_lattices(A_138,B_139),u1_struct_0(A_138))
      | ~ l3_lattices(A_138)
      | ~ v8_lattices(A_138)
      | ~ v6_lattices(A_138)
      | v2_struct_0(A_138)
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | ~ l3_lattices(A_138)
      | ~ v17_lattices(A_138)
      | ~ v10_lattices(A_138)
      | v2_struct_0(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_40])).

tff(c_1188,plain,
    ( r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v17_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_1141])).

tff(c_1236,plain,
    ( r1_lattices('#skF_3',k7_lattices('#skF_3','#skF_5'),k7_lattices('#skF_3','#skF_4'))
    | ~ m1_subset_1(k7_lattices('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_578,c_111,c_52,c_985,c_1188])).

tff(c_1237,plain,(
    ~ m1_subset_1(k7_lattices('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_984,c_1236])).

tff(c_1267,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1237])).

tff(c_1270,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1267])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.68  
% 3.80/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.68  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.80/1.68  
% 3.80/1.68  %Foreground sorts:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Background operators:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Foreground operators:
% 3.80/1.68  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.80/1.68  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.80/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.68  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.80/1.68  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.80/1.68  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.80/1.68  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.68  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.80/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.80/1.68  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.80/1.68  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.80/1.68  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.80/1.68  tff(v17_lattices, type, v17_lattices: $i > $o).
% 3.80/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.68  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.80/1.68  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.80/1.68  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.80/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.68  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.80/1.68  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.68  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.68  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 3.80/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.68  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.80/1.68  
% 3.97/1.70  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_lattices)).
% 3.97/1.70  tff(f_71, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 3.97/1.70  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.97/1.70  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 3.97/1.70  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 3.97/1.70  tff(f_109, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.97/1.70  tff(f_77, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.97/1.70  tff(f_90, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.97/1.70  tff(f_162, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_lattices)).
% 3.97/1.70  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 3.97/1.70  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_52, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(k7_lattices(A_13, B_14), u1_struct_0(A_13)) | ~m1_subset_1(B_14, u1_struct_0(A_13)) | ~l3_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.70  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_56, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.97/1.70  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.97/1.70  tff(c_79, plain, (![A_60, B_61, C_62]: (k1_lattices(A_60, k2_lattices(A_60, B_61, C_62), C_62)=C_62 | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~v8_lattices(A_60) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.97/1.70  tff(c_87, plain, (![B_61]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_61, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_61, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_79])).
% 3.97/1.70  tff(c_95, plain, (![B_61]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_61, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_61, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87])).
% 3.97/1.70  tff(c_96, plain, (![B_61]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_61, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_61, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_95])).
% 3.97/1.70  tff(c_101, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_96])).
% 3.97/1.70  tff(c_104, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_101])).
% 3.97/1.70  tff(c_107, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_104])).
% 3.97/1.70  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_107])).
% 3.97/1.70  tff(c_111, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_96])).
% 3.97/1.70  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.97/1.70  tff(c_458, plain, (![A_84, B_85, C_86]: (r1_lattices(A_84, B_85, C_86) | k2_lattices(A_84, B_85, C_86)!=B_85 | ~m1_subset_1(C_86, u1_struct_0(A_84)) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l3_lattices(A_84) | ~v9_lattices(A_84) | ~v8_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.97/1.70  tff(c_466, plain, (![B_85]: (r1_lattices('#skF_3', B_85, '#skF_5') | k2_lattices('#skF_3', B_85, '#skF_5')!=B_85 | ~m1_subset_1(B_85, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_458])).
% 3.97/1.70  tff(c_474, plain, (![B_85]: (r1_lattices('#skF_3', B_85, '#skF_5') | k2_lattices('#skF_3', B_85, '#skF_5')!=B_85 | ~m1_subset_1(B_85, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52, c_466])).
% 3.97/1.70  tff(c_475, plain, (![B_85]: (r1_lattices('#skF_3', B_85, '#skF_5') | k2_lattices('#skF_3', B_85, '#skF_5')!=B_85 | ~m1_subset_1(B_85, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_474])).
% 3.97/1.70  tff(c_480, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_475])).
% 3.97/1.70  tff(c_483, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_480])).
% 3.97/1.70  tff(c_486, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_483])).
% 3.97/1.70  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_486])).
% 3.97/1.70  tff(c_490, plain, (v9_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_475])).
% 3.97/1.70  tff(c_46, plain, (r3_lattices('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_561, plain, (![A_89, B_90, C_91]: (r1_lattices(A_89, B_90, C_91) | ~r3_lattices(A_89, B_90, C_91) | ~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l3_lattices(A_89) | ~v9_lattices(A_89) | ~v8_lattices(A_89) | ~v6_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.97/1.70  tff(c_563, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_561])).
% 3.97/1.70  tff(c_566, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_490, c_52, c_50, c_48, c_563])).
% 3.97/1.70  tff(c_567, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5') | ~v6_lattices('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_566])).
% 3.97/1.70  tff(c_568, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_567])).
% 3.97/1.70  tff(c_571, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_568])).
% 3.97/1.70  tff(c_574, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_571])).
% 3.97/1.70  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_574])).
% 3.97/1.70  tff(c_578, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_567])).
% 3.97/1.70  tff(c_600, plain, (![A_92, B_93, C_94]: (r3_lattices(A_92, B_93, C_94) | ~r1_lattices(A_92, B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0(A_92)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l3_lattices(A_92) | ~v9_lattices(A_92) | ~v8_lattices(A_92) | ~v6_lattices(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.97/1.70  tff(c_964, plain, (![A_131, B_132, B_133]: (r3_lattices(A_131, B_132, k7_lattices(A_131, B_133)) | ~r1_lattices(A_131, B_132, k7_lattices(A_131, B_133)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~v9_lattices(A_131) | ~v8_lattices(A_131) | ~v6_lattices(A_131) | ~m1_subset_1(B_133, u1_struct_0(A_131)) | ~l3_lattices(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_24, c_600])).
% 3.97/1.70  tff(c_44, plain, (~r3_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_969, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_964, c_44])).
% 3.97/1.70  tff(c_973, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_578, c_111, c_490, c_969])).
% 3.97/1.70  tff(c_974, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_973])).
% 3.97/1.70  tff(c_975, plain, (~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_974])).
% 3.97/1.70  tff(c_978, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_975])).
% 3.97/1.70  tff(c_981, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_978])).
% 3.97/1.70  tff(c_983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_981])).
% 3.97/1.70  tff(c_984, plain, (~r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_974])).
% 3.97/1.70  tff(c_54, plain, (v17_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.97/1.70  tff(c_985, plain, (m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_974])).
% 3.97/1.70  tff(c_577, plain, (r1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_567])).
% 3.97/1.70  tff(c_38, plain, (![A_22, B_26, C_28]: (k2_lattices(A_22, B_26, C_28)=B_26 | ~r1_lattices(A_22, B_26, C_28) | ~m1_subset_1(C_28, u1_struct_0(A_22)) | ~m1_subset_1(B_26, u1_struct_0(A_22)) | ~l3_lattices(A_22) | ~v9_lattices(A_22) | ~v8_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.97/1.70  tff(c_581, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_577, c_38])).
% 3.97/1.70  tff(c_584, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_490, c_52, c_50, c_48, c_581])).
% 3.97/1.70  tff(c_585, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_584])).
% 3.97/1.70  tff(c_134, plain, (![B_66]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_66, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_66, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_96])).
% 3.97/1.70  tff(c_166, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_50, c_134])).
% 3.97/1.70  tff(c_586, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_585, c_166])).
% 3.97/1.70  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.97/1.70  tff(c_64, plain, (![A_48]: (l2_lattices(A_48) | ~l3_lattices(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.97/1.70  tff(c_68, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_52, c_64])).
% 3.97/1.70  tff(c_112, plain, (![A_63, B_64, C_65]: (k3_lattices(A_63, B_64, C_65)=k1_lattices(A_63, B_64, C_65) | ~m1_subset_1(C_65, u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l2_lattices(A_63) | ~v4_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.97/1.70  tff(c_120, plain, (![B_64]: (k3_lattices('#skF_3', B_64, '#skF_5')=k1_lattices('#skF_3', B_64, '#skF_5') | ~m1_subset_1(B_64, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_112])).
% 3.97/1.70  tff(c_128, plain, (![B_64]: (k3_lattices('#skF_3', B_64, '#skF_5')=k1_lattices('#skF_3', B_64, '#skF_5') | ~m1_subset_1(B_64, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_120])).
% 3.97/1.70  tff(c_129, plain, (![B_64]: (k3_lattices('#skF_3', B_64, '#skF_5')=k1_lattices('#skF_3', B_64, '#skF_5') | ~m1_subset_1(B_64, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_128])).
% 3.97/1.70  tff(c_175, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_129])).
% 3.97/1.70  tff(c_178, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_175])).
% 3.97/1.70  tff(c_181, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_178])).
% 3.97/1.70  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_181])).
% 3.97/1.70  tff(c_186, plain, (![B_67]: (k3_lattices('#skF_3', B_67, '#skF_5')=k1_lattices('#skF_3', B_67, '#skF_5') | ~m1_subset_1(B_67, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_129])).
% 3.97/1.70  tff(c_218, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')=k1_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_186])).
% 3.97/1.70  tff(c_591, plain, (k3_lattices('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_218])).
% 3.97/1.70  tff(c_695, plain, (![A_97, B_98, C_99]: (k4_lattices(A_97, k7_lattices(A_97, B_98), k7_lattices(A_97, C_99))=k7_lattices(A_97, k3_lattices(A_97, B_98, C_99)) | ~m1_subset_1(C_99, u1_struct_0(A_97)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l3_lattices(A_97) | ~v17_lattices(A_97) | ~v10_lattices(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.97/1.70  tff(c_40, plain, (![A_29, B_33, C_35]: (r1_lattices(A_29, k4_lattices(A_29, B_33, C_35), B_33) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~m1_subset_1(B_33, u1_struct_0(A_29)) | ~l3_lattices(A_29) | ~v8_lattices(A_29) | ~v6_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.97/1.70  tff(c_1141, plain, (![A_138, B_139, C_140]: (r1_lattices(A_138, k7_lattices(A_138, k3_lattices(A_138, B_139, C_140)), k7_lattices(A_138, B_139)) | ~m1_subset_1(k7_lattices(A_138, C_140), u1_struct_0(A_138)) | ~m1_subset_1(k7_lattices(A_138, B_139), u1_struct_0(A_138)) | ~l3_lattices(A_138) | ~v8_lattices(A_138) | ~v6_lattices(A_138) | v2_struct_0(A_138) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | ~l3_lattices(A_138) | ~v17_lattices(A_138) | ~v10_lattices(A_138) | v2_struct_0(A_138))), inference(superposition, [status(thm), theory('equality')], [c_695, c_40])).
% 3.97/1.70  tff(c_1188, plain, (r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v17_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_591, c_1141])).
% 3.97/1.70  tff(c_1236, plain, (r1_lattices('#skF_3', k7_lattices('#skF_3', '#skF_5'), k7_lattices('#skF_3', '#skF_4')) | ~m1_subset_1(k7_lattices('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_578, c_111, c_52, c_985, c_1188])).
% 3.97/1.70  tff(c_1237, plain, (~m1_subset_1(k7_lattices('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_984, c_1236])).
% 3.97/1.70  tff(c_1267, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1237])).
% 3.97/1.70  tff(c_1270, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1267])).
% 3.97/1.70  tff(c_1272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1270])).
% 3.97/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.70  
% 3.97/1.70  Inference rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Ref     : 0
% 3.97/1.70  #Sup     : 241
% 3.97/1.70  #Fact    : 0
% 3.97/1.70  #Define  : 0
% 3.97/1.70  #Split   : 13
% 3.97/1.70  #Chain   : 0
% 3.97/1.70  #Close   : 0
% 3.97/1.70  
% 3.97/1.70  Ordering : KBO
% 3.97/1.70  
% 3.97/1.70  Simplification rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Subsume      : 8
% 3.97/1.70  #Demod        : 322
% 3.97/1.70  #Tautology    : 126
% 3.97/1.70  #SimpNegUnit  : 88
% 3.97/1.70  #BackRed      : 2
% 3.97/1.70  
% 3.97/1.70  #Partial instantiations: 0
% 3.97/1.70  #Strategies tried      : 1
% 3.97/1.70  
% 3.97/1.70  Timing (in seconds)
% 3.97/1.70  ----------------------
% 3.97/1.71  Preprocessing        : 0.36
% 3.97/1.71  Parsing              : 0.19
% 3.97/1.71  CNF conversion       : 0.03
% 3.97/1.71  Main loop            : 0.52
% 3.97/1.71  Inferencing          : 0.20
% 3.97/1.71  Reduction            : 0.17
% 3.97/1.71  Demodulation         : 0.11
% 3.97/1.71  BG Simplification    : 0.03
% 3.97/1.71  Subsumption          : 0.09
% 3.97/1.71  Abstraction          : 0.03
% 3.97/1.71  MUC search           : 0.00
% 3.97/1.71  Cooper               : 0.00
% 3.97/1.71  Total                : 0.92
% 3.97/1.71  Index Insertion      : 0.00
% 3.97/1.71  Index Deletion       : 0.00
% 3.97/1.71  Index Matching       : 0.00
% 3.97/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
