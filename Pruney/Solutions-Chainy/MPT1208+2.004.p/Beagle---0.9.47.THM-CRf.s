%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :  200 (2923 expanded)
%              Number of leaves         :   44 ( 991 expanded)
%              Depth                    :   30
%              Number of atoms          :  586 (10675 expanded)
%              Number of equality atoms :   84 (1760 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

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

tff(f_246,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

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

tff(f_120,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_81,axiom,(
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

tff(f_188,axiom,(
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

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_169,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_152,axiom,(
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

tff(f_231,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattices(A,B,C)
                   => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

tff(f_207,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_68,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_72,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [A_78] :
      ( l2_lattices(A_78)
      | ~ l3_lattices(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_79,plain,(
    l2_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_42,plain,(
    ! [A_37] :
      ( m1_subset_1(k6_lattices(A_37),u1_struct_0(A_37))
      | ~ l2_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    v14_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_210,plain,(
    ! [A_102,C_103] :
      ( k1_lattices(A_102,C_103,k6_lattices(A_102)) = k6_lattices(A_102)
      | ~ m1_subset_1(C_103,u1_struct_0(A_102))
      | ~ m1_subset_1(k6_lattices(A_102),u1_struct_0(A_102))
      | ~ v14_lattices(A_102)
      | ~ l2_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_226,plain,
    ( k1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = k6_lattices('#skF_6')
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6'))
    | ~ v14_lattices('#skF_6')
    | ~ l2_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_210])).

tff(c_236,plain,
    ( k1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = k6_lattices('#skF_6')
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_70,c_226])).

tff(c_237,plain,
    ( k1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = k6_lattices('#skF_6')
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_236])).

tff(c_238,plain,(
    ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_241,plain,
    ( ~ l2_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_244,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_244])).

tff(c_248,plain,(
    m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_247,plain,(
    k1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = k6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_36,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_5'(A_23),u1_struct_0(A_23))
      | v9_lattices(A_23)
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_lattices(A_98,k2_lattices(A_98,B_99,C_100),C_100) = C_100
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ v8_lattices(A_98)
      | ~ l3_lattices(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    ! [B_99] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_99,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_126,plain,(
    ! [B_99] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_99,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_116])).

tff(c_127,plain,(
    ! [B_99] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_99,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_126])).

tff(c_128,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_131,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_134,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_134])).

tff(c_139,plain,(
    ! [B_101] :
      ( k1_lattices('#skF_6',k2_lattices('#skF_6',B_101,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_159,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_5'('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_189,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_5'('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_159])).

tff(c_190,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_5'('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_189])).

tff(c_208,plain,(
    v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_373,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_lattices(A_112,B_113,k1_lattices(A_112,B_113,C_114)) = B_113
      | ~ m1_subset_1(C_114,u1_struct_0(A_112))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ v9_lattices(A_112)
      | ~ l3_lattices(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_375,plain,(
    ! [B_113] :
      ( k2_lattices('#skF_6',B_113,k1_lattices('#skF_6',B_113,k6_lattices('#skF_6'))) = B_113
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_248,c_373])).

tff(c_394,plain,(
    ! [B_113] :
      ( k2_lattices('#skF_6',B_113,k1_lattices('#skF_6',B_113,k6_lattices('#skF_6'))) = B_113
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_208,c_375])).

tff(c_500,plain,(
    ! [B_116] :
      ( k2_lattices('#skF_6',B_116,k1_lattices('#skF_6',B_116,k6_lattices('#skF_6'))) = B_116
      | ~ m1_subset_1(B_116,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_394])).

tff(c_522,plain,
    ( k2_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_500])).

tff(c_535,plain,(
    k2_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_522])).

tff(c_138,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_1276,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_lattices(A_151,B_152,C_153)
      | k2_lattices(A_151,B_152,C_153) != B_152
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l3_lattices(A_151)
      | ~ v9_lattices(A_151)
      | ~ v8_lattices(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1278,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,k6_lattices('#skF_6'))
      | k2_lattices('#skF_6',B_152,k6_lattices('#skF_6')) != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_248,c_1276])).

tff(c_1297,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,k6_lattices('#skF_6'))
      | k2_lattices('#skF_6',B_152,k6_lattices('#skF_6')) != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_1278])).

tff(c_1298,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,k6_lattices('#skF_6'))
      | k2_lattices('#skF_6',B_152,k6_lattices('#skF_6')) != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1297])).

tff(c_80,plain,(
    ! [A_79] :
      ( l1_lattices(A_79)
      | ~ l3_lattices(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_84,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_40,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k2_lattices(A_34,B_35,C_36),u1_struct_0(A_34))
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_1] :
      ( v7_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1294,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,'#skF_7')
      | k2_lattices('#skF_6',B_152,'#skF_7') != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_1276])).

tff(c_1308,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,'#skF_7')
      | k2_lattices('#skF_6',B_152,'#skF_7') != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_1294])).

tff(c_1310,plain,(
    ! [B_154] :
      ( r1_lattices('#skF_6',B_154,'#skF_7')
      | k2_lattices('#skF_6',B_154,'#skF_7') != B_154
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1308])).

tff(c_1374,plain,
    ( r1_lattices('#skF_6','#skF_7','#skF_7')
    | k2_lattices('#skF_6','#skF_7','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_66,c_1310])).

tff(c_1375,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_7') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1374])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_558,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_lattices(A_117,B_118,C_119) = k2_lattices(A_117,B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_lattices(A_117)
      | ~ v6_lattices(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_576,plain,(
    ! [B_118] :
      ( k4_lattices('#skF_6',B_118,'#skF_7') = k2_lattices('#skF_6',B_118,'#skF_7')
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_558])).

tff(c_590,plain,(
    ! [B_118] :
      ( k4_lattices('#skF_6',B_118,'#skF_7') = k2_lattices('#skF_6',B_118,'#skF_7')
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_576])).

tff(c_591,plain,(
    ! [B_118] :
      ( k4_lattices('#skF_6',B_118,'#skF_7') = k2_lattices('#skF_6',B_118,'#skF_7')
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_590])).

tff(c_592,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_595,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_592])).

tff(c_598,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_595])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_598])).

tff(c_602,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_750,plain,(
    ! [A_122,B_123,C_124] :
      ( r3_lattices(A_122,B_123,B_123)
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l3_lattices(A_122)
      | ~ v9_lattices(A_122)
      | ~ v8_lattices(A_122)
      | ~ v6_lattices(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_752,plain,(
    ! [B_123] :
      ( r3_lattices('#skF_6',B_123,B_123)
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_248,c_750])).

tff(c_771,plain,(
    ! [B_123] :
      ( r3_lattices('#skF_6',B_123,B_123)
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_138,c_208,c_68,c_752])).

tff(c_784,plain,(
    ! [B_125] :
      ( r3_lattices('#skF_6',B_125,B_125)
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_771])).

tff(c_839,plain,(
    r3_lattices('#skF_6','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_784])).

tff(c_1401,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_lattices(A_156,B_157,C_158)
      | ~ r3_lattices(A_156,B_157,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l3_lattices(A_156)
      | ~ v9_lattices(A_156)
      | ~ v8_lattices(A_156)
      | ~ v6_lattices(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1411,plain,
    ( r1_lattices('#skF_6','#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_839,c_1401])).

tff(c_1427,plain,
    ( r1_lattices('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_138,c_208,c_68,c_66,c_1411])).

tff(c_1428,plain,(
    r1_lattices('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1427])).

tff(c_58,plain,(
    ! [A_48,B_52,C_54] :
      ( k2_lattices(A_48,B_52,C_54) = B_52
      | ~ r1_lattices(A_48,B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l3_lattices(A_48)
      | ~ v9_lattices(A_48)
      | ~ v8_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1430,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1428,c_58])).

tff(c_1435,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_66,c_1430])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1375,c_1435])).

tff(c_1438,plain,(
    r1_lattices('#skF_6','#skF_7','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1374])).

tff(c_1441,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1438,c_58])).

tff(c_1446,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_66,c_1441])).

tff(c_1447,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1446])).

tff(c_1988,plain,(
    ! [A_185,B_186,D_187,C_188] :
      ( r1_lattices(A_185,k2_lattices(A_185,B_186,D_187),k2_lattices(A_185,C_188,D_187))
      | ~ r1_lattices(A_185,B_186,C_188)
      | ~ m1_subset_1(D_187,u1_struct_0(A_185))
      | ~ m1_subset_1(C_188,u1_struct_0(A_185))
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l3_lattices(A_185)
      | ~ v9_lattices(A_185)
      | ~ v8_lattices(A_185)
      | ~ v7_lattices(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1995,plain,(
    ! [C_188] :
      ( r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_188,'#skF_7'))
      | ~ r1_lattices('#skF_6','#skF_7',C_188)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v7_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_1988])).

tff(c_2044,plain,(
    ! [C_188] :
      ( r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_188,'#skF_7'))
      | ~ r1_lattices('#skF_6','#skF_7',C_188)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_6'))
      | ~ v7_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_66,c_66,c_1995])).

tff(c_2045,plain,(
    ! [C_188] :
      ( r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_188,'#skF_7'))
      | ~ r1_lattices('#skF_6','#skF_7',C_188)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_6'))
      | ~ v7_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2044])).

tff(c_2073,plain,(
    ~ v7_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2045])).

tff(c_2076,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_2073])).

tff(c_2079,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_2076])).

tff(c_2081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2079])).

tff(c_2104,plain,(
    ! [C_190] :
      ( r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_190,'#skF_7'))
      | ~ r1_lattices('#skF_6','#skF_7',C_190)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_2045])).

tff(c_2106,plain,(
    ! [C_190] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_190,'#skF_7')) = '#skF_7'
      | ~ m1_subset_1(k2_lattices('#skF_6',C_190,'#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_lattices('#skF_6','#skF_7',C_190)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2104,c_58])).

tff(c_2114,plain,(
    ! [C_190] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_190,'#skF_7')) = '#skF_7'
      | ~ m1_subset_1(k2_lattices('#skF_6',C_190,'#skF_7'),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r1_lattices('#skF_6','#skF_7',C_190)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_208,c_68,c_66,c_2106])).

tff(c_2576,plain,(
    ! [C_215] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_215,'#skF_7')) = '#skF_7'
      | ~ m1_subset_1(k2_lattices('#skF_6',C_215,'#skF_7'),u1_struct_0('#skF_6'))
      | ~ r1_lattices('#skF_6','#skF_7',C_215)
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2114])).

tff(c_2583,plain,(
    ! [B_35] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',B_35,'#skF_7')) = '#skF_7'
      | ~ r1_lattices('#skF_6','#skF_7',B_35)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_2576])).

tff(c_2588,plain,(
    ! [B_35] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',B_35,'#skF_7')) = '#skF_7'
      | ~ r1_lattices('#skF_6','#skF_7',B_35)
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_2583])).

tff(c_2590,plain,(
    ! [B_216] :
      ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',B_216,'#skF_7')) = '#skF_7'
      | ~ r1_lattices('#skF_6','#skF_7',B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2588])).

tff(c_2625,plain,
    ( k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7')) = '#skF_7'
    | ~ r1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) ),
    inference(resolution,[status(thm)],[c_248,c_2590])).

tff(c_2691,plain,(
    ~ r1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2625])).

tff(c_2694,plain,
    ( k2_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1298,c_2691])).

tff(c_2698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_535,c_2694])).

tff(c_2700,plain,(
    r1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_2082,plain,(
    ! [C_188] :
      ( r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',C_188,'#skF_7'))
      | ~ r1_lattices('#skF_6','#skF_7',C_188)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_2045])).

tff(c_681,plain,(
    ! [B_121] :
      ( k4_lattices('#skF_6',B_121,'#skF_7') = k2_lattices('#skF_6',B_121,'#skF_7')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_712,plain,
    ( k4_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') = k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7')
    | ~ l2_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_681])).

tff(c_743,plain,
    ( k4_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') = k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_712])).

tff(c_744,plain,(
    k4_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') = k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_743])).

tff(c_64,plain,(
    k4_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_841,plain,(
    k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_64])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1534,plain,(
    ! [B_162] :
      ( r1_lattices('#skF_6',B_162,k6_lattices('#skF_6'))
      | k2_lattices('#skF_6',B_162,k6_lattices('#skF_6')) != B_162
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1297])).

tff(c_60,plain,(
    ! [C_61,B_59,A_55] :
      ( C_61 = B_59
      | ~ r1_lattices(A_55,C_61,B_59)
      | ~ r1_lattices(A_55,B_59,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_55))
      | ~ m1_subset_1(B_59,u1_struct_0(A_55))
      | ~ l2_lattices(A_55)
      | ~ v4_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1538,plain,(
    ! [B_162] :
      ( k6_lattices('#skF_6') = B_162
      | ~ r1_lattices('#skF_6',k6_lattices('#skF_6'),B_162)
      | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l2_lattices('#skF_6')
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | k2_lattices('#skF_6',B_162,k6_lattices('#skF_6')) != B_162
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1534,c_60])).

tff(c_1545,plain,(
    ! [B_162] :
      ( k6_lattices('#skF_6') = B_162
      | ~ r1_lattices('#skF_6',k6_lattices('#skF_6'),B_162)
      | ~ v4_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | k2_lattices('#skF_6',B_162,k6_lattices('#skF_6')) != B_162
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_248,c_1538])).

tff(c_1546,plain,(
    ! [B_162] :
      ( k6_lattices('#skF_6') = B_162
      | ~ r1_lattices('#skF_6',k6_lattices('#skF_6'),B_162)
      | ~ v4_lattices('#skF_6')
      | k2_lattices('#skF_6',B_162,k6_lattices('#skF_6')) != B_162
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1545])).

tff(c_1547,plain,(
    ~ v4_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_1550,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1547])).

tff(c_1553,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1550])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1553])).

tff(c_1557,plain,(
    v4_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_167,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7'
    | ~ l2_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_139])).

tff(c_197,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_167])).

tff(c_198,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_197])).

tff(c_391,plain,(
    ! [B_113] :
      ( k2_lattices('#skF_6',B_113,k1_lattices('#skF_6',B_113,'#skF_7')) = B_113
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_373])).

tff(c_405,plain,(
    ! [B_113] :
      ( k2_lattices('#skF_6',B_113,k1_lattices('#skF_6',B_113,'#skF_7')) = B_113
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_208,c_391])).

tff(c_407,plain,(
    ! [B_115] :
      ( k2_lattices('#skF_6',B_115,k1_lattices('#skF_6',B_115,'#skF_7')) = B_115
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_405])).

tff(c_415,plain,(
    ! [B_35,C_36] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k1_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),'#skF_7')) = k2_lattices('#skF_6',B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_407])).

tff(c_441,plain,(
    ! [B_35,C_36] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k1_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),'#skF_7')) = k2_lattices('#skF_6',B_35,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_415])).

tff(c_3210,plain,(
    ! [B_253,C_254] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_253,C_254),k1_lattices('#skF_6',k2_lattices('#skF_6',B_253,C_254),'#skF_7')) = k2_lattices('#skF_6',B_253,C_254)
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_441])).

tff(c_3333,plain,
    ( k2_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') = k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_3210])).

tff(c_3388,plain,(
    k2_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') = k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_66,c_3333])).

tff(c_792,plain,(
    ! [B_35,C_36] :
      ( r3_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k2_lattices('#skF_6',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_784])).

tff(c_817,plain,(
    ! [B_35,C_36] :
      ( r3_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k2_lattices('#skF_6',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_792])).

tff(c_818,plain,(
    ! [B_35,C_36] :
      ( r3_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k2_lattices('#skF_6',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_817])).

tff(c_1493,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_lattices(A_159,B_160,C_161)
      | ~ r3_lattices(A_159,B_160,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l3_lattices(A_159)
      | ~ v9_lattices(A_159)
      | ~ v8_lattices(A_159)
      | ~ v6_lattices(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1497,plain,(
    ! [B_35,C_36] :
      ( r1_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k2_lattices('#skF_6',B_35,C_36))
      | ~ m1_subset_1(k2_lattices('#skF_6',B_35,C_36),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_818,c_1493])).

tff(c_1507,plain,(
    ! [B_35,C_36] :
      ( r1_lattices('#skF_6',k2_lattices('#skF_6',B_35,C_36),k2_lattices('#skF_6',B_35,C_36))
      | ~ m1_subset_1(k2_lattices('#skF_6',B_35,C_36),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_138,c_208,c_68,c_1497])).

tff(c_3697,plain,(
    ! [B_268,C_269] :
      ( r1_lattices('#skF_6',k2_lattices('#skF_6',B_268,C_269),k2_lattices('#skF_6',B_268,C_269))
      | ~ m1_subset_1(k2_lattices('#skF_6',B_268,C_269),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_269,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_268,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1507])).

tff(c_3712,plain,
    ( r1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),k2_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7'))
    | ~ m1_subset_1(k2_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3388,c_3697])).

tff(c_3810,plain,
    ( r1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'))
    | ~ m1_subset_1(k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3388,c_3388,c_3712])).

tff(c_3851,plain,(
    ~ m1_subset_1(k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3810])).

tff(c_3864,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_3851])).

tff(c_3867,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_248,c_66,c_3864])).

tff(c_3869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3867])).

tff(c_3871,plain,(
    m1_subset_1(k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3810])).

tff(c_1309,plain,(
    ! [B_152] :
      ( r1_lattices('#skF_6',B_152,'#skF_7')
      | k2_lattices('#skF_6',B_152,'#skF_7') != B_152
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1308])).

tff(c_3895,plain,
    ( r1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7')
    | k2_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') != k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3871,c_1309])).

tff(c_3958,plain,(
    r1_lattices('#skF_6',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3388,c_3895])).

tff(c_4009,plain,
    ( k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') = '#skF_7'
    | ~ r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'))
    | ~ m1_subset_1(k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l2_lattices('#skF_6')
    | ~ v4_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3958,c_60])).

tff(c_4016,plain,
    ( k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7') = '#skF_7'
    | ~ r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_79,c_66,c_3871,c_4009])).

tff(c_4017,plain,(
    ~ r1_lattices('#skF_6','#skF_7',k2_lattices('#skF_6',k6_lattices('#skF_6'),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_841,c_4016])).

tff(c_4020,plain,
    ( ~ r1_lattices('#skF_6','#skF_7',k6_lattices('#skF_6'))
    | ~ m1_subset_1(k6_lattices('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2082,c_4017])).

tff(c_4024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_2700,c_4020])).

tff(c_4026,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_4029,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_4026])).

tff(c_4032,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_4029])).

tff(c_4034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.26  
% 6.03/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.26  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1
% 6.33/2.26  
% 6.33/2.26  %Foreground sorts:
% 6.33/2.26  
% 6.33/2.26  
% 6.33/2.26  %Background operators:
% 6.33/2.26  
% 6.33/2.26  
% 6.33/2.26  %Foreground operators:
% 6.33/2.26  tff(l3_lattices, type, l3_lattices: $i > $o).
% 6.33/2.26  tff(k6_lattices, type, k6_lattices: $i > $i).
% 6.33/2.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.33/2.26  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 6.33/2.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.33/2.26  tff(l2_lattices, type, l2_lattices: $i > $o).
% 6.33/2.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.33/2.26  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.33/2.26  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 6.33/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.33/2.26  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 6.33/2.26  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 6.33/2.26  tff(l1_lattices, type, l1_lattices: $i > $o).
% 6.33/2.26  tff('#skF_7', type, '#skF_7': $i).
% 6.33/2.26  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 6.33/2.26  tff(v4_lattices, type, v4_lattices: $i > $o).
% 6.33/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.33/2.26  tff(v6_lattices, type, v6_lattices: $i > $o).
% 6.33/2.26  tff(v9_lattices, type, v9_lattices: $i > $o).
% 6.33/2.26  tff(v5_lattices, type, v5_lattices: $i > $o).
% 6.33/2.26  tff(v10_lattices, type, v10_lattices: $i > $o).
% 6.33/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.33/2.26  tff(v14_lattices, type, v14_lattices: $i > $o).
% 6.33/2.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.33/2.26  tff(v8_lattices, type, v8_lattices: $i > $o).
% 6.33/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.33/2.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.33/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.33/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.33/2.26  tff(v7_lattices, type, v7_lattices: $i > $o).
% 6.33/2.26  
% 6.33/2.29  tff(f_246, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 6.33/2.29  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 6.33/2.29  tff(f_120, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 6.33/2.29  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 6.33/2.29  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattices)).
% 6.33/2.29  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 6.33/2.29  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 6.33/2.29  tff(f_188, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 6.33/2.29  tff(f_107, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattices)).
% 6.33/2.29  tff(f_133, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 6.33/2.29  tff(f_169, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_lattices(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 6.33/2.29  tff(f_152, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 6.33/2.29  tff(f_231, axiom, (![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 6.33/2.29  tff(f_207, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 6.33/2.29  tff(c_74, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_68, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_72, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.29  tff(c_75, plain, (![A_78]: (l2_lattices(A_78) | ~l3_lattices(A_78))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.33/2.29  tff(c_79, plain, (l2_lattices('#skF_6')), inference(resolution, [status(thm)], [c_68, c_75])).
% 6.33/2.29  tff(c_42, plain, (![A_37]: (m1_subset_1(k6_lattices(A_37), u1_struct_0(A_37)) | ~l2_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.33/2.29  tff(c_70, plain, (v14_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_210, plain, (![A_102, C_103]: (k1_lattices(A_102, C_103, k6_lattices(A_102))=k6_lattices(A_102) | ~m1_subset_1(C_103, u1_struct_0(A_102)) | ~m1_subset_1(k6_lattices(A_102), u1_struct_0(A_102)) | ~v14_lattices(A_102) | ~l2_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.33/2.29  tff(c_226, plain, (k1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))=k6_lattices('#skF_6') | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6')) | ~v14_lattices('#skF_6') | ~l2_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_210])).
% 6.33/2.29  tff(c_236, plain, (k1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))=k6_lattices('#skF_6') | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_70, c_226])).
% 6.33/2.29  tff(c_237, plain, (k1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))=k6_lattices('#skF_6') | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_236])).
% 6.33/2.29  tff(c_238, plain, (~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_237])).
% 6.33/2.29  tff(c_241, plain, (~l2_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_238])).
% 6.33/2.29  tff(c_244, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_241])).
% 6.33/2.29  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_244])).
% 6.33/2.29  tff(c_248, plain, (m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_237])).
% 6.33/2.29  tff(c_247, plain, (k1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))=k6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_237])).
% 6.33/2.29  tff(c_36, plain, (![A_23]: (m1_subset_1('#skF_5'(A_23), u1_struct_0(A_23)) | v9_lattices(A_23) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.33/2.29  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.29  tff(c_100, plain, (![A_98, B_99, C_100]: (k1_lattices(A_98, k2_lattices(A_98, B_99, C_100), C_100)=C_100 | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~v8_lattices(A_98) | ~l3_lattices(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.33/2.29  tff(c_116, plain, (![B_99]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_99, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_100])).
% 6.33/2.29  tff(c_126, plain, (![B_99]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_99, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_116])).
% 6.33/2.29  tff(c_127, plain, (![B_99]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_99, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_99, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_126])).
% 6.33/2.29  tff(c_128, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_127])).
% 6.33/2.29  tff(c_131, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_4, c_128])).
% 6.33/2.29  tff(c_134, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_131])).
% 6.33/2.29  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_134])).
% 6.33/2.29  tff(c_139, plain, (![B_101]: (k1_lattices('#skF_6', k2_lattices('#skF_6', B_101, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_101, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_127])).
% 6.33/2.29  tff(c_159, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_5'('#skF_6'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_139])).
% 6.33/2.29  tff(c_189, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_5'('#skF_6'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_159])).
% 6.33/2.29  tff(c_190, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_5'('#skF_6'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_189])).
% 6.33/2.29  tff(c_208, plain, (v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_190])).
% 6.33/2.29  tff(c_373, plain, (![A_112, B_113, C_114]: (k2_lattices(A_112, B_113, k1_lattices(A_112, B_113, C_114))=B_113 | ~m1_subset_1(C_114, u1_struct_0(A_112)) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~v9_lattices(A_112) | ~l3_lattices(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.33/2.29  tff(c_375, plain, (![B_113]: (k2_lattices('#skF_6', B_113, k1_lattices('#skF_6', B_113, k6_lattices('#skF_6')))=B_113 | ~m1_subset_1(B_113, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_373])).
% 6.33/2.29  tff(c_394, plain, (![B_113]: (k2_lattices('#skF_6', B_113, k1_lattices('#skF_6', B_113, k6_lattices('#skF_6')))=B_113 | ~m1_subset_1(B_113, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_208, c_375])).
% 6.33/2.29  tff(c_500, plain, (![B_116]: (k2_lattices('#skF_6', B_116, k1_lattices('#skF_6', B_116, k6_lattices('#skF_6')))=B_116 | ~m1_subset_1(B_116, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_394])).
% 6.33/2.29  tff(c_522, plain, (k2_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_500])).
% 6.33/2.29  tff(c_535, plain, (k2_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_522])).
% 6.33/2.29  tff(c_138, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_127])).
% 6.33/2.29  tff(c_1276, plain, (![A_151, B_152, C_153]: (r1_lattices(A_151, B_152, C_153) | k2_lattices(A_151, B_152, C_153)!=B_152 | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l3_lattices(A_151) | ~v9_lattices(A_151) | ~v8_lattices(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_188])).
% 6.33/2.29  tff(c_1278, plain, (![B_152]: (r1_lattices('#skF_6', B_152, k6_lattices('#skF_6')) | k2_lattices('#skF_6', B_152, k6_lattices('#skF_6'))!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_1276])).
% 6.33/2.29  tff(c_1297, plain, (![B_152]: (r1_lattices('#skF_6', B_152, k6_lattices('#skF_6')) | k2_lattices('#skF_6', B_152, k6_lattices('#skF_6'))!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_1278])).
% 6.33/2.29  tff(c_1298, plain, (![B_152]: (r1_lattices('#skF_6', B_152, k6_lattices('#skF_6')) | k2_lattices('#skF_6', B_152, k6_lattices('#skF_6'))!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1297])).
% 6.33/2.29  tff(c_80, plain, (![A_79]: (l1_lattices(A_79) | ~l3_lattices(A_79))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.33/2.29  tff(c_84, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_68, c_80])).
% 6.33/2.29  tff(c_40, plain, (![A_34, B_35, C_36]: (m1_subset_1(k2_lattices(A_34, B_35, C_36), u1_struct_0(A_34)) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.33/2.29  tff(c_6, plain, (![A_1]: (v7_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.29  tff(c_1294, plain, (![B_152]: (r1_lattices('#skF_6', B_152, '#skF_7') | k2_lattices('#skF_6', B_152, '#skF_7')!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_1276])).
% 6.33/2.29  tff(c_1308, plain, (![B_152]: (r1_lattices('#skF_6', B_152, '#skF_7') | k2_lattices('#skF_6', B_152, '#skF_7')!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_1294])).
% 6.33/2.29  tff(c_1310, plain, (![B_154]: (r1_lattices('#skF_6', B_154, '#skF_7') | k2_lattices('#skF_6', B_154, '#skF_7')!=B_154 | ~m1_subset_1(B_154, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1308])).
% 6.33/2.29  tff(c_1374, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_7') | k2_lattices('#skF_6', '#skF_7', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_66, c_1310])).
% 6.33/2.29  tff(c_1375, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')!='#skF_7'), inference(splitLeft, [status(thm)], [c_1374])).
% 6.33/2.29  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.29  tff(c_558, plain, (![A_117, B_118, C_119]: (k4_lattices(A_117, B_118, C_119)=k2_lattices(A_117, B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_lattices(A_117) | ~v6_lattices(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.33/2.29  tff(c_576, plain, (![B_118]: (k4_lattices('#skF_6', B_118, '#skF_7')=k2_lattices('#skF_6', B_118, '#skF_7') | ~m1_subset_1(B_118, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_558])).
% 6.33/2.29  tff(c_590, plain, (![B_118]: (k4_lattices('#skF_6', B_118, '#skF_7')=k2_lattices('#skF_6', B_118, '#skF_7') | ~m1_subset_1(B_118, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_576])).
% 6.33/2.29  tff(c_591, plain, (![B_118]: (k4_lattices('#skF_6', B_118, '#skF_7')=k2_lattices('#skF_6', B_118, '#skF_7') | ~m1_subset_1(B_118, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_590])).
% 6.33/2.29  tff(c_592, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_591])).
% 6.33/2.29  tff(c_595, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_592])).
% 6.33/2.29  tff(c_598, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_595])).
% 6.33/2.29  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_598])).
% 6.33/2.29  tff(c_602, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_591])).
% 6.33/2.29  tff(c_750, plain, (![A_122, B_123, C_124]: (r3_lattices(A_122, B_123, B_123) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l3_lattices(A_122) | ~v9_lattices(A_122) | ~v8_lattices(A_122) | ~v6_lattices(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.33/2.29  tff(c_752, plain, (![B_123]: (r3_lattices('#skF_6', B_123, B_123) | ~m1_subset_1(B_123, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_750])).
% 6.33/2.29  tff(c_771, plain, (![B_123]: (r3_lattices('#skF_6', B_123, B_123) | ~m1_subset_1(B_123, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_138, c_208, c_68, c_752])).
% 6.33/2.29  tff(c_784, plain, (![B_125]: (r3_lattices('#skF_6', B_125, B_125) | ~m1_subset_1(B_125, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_771])).
% 6.33/2.29  tff(c_839, plain, (r3_lattices('#skF_6', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_66, c_784])).
% 6.33/2.29  tff(c_1401, plain, (![A_156, B_157, C_158]: (r1_lattices(A_156, B_157, C_158) | ~r3_lattices(A_156, B_157, C_158) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_157, u1_struct_0(A_156)) | ~l3_lattices(A_156) | ~v9_lattices(A_156) | ~v8_lattices(A_156) | ~v6_lattices(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.33/2.29  tff(c_1411, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_839, c_1401])).
% 6.33/2.29  tff(c_1427, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_138, c_208, c_68, c_66, c_1411])).
% 6.33/2.29  tff(c_1428, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_1427])).
% 6.33/2.29  tff(c_58, plain, (![A_48, B_52, C_54]: (k2_lattices(A_48, B_52, C_54)=B_52 | ~r1_lattices(A_48, B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l3_lattices(A_48) | ~v9_lattices(A_48) | ~v8_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_188])).
% 6.33/2.29  tff(c_1430, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1428, c_58])).
% 6.33/2.29  tff(c_1435, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_66, c_1430])).
% 6.33/2.29  tff(c_1437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1375, c_1435])).
% 6.33/2.29  tff(c_1438, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_7')), inference(splitRight, [status(thm)], [c_1374])).
% 6.33/2.29  tff(c_1441, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1438, c_58])).
% 6.33/2.29  tff(c_1446, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_66, c_1441])).
% 6.33/2.29  tff(c_1447, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_74, c_1446])).
% 6.33/2.29  tff(c_1988, plain, (![A_185, B_186, D_187, C_188]: (r1_lattices(A_185, k2_lattices(A_185, B_186, D_187), k2_lattices(A_185, C_188, D_187)) | ~r1_lattices(A_185, B_186, C_188) | ~m1_subset_1(D_187, u1_struct_0(A_185)) | ~m1_subset_1(C_188, u1_struct_0(A_185)) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l3_lattices(A_185) | ~v9_lattices(A_185) | ~v8_lattices(A_185) | ~v7_lattices(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.33/2.29  tff(c_1995, plain, (![C_188]: (r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_188, '#skF_7')) | ~r1_lattices('#skF_6', '#skF_7', C_188) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(C_188, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v7_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_1988])).
% 6.33/2.29  tff(c_2044, plain, (![C_188]: (r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_188, '#skF_7')) | ~r1_lattices('#skF_6', '#skF_7', C_188) | ~m1_subset_1(C_188, u1_struct_0('#skF_6')) | ~v7_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_66, c_66, c_1995])).
% 6.33/2.29  tff(c_2045, plain, (![C_188]: (r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_188, '#skF_7')) | ~r1_lattices('#skF_6', '#skF_7', C_188) | ~m1_subset_1(C_188, u1_struct_0('#skF_6')) | ~v7_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2044])).
% 6.33/2.29  tff(c_2073, plain, (~v7_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_2045])).
% 6.33/2.29  tff(c_2076, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_6, c_2073])).
% 6.33/2.29  tff(c_2079, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_2076])).
% 6.33/2.29  tff(c_2081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2079])).
% 6.33/2.29  tff(c_2104, plain, (![C_190]: (r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_190, '#skF_7')) | ~r1_lattices('#skF_6', '#skF_7', C_190) | ~m1_subset_1(C_190, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_2045])).
% 6.33/2.29  tff(c_2106, plain, (![C_190]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_190, '#skF_7'))='#skF_7' | ~m1_subset_1(k2_lattices('#skF_6', C_190, '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r1_lattices('#skF_6', '#skF_7', C_190) | ~m1_subset_1(C_190, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_2104, c_58])).
% 6.33/2.29  tff(c_2114, plain, (![C_190]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_190, '#skF_7'))='#skF_7' | ~m1_subset_1(k2_lattices('#skF_6', C_190, '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r1_lattices('#skF_6', '#skF_7', C_190) | ~m1_subset_1(C_190, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_208, c_68, c_66, c_2106])).
% 6.33/2.29  tff(c_2576, plain, (![C_215]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_215, '#skF_7'))='#skF_7' | ~m1_subset_1(k2_lattices('#skF_6', C_215, '#skF_7'), u1_struct_0('#skF_6')) | ~r1_lattices('#skF_6', '#skF_7', C_215) | ~m1_subset_1(C_215, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_2114])).
% 6.33/2.29  tff(c_2583, plain, (![B_35]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', B_35, '#skF_7'))='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', B_35) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2576])).
% 6.33/2.29  tff(c_2588, plain, (![B_35]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', B_35, '#skF_7'))='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', B_35) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_2583])).
% 6.33/2.29  tff(c_2590, plain, (![B_216]: (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', B_216, '#skF_7'))='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_2588])).
% 6.33/2.29  tff(c_2625, plain, (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'))='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_2590])).
% 6.33/2.29  tff(c_2691, plain, (~r1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))), inference(splitLeft, [status(thm)], [c_2625])).
% 6.33/2.29  tff(c_2694, plain, (k2_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1298, c_2691])).
% 6.33/2.29  tff(c_2698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_535, c_2694])).
% 6.33/2.29  tff(c_2700, plain, (r1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6'))), inference(splitRight, [status(thm)], [c_2625])).
% 6.33/2.29  tff(c_2082, plain, (![C_188]: (r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', C_188, '#skF_7')) | ~r1_lattices('#skF_6', '#skF_7', C_188) | ~m1_subset_1(C_188, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_2045])).
% 6.33/2.29  tff(c_681, plain, (![B_121]: (k4_lattices('#skF_6', B_121, '#skF_7')=k2_lattices('#skF_6', B_121, '#skF_7') | ~m1_subset_1(B_121, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_591])).
% 6.33/2.29  tff(c_712, plain, (k4_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7') | ~l2_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_681])).
% 6.33/2.29  tff(c_743, plain, (k4_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_712])).
% 6.33/2.29  tff(c_744, plain, (k4_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_743])).
% 6.33/2.29  tff(c_64, plain, (k4_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.33/2.29  tff(c_841, plain, (k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_744, c_64])).
% 6.33/2.29  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.29  tff(c_1534, plain, (![B_162]: (r1_lattices('#skF_6', B_162, k6_lattices('#skF_6')) | k2_lattices('#skF_6', B_162, k6_lattices('#skF_6'))!=B_162 | ~m1_subset_1(B_162, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1297])).
% 6.33/2.29  tff(c_60, plain, (![C_61, B_59, A_55]: (C_61=B_59 | ~r1_lattices(A_55, C_61, B_59) | ~r1_lattices(A_55, B_59, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_55)) | ~m1_subset_1(B_59, u1_struct_0(A_55)) | ~l2_lattices(A_55) | ~v4_lattices(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.33/2.29  tff(c_1538, plain, (![B_162]: (k6_lattices('#skF_6')=B_162 | ~r1_lattices('#skF_6', k6_lattices('#skF_6'), B_162) | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6') | k2_lattices('#skF_6', B_162, k6_lattices('#skF_6'))!=B_162 | ~m1_subset_1(B_162, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1534, c_60])).
% 6.33/2.29  tff(c_1545, plain, (![B_162]: (k6_lattices('#skF_6')=B_162 | ~r1_lattices('#skF_6', k6_lattices('#skF_6'), B_162) | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6') | k2_lattices('#skF_6', B_162, k6_lattices('#skF_6'))!=B_162 | ~m1_subset_1(B_162, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_248, c_1538])).
% 6.33/2.29  tff(c_1546, plain, (![B_162]: (k6_lattices('#skF_6')=B_162 | ~r1_lattices('#skF_6', k6_lattices('#skF_6'), B_162) | ~v4_lattices('#skF_6') | k2_lattices('#skF_6', B_162, k6_lattices('#skF_6'))!=B_162 | ~m1_subset_1(B_162, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1545])).
% 6.33/2.29  tff(c_1547, plain, (~v4_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_1546])).
% 6.33/2.29  tff(c_1550, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_12, c_1547])).
% 6.33/2.29  tff(c_1553, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1550])).
% 6.33/2.29  tff(c_1555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1553])).
% 6.33/2.29  tff(c_1557, plain, (v4_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_1546])).
% 6.33/2.29  tff(c_167, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')='#skF_7' | ~l2_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_139])).
% 6.33/2.29  tff(c_197, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_167])).
% 6.33/2.29  tff(c_198, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_74, c_197])).
% 6.33/2.29  tff(c_391, plain, (![B_113]: (k2_lattices('#skF_6', B_113, k1_lattices('#skF_6', B_113, '#skF_7'))=B_113 | ~m1_subset_1(B_113, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_373])).
% 6.33/2.29  tff(c_405, plain, (![B_113]: (k2_lattices('#skF_6', B_113, k1_lattices('#skF_6', B_113, '#skF_7'))=B_113 | ~m1_subset_1(B_113, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_208, c_391])).
% 6.33/2.29  tff(c_407, plain, (![B_115]: (k2_lattices('#skF_6', B_115, k1_lattices('#skF_6', B_115, '#skF_7'))=B_115 | ~m1_subset_1(B_115, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_405])).
% 6.33/2.29  tff(c_415, plain, (![B_35, C_36]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k1_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), '#skF_7'))=k2_lattices('#skF_6', B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_407])).
% 6.33/2.29  tff(c_441, plain, (![B_35, C_36]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k1_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), '#skF_7'))=k2_lattices('#skF_6', B_35, C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_415])).
% 6.33/2.29  tff(c_3210, plain, (![B_253, C_254]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_253, C_254), k1_lattices('#skF_6', k2_lattices('#skF_6', B_253, C_254), '#skF_7'))=k2_lattices('#skF_6', B_253, C_254) | ~m1_subset_1(C_254, u1_struct_0('#skF_6')) | ~m1_subset_1(B_253, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_441])).
% 6.33/2.29  tff(c_3333, plain, (k2_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_3210])).
% 6.33/2.29  tff(c_3388, plain, (k2_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_66, c_3333])).
% 6.33/2.29  tff(c_792, plain, (![B_35, C_36]: (r3_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k2_lattices('#skF_6', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_784])).
% 6.33/2.29  tff(c_817, plain, (![B_35, C_36]: (r3_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k2_lattices('#skF_6', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_792])).
% 6.33/2.29  tff(c_818, plain, (![B_35, C_36]: (r3_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k2_lattices('#skF_6', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_817])).
% 6.33/2.29  tff(c_1493, plain, (![A_159, B_160, C_161]: (r1_lattices(A_159, B_160, C_161) | ~r3_lattices(A_159, B_160, C_161) | ~m1_subset_1(C_161, u1_struct_0(A_159)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l3_lattices(A_159) | ~v9_lattices(A_159) | ~v8_lattices(A_159) | ~v6_lattices(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.33/2.29  tff(c_1497, plain, (![B_35, C_36]: (r1_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k2_lattices('#skF_6', B_35, C_36)) | ~m1_subset_1(k2_lattices('#skF_6', B_35, C_36), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_818, c_1493])).
% 6.33/2.29  tff(c_1507, plain, (![B_35, C_36]: (r1_lattices('#skF_6', k2_lattices('#skF_6', B_35, C_36), k2_lattices('#skF_6', B_35, C_36)) | ~m1_subset_1(k2_lattices('#skF_6', B_35, C_36), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~m1_subset_1(C_36, u1_struct_0('#skF_6')) | ~m1_subset_1(B_35, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_138, c_208, c_68, c_1497])).
% 6.33/2.29  tff(c_3697, plain, (![B_268, C_269]: (r1_lattices('#skF_6', k2_lattices('#skF_6', B_268, C_269), k2_lattices('#skF_6', B_268, C_269)) | ~m1_subset_1(k2_lattices('#skF_6', B_268, C_269), u1_struct_0('#skF_6')) | ~m1_subset_1(C_269, u1_struct_0('#skF_6')) | ~m1_subset_1(B_268, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1507])).
% 6.33/2.29  tff(c_3712, plain, (r1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), k2_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')) | ~m1_subset_1(k2_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3388, c_3697])).
% 6.33/2.29  tff(c_3810, plain, (r1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')) | ~m1_subset_1(k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3388, c_3388, c_3712])).
% 6.33/2.29  tff(c_3851, plain, (~m1_subset_1(k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_3810])).
% 6.33/2.29  tff(c_3864, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_3851])).
% 6.33/2.29  tff(c_3867, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_248, c_66, c_3864])).
% 6.33/2.29  tff(c_3869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3867])).
% 6.33/2.29  tff(c_3871, plain, (m1_subset_1(k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_3810])).
% 6.33/2.29  tff(c_1309, plain, (![B_152]: (r1_lattices('#skF_6', B_152, '#skF_7') | k2_lattices('#skF_6', B_152, '#skF_7')!=B_152 | ~m1_subset_1(B_152, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1308])).
% 6.33/2.29  tff(c_3895, plain, (r1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7') | k2_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')!=k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_3871, c_1309])).
% 6.33/2.29  tff(c_3958, plain, (r1_lattices('#skF_6', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3388, c_3895])).
% 6.33/2.29  tff(c_4009, plain, (k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')) | ~m1_subset_1(k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~v4_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_3958, c_60])).
% 6.33/2.29  tff(c_4016, plain, (k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')='#skF_7' | ~r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_79, c_66, c_3871, c_4009])).
% 6.33/2.29  tff(c_4017, plain, (~r1_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', k6_lattices('#skF_6'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_841, c_4016])).
% 6.33/2.29  tff(c_4020, plain, (~r1_lattices('#skF_6', '#skF_7', k6_lattices('#skF_6')) | ~m1_subset_1(k6_lattices('#skF_6'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2082, c_4017])).
% 6.33/2.29  tff(c_4024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_2700, c_4020])).
% 6.33/2.29  tff(c_4026, plain, (~v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_190])).
% 6.33/2.29  tff(c_4029, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_2, c_4026])).
% 6.33/2.29  tff(c_4032, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_4029])).
% 6.33/2.29  tff(c_4034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4032])).
% 6.33/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.29  
% 6.33/2.29  Inference rules
% 6.33/2.29  ----------------------
% 6.33/2.29  #Ref     : 0
% 6.33/2.29  #Sup     : 762
% 6.33/2.29  #Fact    : 0
% 6.33/2.29  #Define  : 0
% 6.33/2.29  #Split   : 14
% 6.33/2.29  #Chain   : 0
% 6.33/2.29  #Close   : 0
% 6.33/2.29  
% 6.33/2.29  Ordering : KBO
% 6.33/2.29  
% 6.33/2.29  Simplification rules
% 6.33/2.29  ----------------------
% 6.33/2.29  #Subsume      : 45
% 6.33/2.29  #Demod        : 1379
% 6.33/2.29  #Tautology    : 434
% 6.33/2.29  #SimpNegUnit  : 304
% 6.33/2.29  #BackRed      : 25
% 6.33/2.29  
% 6.33/2.29  #Partial instantiations: 0
% 6.33/2.29  #Strategies tried      : 1
% 6.33/2.29  
% 6.33/2.29  Timing (in seconds)
% 6.33/2.29  ----------------------
% 6.49/2.29  Preprocessing        : 0.36
% 6.49/2.29  Parsing              : 0.18
% 6.49/2.29  CNF conversion       : 0.03
% 6.49/2.30  Main loop            : 1.08
% 6.49/2.30  Inferencing          : 0.41
% 6.49/2.30  Reduction            : 0.35
% 6.49/2.30  Demodulation         : 0.25
% 6.49/2.30  BG Simplification    : 0.05
% 6.49/2.30  Subsumption          : 0.20
% 6.49/2.30  Abstraction          : 0.06
% 6.49/2.30  MUC search           : 0.00
% 6.49/2.30  Cooper               : 0.00
% 6.49/2.30  Total                : 1.50
% 6.49/2.30  Index Insertion      : 0.00
% 6.49/2.30  Index Deletion       : 0.00
% 6.49/2.30  Index Matching       : 0.00
% 6.49/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
