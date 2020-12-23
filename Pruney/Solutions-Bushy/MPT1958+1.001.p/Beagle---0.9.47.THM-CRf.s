%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1958+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 224 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 658 expanded)
%              Number of equality atoms :   28 ( 108 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v7_struct_0 > v5_orders_2 > v3_yellow_0 > v2_yellow_0 > v2_struct_0 > v1_yellow_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k4_yellow_0 > k3_yellow_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(v2_yellow_0,type,(
    v2_yellow_0: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_orders_2(A)
          & v3_yellow_0(A)
          & l1_orders_2(A) )
       => ( v7_struct_0(A)
        <=> k4_yellow_0(A) = k3_yellow_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_7)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v7_struct_0(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_yellow_0(A)
       => ( v1_yellow_0(A)
          & v2_yellow_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k4_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,k4_yellow_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [A_34] :
      ( '#skF_2'(A_34) != '#skF_1'(A_34)
      | v7_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,
    ( k4_yellow_0('#skF_3') != k3_yellow_0('#skF_3')
    | ~ v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_73,plain,
    ( '#skF_2'('#skF_3') != '#skF_1'('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_42])).

tff(c_74,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_77,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_82,plain,(
    '#skF_2'('#skF_3') != '#skF_1'('#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_83,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_12,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),u1_struct_0(A_2))
      | v7_struct_0(A_2)
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    v3_yellow_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_55,plain,(
    ! [A_31] :
      ( v1_yellow_0(A_31)
      | ~ v3_yellow_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_61,plain,(
    v1_yellow_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_22,plain,(
    ! [A_23,B_25] :
      ( r1_orders_2(A_23,k3_yellow_0(A_23),B_25)
      | ~ m1_subset_1(B_25,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v1_yellow_0(A_23)
      | ~ v5_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,
    ( v7_struct_0('#skF_3')
    | k4_yellow_0('#skF_3') = k3_yellow_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    k4_yellow_0('#skF_3') = k3_yellow_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40])).

tff(c_62,plain,(
    ! [A_32] :
      ( m1_subset_1(k4_yellow_0(A_32),u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,
    ( m1_subset_1(k3_yellow_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_62])).

tff(c_67,plain,(
    m1_subset_1(k3_yellow_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_65])).

tff(c_43,plain,(
    ! [A_30] :
      ( v2_yellow_0(A_30)
      | ~ v3_yellow_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,
    ( v2_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_49,plain,(
    v2_yellow_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_46])).

tff(c_133,plain,(
    ! [A_43,B_44] :
      ( r1_orders_2(A_43,B_44,k4_yellow_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v2_yellow_0(A_43)
      | ~ v5_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_136,plain,(
    ! [B_44] :
      ( r1_orders_2('#skF_3',B_44,k3_yellow_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_yellow_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_133])).

tff(c_138,plain,(
    ! [B_44] :
      ( r1_orders_2('#skF_3',B_44,k3_yellow_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_49,c_26,c_136])).

tff(c_139,plain,(
    ! [B_44] :
      ( r1_orders_2('#skF_3',B_44,k3_yellow_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_138])).

tff(c_183,plain,(
    ! [C_52,B_53,A_54] :
      ( C_52 = B_53
      | ~ r1_orders_2(A_54,C_52,B_53)
      | ~ r1_orders_2(A_54,B_53,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_54))
      | ~ m1_subset_1(B_53,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [B_44] :
      ( k3_yellow_0('#skF_3') = B_44
      | ~ r1_orders_2('#skF_3',k3_yellow_0('#skF_3'),B_44)
      | ~ m1_subset_1(k3_yellow_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_139,c_183])).

tff(c_195,plain,(
    ! [B_55] :
      ( k3_yellow_0('#skF_3') = B_55
      | ~ r1_orders_2('#skF_3',k3_yellow_0('#skF_3'),B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_67,c_187])).

tff(c_199,plain,(
    ! [B_25] :
      ( k3_yellow_0('#skF_3') = B_25
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_yellow_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_210,plain,(
    ! [B_25] :
      ( k3_yellow_0('#skF_3') = B_25
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_61,c_26,c_199])).

tff(c_220,plain,(
    ! [B_56] :
      ( k3_yellow_0('#skF_3') = B_56
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_210])).

tff(c_228,plain,
    ( k3_yellow_0('#skF_3') = '#skF_1'('#skF_3')
    | v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_246,plain,
    ( k3_yellow_0('#skF_3') = '#skF_1'('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_228])).

tff(c_247,plain,(
    k3_yellow_0('#skF_3') = '#skF_1'('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_246])).

tff(c_10,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_2'(A_2),u1_struct_0(A_2))
      | v7_struct_0(A_2)
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,
    ( k3_yellow_0('#skF_3') = '#skF_2'('#skF_3')
    | v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_220])).

tff(c_242,plain,
    ( k3_yellow_0('#skF_3') = '#skF_2'('#skF_3')
    | v7_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_224])).

tff(c_243,plain,(
    k3_yellow_0('#skF_3') = '#skF_2'('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_242])).

tff(c_287,plain,(
    '#skF_2'('#skF_3') = '#skF_1'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_243])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_287])).

tff(c_290,plain,(
    k4_yellow_0('#skF_3') != k3_yellow_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_291,plain,(
    v7_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_16,plain,(
    ! [A_14] :
      ( m1_subset_1(k4_yellow_0(A_14),u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_13] :
      ( m1_subset_1(k3_yellow_0(A_13),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_313,plain,(
    ! [C_66,B_67,A_68] :
      ( C_66 = B_67
      | ~ m1_subset_1(C_66,u1_struct_0(A_68))
      | ~ m1_subset_1(B_67,u1_struct_0(A_68))
      | ~ v7_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_326,plain,(
    ! [A_69,B_70] :
      ( k3_yellow_0(A_69) = B_70
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ v7_struct_0(A_69)
      | ~ l1_struct_0(A_69)
      | ~ l1_orders_2(A_69) ) ),
    inference(resolution,[status(thm)],[c_14,c_313])).

tff(c_344,plain,(
    ! [A_71] :
      ( k4_yellow_0(A_71) = k3_yellow_0(A_71)
      | ~ v7_struct_0(A_71)
      | ~ l1_struct_0(A_71)
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_16,c_326])).

tff(c_350,plain,
    ( k4_yellow_0('#skF_3') = k3_yellow_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_291,c_344])).

tff(c_354,plain,
    ( k4_yellow_0('#skF_3') = k3_yellow_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_350])).

tff(c_355,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_354])).

tff(c_358,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_355])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_358])).

%------------------------------------------------------------------------------
