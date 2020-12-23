%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  167 (1490 expanded)
%              Number of leaves         :   39 ( 561 expanded)
%              Depth                    :   20
%              Number of atoms          :  432 (3863 expanded)
%              Number of equality atoms :   29 ( 374 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r3_lattices > r1_lattices > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v3_lattices > v2_struct_0 > v10_lattices > l3_lattices > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k5_lattice3,type,(
    k5_lattice3: ( $i * $i ) > $i )).

tff(k4_lattice3,type,(
    k4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( r3_orders_2(k3_yellow_1(A),B,C)
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_114,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_142,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( r1_lattices(k1_lattice3(A),B,C)
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

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

tff(f_66,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_lattices(A,B,C)
              <=> r3_orders_2(k3_lattice3(A),k4_lattice3(A,B),k4_lattice3(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_76,plain,(
    ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_30,plain,(
    ! [A_14] : ~ v2_struct_0(k1_lattice3(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_15] : v10_lattices(k1_lattice3(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    ! [A_11] : l3_lattices(k1_lattice3(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    ! [A_27] : k3_lattice3(k1_lattice3(A_27)) = k3_yellow_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,(
    ! [A_42,B_43] :
      ( k5_lattice3(A_42,B_43) = B_43
      | ~ m1_subset_1(B_43,u1_struct_0(k3_lattice3(A_42)))
      | ~ l3_lattices(A_42)
      | ~ v10_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    ! [A_27,B_43] :
      ( k5_lattice3(k1_lattice3(A_27),B_43) = B_43
      | ~ m1_subset_1(B_43,u1_struct_0(k3_yellow_1(A_27)))
      | ~ l3_lattices(k1_lattice3(A_27))
      | ~ v10_lattices(k1_lattice3(A_27))
      | v2_struct_0(k1_lattice3(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_92])).

tff(c_97,plain,(
    ! [A_27,B_43] :
      ( k5_lattice3(k1_lattice3(A_27),B_43) = B_43
      | ~ m1_subset_1(B_43,u1_struct_0(k3_yellow_1(A_27)))
      | v2_struct_0(k1_lattice3(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_95])).

tff(c_99,plain,(
    ! [A_44,B_45] :
      ( k5_lattice3(k1_lattice3(A_44),B_45) = B_45
      | ~ m1_subset_1(B_45,u1_struct_0(k3_yellow_1(A_44))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_97])).

tff(c_106,plain,(
    k5_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_116,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k5_lattice3(A_46,B_47),u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(k3_lattice3(A_46)))
      | ~ l3_lattices(A_46)
      | ~ v10_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_133,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k3_lattice3(k1_lattice3('#skF_1'))))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_116])).

tff(c_141,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_48,c_46,c_133])).

tff(c_142,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_141])).

tff(c_58,plain,
    ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_81,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_107,plain,(
    k5_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_130,plain,
    ( m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k3_lattice3(k1_lattice3('#skF_1'))))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_116])).

tff(c_138,plain,
    ( m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_50,c_46,c_130])).

tff(c_139,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_138])).

tff(c_38,plain,(
    ! [A_16,B_17,C_19] :
      ( r1_lattices(k1_lattice3(A_16),B_17,C_19)
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(k1_lattice3(A_16)))
      | ~ m1_subset_1(B_17,u1_struct_0(k1_lattice3(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_199,plain,(
    ! [B_55] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_55,'#skF_3')
      | ~ r1_tarski(B_55,'#skF_3')
      | ~ m1_subset_1(B_55,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_142,c_38])).

tff(c_205,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_199])).

tff(c_213,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_205])).

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

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_300,plain,(
    ! [A_68,B_69,C_70] :
      ( r3_lattices(A_68,B_69,C_70)
      | ~ r1_lattices(A_68,B_69,C_70)
      | ~ m1_subset_1(C_70,u1_struct_0(A_68))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l3_lattices(A_68)
      | ~ v9_lattices(A_68)
      | ~ v8_lattices(A_68)
      | ~ v6_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_302,plain,(
    ! [B_69] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_142,c_300])).

tff(c_313,plain,(
    ! [B_69] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_302])).

tff(c_314,plain,(
    ! [B_69] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_313])).

tff(c_322,plain,(
    ~ v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_325,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_322])).

tff(c_328,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_328])).

tff(c_331,plain,(
    ! [B_69] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_338,plain,(
    ~ v9_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_341,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_338])).

tff(c_344,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_344])).

tff(c_347,plain,(
    ! [B_69] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_69,'#skF_3')
      | ~ m1_subset_1(B_69,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_392,plain,(
    ~ v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_395,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_392])).

tff(c_398,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_395])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_398])).

tff(c_403,plain,(
    ! [B_74] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3')
      | ~ m1_subset_1(B_74,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_409,plain,
    ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_403])).

tff(c_417,plain,(
    r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_409])).

tff(c_20,plain,(
    ! [A_5,B_7] :
      ( k4_lattice3(A_5,B_7) = B_7
      | ~ m1_subset_1(B_7,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_165,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_142,c_20])).

tff(c_169,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_165])).

tff(c_170,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_169])).

tff(c_155,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_159,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_155])).

tff(c_160,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_159])).

tff(c_444,plain,(
    ! [A_76,B_77,C_78] :
      ( r3_orders_2(k3_lattice3(A_76),k4_lattice3(A_76,B_77),k4_lattice3(A_76,C_78))
      | ~ r3_lattices(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l3_lattices(A_76)
      | ~ v10_lattices(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_462,plain,(
    ! [C_78] :
      ( r3_orders_2(k3_lattice3(k1_lattice3('#skF_1')),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_78))
      | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v10_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_444])).

tff(c_483,plain,(
    ! [C_78] :
      ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_78))
      | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k1_lattice3('#skF_1')))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_139,c_46,c_462])).

tff(c_573,plain,(
    ! [C_85] :
      ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_85))
      | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_483])).

tff(c_580,plain,
    ( r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_573])).

tff(c_585,plain,(
    r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_417,c_580])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_585])).

tff(c_588,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_606,plain,(
    ! [A_92,B_93] :
      ( k5_lattice3(A_92,B_93) = B_93
      | ~ m1_subset_1(B_93,u1_struct_0(k3_lattice3(A_92)))
      | ~ l3_lattices(A_92)
      | ~ v10_lattices(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_609,plain,(
    ! [A_27,B_93] :
      ( k5_lattice3(k1_lattice3(A_27),B_93) = B_93
      | ~ m1_subset_1(B_93,u1_struct_0(k3_yellow_1(A_27)))
      | ~ l3_lattices(k1_lattice3(A_27))
      | ~ v10_lattices(k1_lattice3(A_27))
      | v2_struct_0(k1_lattice3(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_606])).

tff(c_611,plain,(
    ! [A_27,B_93] :
      ( k5_lattice3(k1_lattice3(A_27),B_93) = B_93
      | ~ m1_subset_1(B_93,u1_struct_0(k3_yellow_1(A_27)))
      | v2_struct_0(k1_lattice3(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_609])).

tff(c_613,plain,(
    ! [A_94,B_95] :
      ( k5_lattice3(k1_lattice3(A_94),B_95) = B_95
      | ~ m1_subset_1(B_95,u1_struct_0(k3_yellow_1(A_94))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_611])).

tff(c_621,plain,(
    k5_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_613])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k5_lattice3(A_12,B_13),u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(k3_lattice3(A_12)))
      | ~ l3_lattices(A_12)
      | ~ v10_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_650,plain,
    ( m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k3_lattice3(k1_lattice3('#skF_1'))))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_28])).

tff(c_654,plain,
    ( m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_50,c_46,c_650])).

tff(c_655,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_654])).

tff(c_620,plain,(
    k5_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_613])).

tff(c_640,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k3_lattice3(k1_lattice3('#skF_1'))))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_28])).

tff(c_644,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_48,c_46,c_640])).

tff(c_645,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_644])).

tff(c_761,plain,(
    ! [A_113,B_114,C_115] :
      ( r3_lattices(A_113,B_114,C_115)
      | ~ r1_lattices(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l3_lattices(A_113)
      | ~ v9_lattices(A_113)
      | ~ v8_lattices(A_113)
      | ~ v6_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_763,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_655,c_761])).

tff(c_774,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_763])).

tff(c_775,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_774])).

tff(c_834,plain,(
    ~ v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_837,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_834])).

tff(c_840,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_837])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_840])).

tff(c_844,plain,(
    v6_lattices(k1_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_843,plain,(
    ! [B_114] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_845,plain,(
    ~ v9_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_891,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_845])).

tff(c_894,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_891])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_894])).

tff(c_897,plain,(
    ! [B_114] :
      ( ~ v8_lattices(k1_lattice3('#skF_1'))
      | r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_2')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_899,plain,(
    ~ v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_902,plain,
    ( ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1'))
    | ~ l3_lattices(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_899])).

tff(c_905,plain,(
    v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_902])).

tff(c_907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_905])).

tff(c_909,plain,(
    v8_lattices(k1_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_898,plain,(
    v9_lattices(k1_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_765,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_645,c_761])).

tff(c_778,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_765])).

tff(c_779,plain,(
    ! [B_114] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_114,'#skF_3')
      | ~ m1_subset_1(B_114,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ v9_lattices(k1_lattice3('#skF_1'))
      | ~ v8_lattices(k1_lattice3('#skF_1'))
      | ~ v6_lattices(k1_lattice3('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_778])).

tff(c_1069,plain,(
    ! [B_134] :
      ( r3_lattices(k1_lattice3('#skF_1'),B_134,'#skF_3')
      | ~ r1_lattices(k1_lattice3('#skF_1'),B_134,'#skF_3')
      | ~ m1_subset_1(B_134,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_909,c_898,c_779])).

tff(c_1080,plain,
    ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_655,c_1069])).

tff(c_1088,plain,(
    ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_589,plain,(
    r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_659,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_645,c_20])).

tff(c_662,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_659])).

tff(c_663,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_662])).

tff(c_666,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v10_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_655,c_20])).

tff(c_669,plain,
    ( k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_666])).

tff(c_670,plain,(
    k4_lattice3(k1_lattice3('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_669])).

tff(c_1004,plain,(
    ! [A_130,B_131,C_132] :
      ( r3_lattices(A_130,B_131,C_132)
      | ~ r3_orders_2(k3_lattice3(A_130),k4_lattice3(A_130,B_131),k4_lattice3(A_130,C_132))
      | ~ m1_subset_1(C_132,u1_struct_0(A_130))
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l3_lattices(A_130)
      | ~ v10_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1016,plain,(
    ! [C_132] :
      ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_132)
      | ~ r3_orders_2(k3_lattice3(k1_lattice3('#skF_1')),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_132))
      | ~ m1_subset_1(C_132,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l3_lattices(k1_lattice3('#skF_1'))
      | ~ v10_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_1004])).

tff(c_1037,plain,(
    ! [C_132] :
      ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_132)
      | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_132))
      | ~ m1_subset_1(C_132,u1_struct_0(k1_lattice3('#skF_1')))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_655,c_46,c_1016])).

tff(c_1152,plain,(
    ! [C_140] :
      ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2',C_140)
      | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2',k4_lattice3(k1_lattice3('#skF_1'),C_140))
      | ~ m1_subset_1(C_140,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1037])).

tff(c_1165,plain,
    ( r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ r3_orders_2(k3_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1152])).

tff(c_1171,plain,(
    r3_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_589,c_1165])).

tff(c_18,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_lattices(A_2,B_3,C_4)
      | ~ r3_lattices(A_2,B_3,C_4)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | ~ v9_lattices(A_2)
      | ~ v8_lattices(A_2)
      | ~ v6_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1173,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ l3_lattices(k1_lattice3('#skF_1'))
    | ~ v9_lattices(k1_lattice3('#skF_1'))
    | ~ v8_lattices(k1_lattice3('#skF_1'))
    | ~ v6_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1171,c_18])).

tff(c_1176,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_909,c_898,c_26,c_655,c_645,c_1173])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1088,c_1176])).

tff(c_1180,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_40,plain,(
    ! [B_17,C_19,A_16] :
      ( r1_tarski(B_17,C_19)
      | ~ r1_lattices(k1_lattice3(A_16),B_17,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(k1_lattice3(A_16)))
      | ~ m1_subset_1(B_17,u1_struct_0(k1_lattice3(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1188,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1180,c_40])).

tff(c_1191,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_645,c_1188])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.56  
% 3.56/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.56  %$ r3_orders_2 > r3_lattices > r1_lattices > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v3_lattices > v2_struct_0 > v10_lattices > l3_lattices > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.56/1.56  
% 3.56/1.56  %Foreground sorts:
% 3.56/1.56  
% 3.56/1.56  
% 3.56/1.56  %Background operators:
% 3.56/1.56  
% 3.56/1.56  
% 3.56/1.56  %Foreground operators:
% 3.56/1.56  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.56/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.56/1.56  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.56/1.56  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.56  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.56/1.56  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.56/1.56  tff(k5_lattice3, type, k5_lattice3: ($i * $i) > $i).
% 3.56/1.56  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 3.56/1.56  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.56/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.56  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.56/1.56  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.56/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.56  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.56/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.56  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.56/1.56  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.56/1.56  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.56  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.56  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.56/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.56  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.56/1.56  
% 3.56/1.58  tff(f_152, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r3_orders_2(k3_yellow_1(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow_1)).
% 3.56/1.58  tff(f_110, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 3.56/1.58  tff(f_114, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 3.56/1.58  tff(f_94, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 3.56/1.58  tff(f_142, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 3.56/1.58  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k3_lattice3(A))) => (k5_lattice3(A, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattice3)).
% 3.56/1.58  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(k3_lattice3(A)))) => m1_subset_1(k5_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 3.56/1.58  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => (r1_lattices(k1_lattice3(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_lattice3)).
% 3.56/1.58  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.56/1.58  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.56/1.58  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 3.56/1.58  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) <=> r3_orders_2(k3_lattice3(A), k4_lattice3(A, B), k4_lattice3(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_lattice3)).
% 3.56/1.58  tff(c_52, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.56/1.58  tff(c_76, plain, (~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.56/1.58  tff(c_30, plain, (![A_14]: (~v2_struct_0(k1_lattice3(A_14)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.58  tff(c_36, plain, (![A_15]: (v10_lattices(k1_lattice3(A_15)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.56/1.58  tff(c_26, plain, (![A_11]: (l3_lattices(k1_lattice3(A_11)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.56/1.58  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.56/1.58  tff(c_46, plain, (![A_27]: (k3_lattice3(k1_lattice3(A_27))=k3_yellow_1(A_27))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.56/1.58  tff(c_92, plain, (![A_42, B_43]: (k5_lattice3(A_42, B_43)=B_43 | ~m1_subset_1(B_43, u1_struct_0(k3_lattice3(A_42))) | ~l3_lattices(A_42) | ~v10_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.56/1.58  tff(c_95, plain, (![A_27, B_43]: (k5_lattice3(k1_lattice3(A_27), B_43)=B_43 | ~m1_subset_1(B_43, u1_struct_0(k3_yellow_1(A_27))) | ~l3_lattices(k1_lattice3(A_27)) | ~v10_lattices(k1_lattice3(A_27)) | v2_struct_0(k1_lattice3(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_92])).
% 3.56/1.58  tff(c_97, plain, (![A_27, B_43]: (k5_lattice3(k1_lattice3(A_27), B_43)=B_43 | ~m1_subset_1(B_43, u1_struct_0(k3_yellow_1(A_27))) | v2_struct_0(k1_lattice3(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_95])).
% 3.56/1.58  tff(c_99, plain, (![A_44, B_45]: (k5_lattice3(k1_lattice3(A_44), B_45)=B_45 | ~m1_subset_1(B_45, u1_struct_0(k3_yellow_1(A_44))))), inference(negUnitSimplification, [status(thm)], [c_30, c_97])).
% 3.56/1.58  tff(c_106, plain, (k5_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_99])).
% 3.56/1.58  tff(c_116, plain, (![A_46, B_47]: (m1_subset_1(k5_lattice3(A_46, B_47), u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(k3_lattice3(A_46))) | ~l3_lattices(A_46) | ~v10_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.56/1.58  tff(c_133, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0(k3_lattice3(k1_lattice3('#skF_1')))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_116])).
% 3.56/1.58  tff(c_141, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_48, c_46, c_133])).
% 3.56/1.58  tff(c_142, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_141])).
% 3.56/1.58  tff(c_58, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.56/1.58  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_58])).
% 3.56/1.58  tff(c_50, plain, (m1_subset_1('#skF_2', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.56/1.58  tff(c_107, plain, (k5_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_50, c_99])).
% 3.56/1.58  tff(c_130, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k3_lattice3(k1_lattice3('#skF_1')))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_116])).
% 3.56/1.58  tff(c_138, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_50, c_46, c_130])).
% 3.56/1.58  tff(c_139, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_138])).
% 3.56/1.58  tff(c_38, plain, (![A_16, B_17, C_19]: (r1_lattices(k1_lattice3(A_16), B_17, C_19) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, u1_struct_0(k1_lattice3(A_16))) | ~m1_subset_1(B_17, u1_struct_0(k1_lattice3(A_16))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.56/1.58  tff(c_199, plain, (![B_55]: (r1_lattices(k1_lattice3('#skF_1'), B_55, '#skF_3') | ~r1_tarski(B_55, '#skF_3') | ~m1_subset_1(B_55, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_142, c_38])).
% 3.56/1.58  tff(c_205, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_139, c_199])).
% 3.56/1.58  tff(c_213, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_205])).
% 3.56/1.58  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.58  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.58  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.58  tff(c_300, plain, (![A_68, B_69, C_70]: (r3_lattices(A_68, B_69, C_70) | ~r1_lattices(A_68, B_69, C_70) | ~m1_subset_1(C_70, u1_struct_0(A_68)) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l3_lattices(A_68) | ~v9_lattices(A_68) | ~v8_lattices(A_68) | ~v6_lattices(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.56/1.58  tff(c_302, plain, (![B_69]: (r3_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~m1_subset_1(B_69, u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_142, c_300])).
% 3.56/1.58  tff(c_313, plain, (![B_69]: (r3_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~m1_subset_1(B_69, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_302])).
% 3.56/1.58  tff(c_314, plain, (![B_69]: (r3_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~m1_subset_1(B_69, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_313])).
% 3.56/1.58  tff(c_322, plain, (~v6_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_314])).
% 3.56/1.58  tff(c_325, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_322])).
% 3.56/1.58  tff(c_328, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_325])).
% 3.56/1.58  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_328])).
% 3.56/1.58  tff(c_331, plain, (![B_69]: (~v8_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~m1_subset_1(B_69, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_314])).
% 3.56/1.58  tff(c_338, plain, (~v9_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_331])).
% 3.56/1.58  tff(c_341, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_338])).
% 3.56/1.58  tff(c_344, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_341])).
% 3.56/1.58  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_344])).
% 3.56/1.58  tff(c_347, plain, (![B_69]: (~v8_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_69, '#skF_3') | ~m1_subset_1(B_69, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_331])).
% 3.56/1.58  tff(c_392, plain, (~v8_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_347])).
% 3.56/1.58  tff(c_395, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_392])).
% 3.56/1.58  tff(c_398, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_395])).
% 3.56/1.58  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_398])).
% 3.56/1.58  tff(c_403, plain, (![B_74]: (r3_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3') | ~m1_subset_1(B_74, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_347])).
% 3.56/1.58  tff(c_409, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_139, c_403])).
% 3.56/1.58  tff(c_417, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_409])).
% 3.56/1.58  tff(c_20, plain, (![A_5, B_7]: (k4_lattice3(A_5, B_7)=B_7 | ~m1_subset_1(B_7, u1_struct_0(A_5)) | ~l3_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.58  tff(c_165, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_142, c_20])).
% 3.56/1.58  tff(c_169, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_165])).
% 3.56/1.58  tff(c_170, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_169])).
% 3.56/1.58  tff(c_155, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_139, c_20])).
% 3.56/1.58  tff(c_159, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_155])).
% 3.56/1.58  tff(c_160, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_30, c_159])).
% 3.56/1.58  tff(c_444, plain, (![A_76, B_77, C_78]: (r3_orders_2(k3_lattice3(A_76), k4_lattice3(A_76, B_77), k4_lattice3(A_76, C_78)) | ~r3_lattices(A_76, B_77, C_78) | ~m1_subset_1(C_78, u1_struct_0(A_76)) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l3_lattices(A_76) | ~v10_lattices(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.56/1.59  tff(c_462, plain, (![C_78]: (r3_orders_2(k3_lattice3(k1_lattice3('#skF_1')), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_78)) | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_78) | ~m1_subset_1(C_78, u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_444])).
% 3.56/1.59  tff(c_483, plain, (![C_78]: (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_78)) | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_78) | ~m1_subset_1(C_78, u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_139, c_46, c_462])).
% 3.56/1.59  tff(c_573, plain, (![C_85]: (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_85)) | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_85) | ~m1_subset_1(C_85, u1_struct_0(k1_lattice3('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_483])).
% 3.56/1.59  tff(c_580, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_573])).
% 3.56/1.59  tff(c_585, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_417, c_580])).
% 3.56/1.59  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_585])).
% 3.56/1.59  tff(c_588, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.56/1.59  tff(c_606, plain, (![A_92, B_93]: (k5_lattice3(A_92, B_93)=B_93 | ~m1_subset_1(B_93, u1_struct_0(k3_lattice3(A_92))) | ~l3_lattices(A_92) | ~v10_lattices(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.56/1.59  tff(c_609, plain, (![A_27, B_93]: (k5_lattice3(k1_lattice3(A_27), B_93)=B_93 | ~m1_subset_1(B_93, u1_struct_0(k3_yellow_1(A_27))) | ~l3_lattices(k1_lattice3(A_27)) | ~v10_lattices(k1_lattice3(A_27)) | v2_struct_0(k1_lattice3(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_606])).
% 3.56/1.59  tff(c_611, plain, (![A_27, B_93]: (k5_lattice3(k1_lattice3(A_27), B_93)=B_93 | ~m1_subset_1(B_93, u1_struct_0(k3_yellow_1(A_27))) | v2_struct_0(k1_lattice3(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_609])).
% 3.56/1.59  tff(c_613, plain, (![A_94, B_95]: (k5_lattice3(k1_lattice3(A_94), B_95)=B_95 | ~m1_subset_1(B_95, u1_struct_0(k3_yellow_1(A_94))))), inference(negUnitSimplification, [status(thm)], [c_30, c_611])).
% 3.56/1.59  tff(c_621, plain, (k5_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_50, c_613])).
% 3.56/1.59  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(k5_lattice3(A_12, B_13), u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(k3_lattice3(A_12))) | ~l3_lattices(A_12) | ~v10_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.56/1.59  tff(c_650, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k3_lattice3(k1_lattice3('#skF_1')))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_621, c_28])).
% 3.56/1.59  tff(c_654, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_50, c_46, c_650])).
% 3.56/1.59  tff(c_655, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_654])).
% 3.56/1.59  tff(c_620, plain, (k5_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_613])).
% 3.56/1.59  tff(c_640, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0(k3_lattice3(k1_lattice3('#skF_1')))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_620, c_28])).
% 3.56/1.59  tff(c_644, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_48, c_46, c_640])).
% 3.56/1.59  tff(c_645, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_644])).
% 3.56/1.59  tff(c_761, plain, (![A_113, B_114, C_115]: (r3_lattices(A_113, B_114, C_115) | ~r1_lattices(A_113, B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l3_lattices(A_113) | ~v9_lattices(A_113) | ~v8_lattices(A_113) | ~v6_lattices(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.56/1.59  tff(c_763, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_655, c_761])).
% 3.56/1.59  tff(c_774, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_763])).
% 3.56/1.59  tff(c_775, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_774])).
% 3.56/1.59  tff(c_834, plain, (~v6_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_775])).
% 3.56/1.59  tff(c_837, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_834])).
% 3.56/1.59  tff(c_840, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_837])).
% 3.56/1.59  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_840])).
% 3.56/1.59  tff(c_844, plain, (v6_lattices(k1_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_775])).
% 3.56/1.59  tff(c_843, plain, (![B_114]: (~v8_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_775])).
% 3.56/1.59  tff(c_845, plain, (~v9_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_843])).
% 3.56/1.59  tff(c_891, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_845])).
% 3.56/1.59  tff(c_894, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_891])).
% 3.56/1.59  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_894])).
% 3.56/1.59  tff(c_897, plain, (![B_114]: (~v8_lattices(k1_lattice3('#skF_1')) | r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_2') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))))), inference(splitRight, [status(thm)], [c_843])).
% 3.56/1.59  tff(c_899, plain, (~v8_lattices(k1_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_897])).
% 3.56/1.59  tff(c_902, plain, (~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')) | ~l3_lattices(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_899])).
% 3.56/1.59  tff(c_905, plain, (v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_902])).
% 3.56/1.59  tff(c_907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_905])).
% 3.56/1.59  tff(c_909, plain, (v8_lattices(k1_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_897])).
% 3.56/1.59  tff(c_898, plain, (v9_lattices(k1_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_843])).
% 3.56/1.59  tff(c_765, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_645, c_761])).
% 3.56/1.59  tff(c_778, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_765])).
% 3.56/1.59  tff(c_779, plain, (![B_114]: (r3_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_114, '#skF_3') | ~m1_subset_1(B_114, u1_struct_0(k1_lattice3('#skF_1'))) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_778])).
% 3.56/1.59  tff(c_1069, plain, (![B_134]: (r3_lattices(k1_lattice3('#skF_1'), B_134, '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), B_134, '#skF_3') | ~m1_subset_1(B_134, u1_struct_0(k1_lattice3('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_844, c_909, c_898, c_779])).
% 3.56/1.59  tff(c_1080, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_655, c_1069])).
% 3.56/1.59  tff(c_1088, plain, (~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_1080])).
% 3.56/1.59  tff(c_589, plain, (r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.56/1.59  tff(c_659, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_645, c_20])).
% 3.56/1.59  tff(c_662, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_659])).
% 3.56/1.59  tff(c_663, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_662])).
% 3.56/1.59  tff(c_666, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_655, c_20])).
% 3.56/1.59  tff(c_669, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_666])).
% 3.56/1.59  tff(c_670, plain, (k4_lattice3(k1_lattice3('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_30, c_669])).
% 3.56/1.59  tff(c_1004, plain, (![A_130, B_131, C_132]: (r3_lattices(A_130, B_131, C_132) | ~r3_orders_2(k3_lattice3(A_130), k4_lattice3(A_130, B_131), k4_lattice3(A_130, C_132)) | ~m1_subset_1(C_132, u1_struct_0(A_130)) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | ~l3_lattices(A_130) | ~v10_lattices(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.56/1.59  tff(c_1016, plain, (![C_132]: (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_132) | ~r3_orders_2(k3_lattice3(k1_lattice3('#skF_1')), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_132)) | ~m1_subset_1(C_132, u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v10_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_670, c_1004])).
% 3.56/1.59  tff(c_1037, plain, (![C_132]: (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_132) | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_132)) | ~m1_subset_1(C_132, u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_655, c_46, c_1016])).
% 3.56/1.59  tff(c_1152, plain, (![C_140]: (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', C_140) | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', k4_lattice3(k1_lattice3('#skF_1'), C_140)) | ~m1_subset_1(C_140, u1_struct_0(k1_lattice3('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_1037])).
% 3.56/1.59  tff(c_1165, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~r3_orders_2(k3_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_663, c_1152])).
% 3.56/1.59  tff(c_1171, plain, (r3_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_589, c_1165])).
% 3.56/1.59  tff(c_18, plain, (![A_2, B_3, C_4]: (r1_lattices(A_2, B_3, C_4) | ~r3_lattices(A_2, B_3, C_4) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | ~v9_lattices(A_2) | ~v8_lattices(A_2) | ~v6_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.56/1.59  tff(c_1173, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l3_lattices(k1_lattice3('#skF_1')) | ~v9_lattices(k1_lattice3('#skF_1')) | ~v8_lattices(k1_lattice3('#skF_1')) | ~v6_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_1171, c_18])).
% 3.56/1.59  tff(c_1176, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_844, c_909, c_898, c_26, c_655, c_645, c_1173])).
% 3.56/1.59  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1088, c_1176])).
% 3.56/1.59  tff(c_1180, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1080])).
% 3.56/1.59  tff(c_40, plain, (![B_17, C_19, A_16]: (r1_tarski(B_17, C_19) | ~r1_lattices(k1_lattice3(A_16), B_17, C_19) | ~m1_subset_1(C_19, u1_struct_0(k1_lattice3(A_16))) | ~m1_subset_1(B_17, u1_struct_0(k1_lattice3(A_16))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.56/1.59  tff(c_1188, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_1180, c_40])).
% 3.56/1.59  tff(c_1191, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_655, c_645, c_1188])).
% 3.56/1.59  tff(c_1193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_1191])).
% 3.56/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  Inference rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Ref     : 0
% 3.56/1.59  #Sup     : 206
% 3.56/1.59  #Fact    : 0
% 3.56/1.59  #Define  : 0
% 3.56/1.59  #Split   : 29
% 3.56/1.59  #Chain   : 0
% 3.56/1.59  #Close   : 0
% 3.56/1.59  
% 3.56/1.59  Ordering : KBO
% 3.56/1.59  
% 3.56/1.59  Simplification rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Subsume      : 27
% 3.56/1.59  #Demod        : 307
% 3.56/1.59  #Tautology    : 47
% 3.56/1.59  #SimpNegUnit  : 79
% 3.56/1.59  #BackRed      : 0
% 3.56/1.59  
% 3.56/1.59  #Partial instantiations: 0
% 3.56/1.59  #Strategies tried      : 1
% 3.56/1.59  
% 3.56/1.59  Timing (in seconds)
% 3.56/1.59  ----------------------
% 3.56/1.59  Preprocessing        : 0.31
% 3.56/1.59  Parsing              : 0.17
% 3.56/1.59  CNF conversion       : 0.02
% 3.56/1.59  Main loop            : 0.47
% 3.56/1.59  Inferencing          : 0.18
% 3.56/1.59  Reduction            : 0.16
% 3.56/1.59  Demodulation         : 0.11
% 3.56/1.59  BG Simplification    : 0.02
% 3.56/1.59  Subsumption          : 0.07
% 3.56/1.59  Abstraction          : 0.02
% 3.56/1.59  MUC search           : 0.00
% 3.56/1.59  Cooper               : 0.00
% 3.56/1.59  Total                : 0.84
% 3.56/1.59  Index Insertion      : 0.00
% 3.56/1.59  Index Deletion       : 0.00
% 3.56/1.59  Index Matching       : 0.00
% 3.56/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
