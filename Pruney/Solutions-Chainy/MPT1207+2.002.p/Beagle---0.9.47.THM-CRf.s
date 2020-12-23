%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 518 expanded)
%              Number of leaves         :   35 ( 192 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 (1890 expanded)
%              Number of equality atoms :   19 ( 136 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

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

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_lattices(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,B,k1_lattices(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

tff(c_44,plain,(
    ~ r3_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_10,plain,(
    ! [A_1] :
      ( v5_lattices(A_1)
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

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_112,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_lattices(A_52,k2_lattices(A_52,B_53,C_54),C_54) = C_54
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ v8_lattices(A_52)
      | ~ l3_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    ! [B_53] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_53,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_135,plain,(
    ! [B_53] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_53,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_124])).

tff(c_136,plain,(
    ! [B_53] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_53,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_135])).

tff(c_145,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_149,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_152,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_152])).

tff(c_156,plain,(
    v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_344,plain,(
    ! [A_67,B_68,C_69] :
      ( r3_lattices(A_67,B_68,C_69)
      | ~ r1_lattices(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l3_lattices(A_67)
      | ~ v9_lattices(A_67)
      | ~ v8_lattices(A_67)
      | ~ v6_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_356,plain,(
    ! [B_68] :
      ( r3_lattices('#skF_4',B_68,'#skF_5')
      | ~ r1_lattices('#skF_4',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_344])).

tff(c_367,plain,(
    ! [B_68] :
      ( r3_lattices('#skF_4',B_68,'#skF_5')
      | ~ r1_lattices('#skF_4',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_48,c_356])).

tff(c_368,plain,(
    ! [B_68] :
      ( r3_lattices('#skF_4',B_68,'#skF_5')
      | ~ r1_lattices('#skF_4',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_367])).

tff(c_369,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_372,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_369])).

tff(c_375,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_375])).

tff(c_378,plain,(
    ! [B_68] :
      ( ~ v9_lattices('#skF_4')
      | r3_lattices('#skF_4',B_68,'#skF_5')
      | ~ r1_lattices('#skF_4',B_68,'#skF_5')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_380,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_383,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_380])).

tff(c_386,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_383])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_386])).

tff(c_390,plain,(
    v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_379,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_55,plain,(
    ! [A_36] :
      ( l1_lattices(A_36)
      | ~ l3_lattices(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_59,plain,(
    l1_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_55])).

tff(c_32,plain,(
    ! [A_23] :
      ( m1_subset_1(k5_lattices(A_23),u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    v13_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_76,plain,(
    ! [A_50,C_51] :
      ( k2_lattices(A_50,C_51,k5_lattices(A_50)) = k5_lattices(A_50)
      | ~ m1_subset_1(C_51,u1_struct_0(A_50))
      | ~ m1_subset_1(k5_lattices(A_50),u1_struct_0(A_50))
      | ~ v13_lattices(A_50)
      | ~ l1_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v13_lattices('#skF_4')
    | ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_93,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50,c_86])).

tff(c_94,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_93])).

tff(c_95,plain,(
    ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_98,plain,
    ( ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_101,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_98])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_101])).

tff(c_105,plain,(
    m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_206,plain,(
    ! [A_56,C_57] :
      ( k2_lattices(A_56,k5_lattices(A_56),C_57) = k5_lattices(A_56)
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ m1_subset_1(k5_lattices(A_56),u1_struct_0(A_56))
      | ~ v13_lattices(A_56)
      | ~ l1_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_218,plain,
    ( k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v13_lattices('#skF_4')
    | ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_229,plain,
    ( k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50,c_105,c_218])).

tff(c_230,plain,(
    k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_229])).

tff(c_157,plain,(
    ! [B_55] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_55,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_180,plain,(
    k1_lattices('#skF_4',k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_105,c_157])).

tff(c_231,plain,(
    k1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_180])).

tff(c_391,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_lattices(A_70,B_71,k1_lattices(A_70,B_71,C_72))
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | ~ v9_lattices(A_70)
      | ~ v8_lattices(A_70)
      | ~ v6_lattices(A_70)
      | ~ v5_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_403,plain,
    ( r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | ~ v9_lattices('#skF_4')
    | ~ v8_lattices('#skF_4')
    | ~ v6_lattices('#skF_4')
    | ~ v5_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_391])).

tff(c_417,plain,
    ( r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5')
    | ~ v9_lattices('#skF_4')
    | ~ v5_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_156,c_48,c_105,c_46,c_403])).

tff(c_418,plain,
    ( r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5')
    | ~ v9_lattices('#skF_4')
    | ~ v5_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_417])).

tff(c_423,plain,
    ( r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5')
    | ~ v5_lattices('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_418])).

tff(c_424,plain,(
    ~ v5_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_427,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_424])).

tff(c_430,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_427])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_430])).

tff(c_433,plain,(
    r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_444,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_4',B_75,'#skF_5')
      | ~ r1_lattices('#skF_4',B_75,'#skF_5')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_447,plain,
    ( r3_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5')
    | ~ r1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_444])).

tff(c_469,plain,(
    r3_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_447])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.78/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.40  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.78/1.40  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.78/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.78/1.40  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.78/1.40  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.78/1.40  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.78/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.40  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.78/1.40  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.78/1.40  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.78/1.40  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.78/1.40  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.78/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.78/1.40  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.78/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.40  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.78/1.40  
% 2.78/1.42  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattices)).
% 2.78/1.42  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.78/1.42  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 2.78/1.42  tff(f_113, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.78/1.42  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.78/1.42  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.78/1.42  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 2.78/1.42  tff(f_134, axiom, (![A]: ((((((~v2_struct_0(A) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, B, k1_lattices(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_lattices)).
% 2.78/1.42  tff(c_44, plain, (~r3_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_48, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_52, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_10, plain, (![A_1]: (v5_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_112, plain, (![A_52, B_53, C_54]: (k1_lattices(A_52, k2_lattices(A_52, B_53, C_54), C_54)=C_54 | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~v8_lattices(A_52) | ~l3_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.78/1.42  tff(c_124, plain, (![B_53]: (k1_lattices('#skF_4', k2_lattices('#skF_4', B_53, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4') | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_112])).
% 2.78/1.42  tff(c_135, plain, (![B_53]: (k1_lattices('#skF_4', k2_lattices('#skF_4', B_53, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_124])).
% 2.78/1.42  tff(c_136, plain, (![B_53]: (k1_lattices('#skF_4', k2_lattices('#skF_4', B_53, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_53, u1_struct_0('#skF_4')) | ~v8_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_135])).
% 2.78/1.42  tff(c_145, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_136])).
% 2.78/1.42  tff(c_149, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_4, c_145])).
% 2.78/1.42  tff(c_152, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_149])).
% 2.78/1.42  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_152])).
% 2.78/1.42  tff(c_156, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_136])).
% 2.78/1.42  tff(c_344, plain, (![A_67, B_68, C_69]: (r3_lattices(A_67, B_68, C_69) | ~r1_lattices(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l3_lattices(A_67) | ~v9_lattices(A_67) | ~v8_lattices(A_67) | ~v6_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_356, plain, (![B_68]: (r3_lattices('#skF_4', B_68, '#skF_5') | ~r1_lattices('#skF_4', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_344])).
% 2.78/1.42  tff(c_367, plain, (![B_68]: (r3_lattices('#skF_4', B_68, '#skF_5') | ~r1_lattices('#skF_4', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_48, c_356])).
% 2.78/1.42  tff(c_368, plain, (![B_68]: (r3_lattices('#skF_4', B_68, '#skF_5') | ~r1_lattices('#skF_4', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_367])).
% 2.78/1.42  tff(c_369, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_368])).
% 2.78/1.42  tff(c_372, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_369])).
% 2.78/1.42  tff(c_375, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_372])).
% 2.78/1.42  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_375])).
% 2.78/1.42  tff(c_378, plain, (![B_68]: (~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_68, '#skF_5') | ~r1_lattices('#skF_4', B_68, '#skF_5') | ~m1_subset_1(B_68, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_368])).
% 2.78/1.42  tff(c_380, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_378])).
% 2.78/1.42  tff(c_383, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_2, c_380])).
% 2.78/1.42  tff(c_386, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_383])).
% 2.78/1.42  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_386])).
% 2.78/1.42  tff(c_390, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_378])).
% 2.78/1.42  tff(c_379, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 2.78/1.42  tff(c_55, plain, (![A_36]: (l1_lattices(A_36) | ~l3_lattices(A_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.42  tff(c_59, plain, (l1_lattices('#skF_4')), inference(resolution, [status(thm)], [c_48, c_55])).
% 2.78/1.42  tff(c_32, plain, (![A_23]: (m1_subset_1(k5_lattices(A_23), u1_struct_0(A_23)) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.78/1.42  tff(c_50, plain, (v13_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.78/1.42  tff(c_76, plain, (![A_50, C_51]: (k2_lattices(A_50, C_51, k5_lattices(A_50))=k5_lattices(A_50) | ~m1_subset_1(C_51, u1_struct_0(A_50)) | ~m1_subset_1(k5_lattices(A_50), u1_struct_0(A_50)) | ~v13_lattices(A_50) | ~l1_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.42  tff(c_86, plain, (k2_lattices('#skF_4', '#skF_5', k5_lattices('#skF_4'))=k5_lattices('#skF_4') | ~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v13_lattices('#skF_4') | ~l1_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_76])).
% 2.78/1.42  tff(c_93, plain, (k2_lattices('#skF_4', '#skF_5', k5_lattices('#skF_4'))=k5_lattices('#skF_4') | ~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50, c_86])).
% 2.78/1.42  tff(c_94, plain, (k2_lattices('#skF_4', '#skF_5', k5_lattices('#skF_4'))=k5_lattices('#skF_4') | ~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_93])).
% 2.78/1.42  tff(c_95, plain, (~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_94])).
% 2.78/1.42  tff(c_98, plain, (~l1_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_95])).
% 2.78/1.42  tff(c_101, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_98])).
% 2.78/1.42  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_101])).
% 2.78/1.42  tff(c_105, plain, (m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_94])).
% 2.78/1.42  tff(c_206, plain, (![A_56, C_57]: (k2_lattices(A_56, k5_lattices(A_56), C_57)=k5_lattices(A_56) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~m1_subset_1(k5_lattices(A_56), u1_struct_0(A_56)) | ~v13_lattices(A_56) | ~l1_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.42  tff(c_218, plain, (k2_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')=k5_lattices('#skF_4') | ~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~v13_lattices('#skF_4') | ~l1_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_206])).
% 2.78/1.42  tff(c_229, plain, (k2_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')=k5_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50, c_105, c_218])).
% 2.78/1.42  tff(c_230, plain, (k2_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')=k5_lattices('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_229])).
% 2.78/1.42  tff(c_157, plain, (![B_55]: (k1_lattices('#skF_4', k2_lattices('#skF_4', B_55, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_55, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_136])).
% 2.78/1.42  tff(c_180, plain, (k1_lattices('#skF_4', k2_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_105, c_157])).
% 2.78/1.42  tff(c_231, plain, (k1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_180])).
% 2.78/1.42  tff(c_391, plain, (![A_70, B_71, C_72]: (r1_lattices(A_70, B_71, k1_lattices(A_70, B_71, C_72)) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l3_lattices(A_70) | ~v9_lattices(A_70) | ~v8_lattices(A_70) | ~v6_lattices(A_70) | ~v5_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.42  tff(c_403, plain, (r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(k5_lattices('#skF_4'), u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | ~v5_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_231, c_391])).
% 2.78/1.42  tff(c_417, plain, (r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5') | ~v9_lattices('#skF_4') | ~v5_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_156, c_48, c_105, c_46, c_403])).
% 2.78/1.42  tff(c_418, plain, (r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5') | ~v9_lattices('#skF_4') | ~v5_lattices('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_417])).
% 2.78/1.42  tff(c_423, plain, (r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5') | ~v5_lattices('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_418])).
% 2.78/1.42  tff(c_424, plain, (~v5_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_423])).
% 2.78/1.42  tff(c_427, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_10, c_424])).
% 2.78/1.42  tff(c_430, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_427])).
% 2.78/1.42  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_430])).
% 2.78/1.42  tff(c_433, plain, (r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_423])).
% 2.78/1.42  tff(c_444, plain, (![B_75]: (r3_lattices('#skF_4', B_75, '#skF_5') | ~r1_lattices('#skF_4', B_75, '#skF_5') | ~m1_subset_1(B_75, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_378])).
% 2.78/1.42  tff(c_447, plain, (r3_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5') | ~r1_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_105, c_444])).
% 2.78/1.42  tff(c_469, plain, (r3_lattices('#skF_4', k5_lattices('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_447])).
% 2.78/1.42  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_469])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 80
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 7
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 3
% 2.78/1.42  #Demod        : 88
% 2.78/1.42  #Tautology    : 39
% 2.78/1.42  #SimpNegUnit  : 29
% 2.78/1.42  #BackRed      : 1
% 2.78/1.42  
% 2.78/1.42  #Partial instantiations: 0
% 2.78/1.42  #Strategies tried      : 1
% 2.78/1.42  
% 2.78/1.42  Timing (in seconds)
% 2.78/1.42  ----------------------
% 2.78/1.42  Preprocessing        : 0.33
% 2.78/1.42  Parsing              : 0.17
% 2.78/1.42  CNF conversion       : 0.03
% 2.78/1.42  Main loop            : 0.33
% 2.78/1.42  Inferencing          : 0.13
% 2.78/1.42  Reduction            : 0.10
% 2.78/1.42  Demodulation         : 0.07
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.06
% 2.78/1.42  Abstraction          : 0.02
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.70
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
