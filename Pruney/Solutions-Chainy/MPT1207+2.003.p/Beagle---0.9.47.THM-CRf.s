%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 731 expanded)
%              Number of leaves         :   33 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  240 (2484 expanded)
%              Number of equality atoms :   26 ( 233 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

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

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

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

tff(f_143,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_73,axiom,(
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

tff(f_128,axiom,(
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

tff(f_111,axiom,(
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

tff(c_38,plain,(
    ~ r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ! [A_28] :
      ( l1_lattices(A_28)
      | ~ l3_lattices(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_161,plain,(
    ! [A_45,B_46,C_47] :
      ( k4_lattices(A_45,B_46,C_47) = k2_lattices(A_45,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_lattices(A_45)
      | ~ v6_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_169,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,'#skF_3') = k2_lattices('#skF_2',B_46,'#skF_3')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_178,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,'#skF_3') = k2_lattices('#skF_2',B_46,'#skF_3')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_169])).

tff(c_179,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,'#skF_3') = k2_lattices('#skF_2',B_46,'#skF_3')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_178])).

tff(c_180,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_183,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_186,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_183])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_186])).

tff(c_190,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_12] :
      ( m1_subset_1(k5_lattices(A_12),u1_struct_0(A_12))
      | ~ l1_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    v13_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    ! [A_39,C_40] :
      ( k2_lattices(A_39,C_40,k5_lattices(A_39)) = k5_lattices(A_39)
      | ~ m1_subset_1(C_40,u1_struct_0(A_39))
      | ~ m1_subset_1(k5_lattices(A_39),u1_struct_0(A_39))
      | ~ v13_lattices(A_39)
      | ~ l1_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_78,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_44,c_73])).

tff(c_79,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_80,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_83,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_86,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_86])).

tff(c_90,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_115,plain,(
    ! [A_42,C_43] :
      ( k2_lattices(A_42,k5_lattices(A_42),C_43) = k5_lattices(A_42)
      | ~ m1_subset_1(C_43,u1_struct_0(A_42))
      | ~ m1_subset_1(k5_lattices(A_42),u1_struct_0(A_42))
      | ~ v13_lattices(A_42)
      | ~ l1_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_132,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_44,c_90,c_123])).

tff(c_133,plain,(
    k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_132])).

tff(c_191,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_2',B_48,'#skF_3') = k2_lattices('#skF_2',B_48,'#skF_3')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_194,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_191])).

tff(c_207,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_194])).

tff(c_222,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_lattices(A_49,k4_lattices(A_49,B_50,C_51),B_50)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | ~ v8_lattices(A_49)
      | ~ v6_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_225,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),k5_lattices('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_222])).

tff(c_227,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),k5_lattices('#skF_2'))
    | ~ v8_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_42,c_90,c_40,c_225])).

tff(c_228,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),k5_lattices('#skF_2'))
    | ~ v8_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_227])).

tff(c_239,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_242,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_245,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_245])).

tff(c_249,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_89,plain,(
    k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_163,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_46,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_90,c_161])).

tff(c_172,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_46,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_163])).

tff(c_173,plain,(
    ! [B_46] :
      ( k4_lattices('#skF_2',B_46,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_46,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_172])).

tff(c_259,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_2',B_55,k5_lattices('#skF_2')) = k2_lattices('#skF_2',B_55,k5_lattices('#skF_2'))
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_173])).

tff(c_273,plain,(
    k4_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_259])).

tff(c_285,plain,(
    k4_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_273])).

tff(c_36,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_lattices(A_20,k4_lattices(A_20,B_24,C_26),B_24)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l3_lattices(A_20)
      | ~ v8_lattices(A_20)
      | ~ v6_lattices(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_289,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v8_lattices('#skF_2')
    | ~ v6_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_36])).

tff(c_293,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_249,c_42,c_40,c_90,c_289])).

tff(c_294,plain,(
    r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_293])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_453,plain,(
    ! [A_63,B_64,C_65] :
      ( r3_lattices(A_63,B_64,C_65)
      | ~ r1_lattices(A_63,B_64,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l3_lattices(A_63)
      | ~ v9_lattices(A_63)
      | ~ v8_lattices(A_63)
      | ~ v6_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_461,plain,(
    ! [B_64] :
      ( r3_lattices('#skF_2',B_64,'#skF_3')
      | ~ r1_lattices('#skF_2',B_64,'#skF_3')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_453])).

tff(c_470,plain,(
    ! [B_64] :
      ( r3_lattices('#skF_2',B_64,'#skF_3')
      | ~ r1_lattices('#skF_2',B_64,'#skF_3')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_249,c_42,c_461])).

tff(c_471,plain,(
    ! [B_64] :
      ( r3_lattices('#skF_2',B_64,'#skF_3')
      | ~ r1_lattices('#skF_2',B_64,'#skF_3')
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_470])).

tff(c_472,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_475,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_472])).

tff(c_478,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_475])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_478])).

tff(c_492,plain,(
    ! [B_67] :
      ( r3_lattices('#skF_2',B_67,'#skF_3')
      | ~ r1_lattices('#skF_2',B_67,'#skF_3')
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_495,plain,
    ( r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_492])).

tff(c_509,plain,(
    r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_495])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 2.92/1.43  
% 2.92/1.43  %Foreground sorts:
% 2.92/1.43  
% 2.92/1.43  
% 2.92/1.43  %Background operators:
% 2.92/1.43  
% 2.92/1.43  
% 2.92/1.43  %Foreground operators:
% 2.92/1.43  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.92/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.43  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.92/1.43  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.92/1.43  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.43  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.92/1.43  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.92/1.43  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.92/1.43  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.92/1.43  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.92/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.43  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.92/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.43  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.92/1.43  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.43  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.92/1.43  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.43  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.92/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.92/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.43  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.92/1.43  
% 2.92/1.45  tff(f_143, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattices)).
% 2.92/1.45  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.92/1.45  tff(f_79, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.92/1.45  tff(f_92, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.92/1.45  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.92/1.45  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 2.92/1.45  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 2.92/1.45  tff(f_111, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.92/1.45  tff(c_38, plain, (~r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_42, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_46, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.45  tff(c_49, plain, (![A_28]: (l1_lattices(A_28) | ~l3_lattices(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.92/1.45  tff(c_53, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.92/1.45  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_161, plain, (![A_45, B_46, C_47]: (k4_lattices(A_45, B_46, C_47)=k2_lattices(A_45, B_46, C_47) | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_lattices(A_45) | ~v6_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.45  tff(c_169, plain, (![B_46]: (k4_lattices('#skF_2', B_46, '#skF_3')=k2_lattices('#skF_2', B_46, '#skF_3') | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_161])).
% 2.92/1.45  tff(c_178, plain, (![B_46]: (k4_lattices('#skF_2', B_46, '#skF_3')=k2_lattices('#skF_2', B_46, '#skF_3') | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_169])).
% 2.92/1.45  tff(c_179, plain, (![B_46]: (k4_lattices('#skF_2', B_46, '#skF_3')=k2_lattices('#skF_2', B_46, '#skF_3') | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_178])).
% 2.92/1.45  tff(c_180, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_179])).
% 2.92/1.45  tff(c_183, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_180])).
% 2.92/1.45  tff(c_186, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_183])).
% 2.92/1.45  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_186])).
% 2.92/1.45  tff(c_190, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_179])).
% 2.92/1.45  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.45  tff(c_24, plain, (![A_12]: (m1_subset_1(k5_lattices(A_12), u1_struct_0(A_12)) | ~l1_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.45  tff(c_44, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.92/1.45  tff(c_67, plain, (![A_39, C_40]: (k2_lattices(A_39, C_40, k5_lattices(A_39))=k5_lattices(A_39) | ~m1_subset_1(C_40, u1_struct_0(A_39)) | ~m1_subset_1(k5_lattices(A_39), u1_struct_0(A_39)) | ~v13_lattices(A_39) | ~l1_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.45  tff(c_73, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.92/1.45  tff(c_78, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_44, c_73])).
% 2.92/1.45  tff(c_79, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_78])).
% 2.92/1.45  tff(c_80, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.92/1.45  tff(c_83, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_80])).
% 2.92/1.45  tff(c_86, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_83])).
% 2.92/1.45  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_86])).
% 2.92/1.45  tff(c_90, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_79])).
% 2.92/1.45  tff(c_115, plain, (![A_42, C_43]: (k2_lattices(A_42, k5_lattices(A_42), C_43)=k5_lattices(A_42) | ~m1_subset_1(C_43, u1_struct_0(A_42)) | ~m1_subset_1(k5_lattices(A_42), u1_struct_0(A_42)) | ~v13_lattices(A_42) | ~l1_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.45  tff(c_123, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.92/1.45  tff(c_132, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_44, c_90, c_123])).
% 2.92/1.45  tff(c_133, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_132])).
% 2.92/1.45  tff(c_191, plain, (![B_48]: (k4_lattices('#skF_2', B_48, '#skF_3')=k2_lattices('#skF_2', B_48, '#skF_3') | ~m1_subset_1(B_48, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 2.92/1.45  tff(c_194, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_90, c_191])).
% 2.92/1.45  tff(c_207, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_194])).
% 2.92/1.45  tff(c_222, plain, (![A_49, B_50, C_51]: (r1_lattices(A_49, k4_lattices(A_49, B_50, C_51), B_50) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v8_lattices(A_49) | ~v6_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.92/1.45  tff(c_225, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), k5_lattices('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_222])).
% 2.92/1.45  tff(c_227, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), k5_lattices('#skF_2')) | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_42, c_90, c_40, c_225])).
% 2.92/1.45  tff(c_228, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), k5_lattices('#skF_2')) | ~v8_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_227])).
% 2.92/1.45  tff(c_239, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_228])).
% 2.92/1.45  tff(c_242, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_239])).
% 2.92/1.45  tff(c_245, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_242])).
% 2.92/1.45  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_245])).
% 2.92/1.45  tff(c_249, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_228])).
% 2.92/1.45  tff(c_89, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_79])).
% 2.92/1.45  tff(c_163, plain, (![B_46]: (k4_lattices('#skF_2', B_46, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_46, k5_lattices('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_161])).
% 2.92/1.45  tff(c_172, plain, (![B_46]: (k4_lattices('#skF_2', B_46, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_46, k5_lattices('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_163])).
% 2.92/1.45  tff(c_173, plain, (![B_46]: (k4_lattices('#skF_2', B_46, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_46, k5_lattices('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_172])).
% 2.92/1.45  tff(c_259, plain, (![B_55]: (k4_lattices('#skF_2', B_55, k5_lattices('#skF_2'))=k2_lattices('#skF_2', B_55, k5_lattices('#skF_2')) | ~m1_subset_1(B_55, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_173])).
% 2.92/1.45  tff(c_273, plain, (k4_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_259])).
% 2.92/1.45  tff(c_285, plain, (k4_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_273])).
% 2.92/1.45  tff(c_36, plain, (![A_20, B_24, C_26]: (r1_lattices(A_20, k4_lattices(A_20, B_24, C_26), B_24) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l3_lattices(A_20) | ~v8_lattices(A_20) | ~v6_lattices(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.92/1.45  tff(c_289, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_36])).
% 2.92/1.45  tff(c_293, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_249, c_42, c_40, c_90, c_289])).
% 2.92/1.45  tff(c_294, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_293])).
% 2.92/1.45  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.45  tff(c_453, plain, (![A_63, B_64, C_65]: (r3_lattices(A_63, B_64, C_65) | ~r1_lattices(A_63, B_64, C_65) | ~m1_subset_1(C_65, u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l3_lattices(A_63) | ~v9_lattices(A_63) | ~v8_lattices(A_63) | ~v6_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.92/1.45  tff(c_461, plain, (![B_64]: (r3_lattices('#skF_2', B_64, '#skF_3') | ~r1_lattices('#skF_2', B_64, '#skF_3') | ~m1_subset_1(B_64, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_453])).
% 2.92/1.45  tff(c_470, plain, (![B_64]: (r3_lattices('#skF_2', B_64, '#skF_3') | ~r1_lattices('#skF_2', B_64, '#skF_3') | ~m1_subset_1(B_64, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_249, c_42, c_461])).
% 2.92/1.45  tff(c_471, plain, (![B_64]: (r3_lattices('#skF_2', B_64, '#skF_3') | ~r1_lattices('#skF_2', B_64, '#skF_3') | ~m1_subset_1(B_64, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_470])).
% 2.92/1.45  tff(c_472, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_471])).
% 2.92/1.45  tff(c_475, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_472])).
% 2.92/1.45  tff(c_478, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_475])).
% 2.92/1.45  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_478])).
% 2.92/1.45  tff(c_492, plain, (![B_67]: (r3_lattices('#skF_2', B_67, '#skF_3') | ~r1_lattices('#skF_2', B_67, '#skF_3') | ~m1_subset_1(B_67, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_471])).
% 2.92/1.45  tff(c_495, plain, (r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_90, c_492])).
% 2.92/1.45  tff(c_509, plain, (r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_495])).
% 2.92/1.45  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_509])).
% 2.92/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  
% 2.92/1.45  Inference rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Ref     : 0
% 2.92/1.45  #Sup     : 83
% 2.92/1.45  #Fact    : 0
% 2.92/1.45  #Define  : 0
% 2.92/1.45  #Split   : 7
% 2.92/1.45  #Chain   : 0
% 2.92/1.45  #Close   : 0
% 2.92/1.45  
% 2.92/1.45  Ordering : KBO
% 2.92/1.45  
% 2.92/1.45  Simplification rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Subsume      : 3
% 2.92/1.45  #Demod        : 145
% 2.92/1.45  #Tautology    : 48
% 2.92/1.45  #SimpNegUnit  : 36
% 2.92/1.45  #BackRed      : 14
% 2.92/1.45  
% 2.92/1.45  #Partial instantiations: 0
% 2.92/1.45  #Strategies tried      : 1
% 2.92/1.45  
% 2.92/1.45  Timing (in seconds)
% 2.92/1.45  ----------------------
% 2.92/1.46  Preprocessing        : 0.35
% 2.92/1.46  Parsing              : 0.18
% 2.92/1.46  CNF conversion       : 0.03
% 2.92/1.46  Main loop            : 0.31
% 2.92/1.46  Inferencing          : 0.11
% 2.92/1.46  Reduction            : 0.10
% 2.92/1.46  Demodulation         : 0.07
% 2.92/1.46  BG Simplification    : 0.03
% 2.92/1.46  Subsumption          : 0.06
% 2.92/1.46  Abstraction          : 0.02
% 2.92/1.46  MUC search           : 0.00
% 2.92/1.46  Cooper               : 0.00
% 2.92/1.46  Total                : 0.71
% 2.92/1.46  Index Insertion      : 0.00
% 2.92/1.46  Index Deletion       : 0.00
% 2.92/1.46  Index Matching       : 0.00
% 2.92/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
