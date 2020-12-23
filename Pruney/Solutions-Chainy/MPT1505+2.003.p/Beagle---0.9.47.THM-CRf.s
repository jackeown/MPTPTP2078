%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:45 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 345 expanded)
%              Number of leaves         :   39 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  356 (1503 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_189,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r2_hidden(B,C)
               => ( r3_lattices(A,B,k15_lattice3(A,C))
                  & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

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

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_70,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_447,plain,(
    ! [A_186,B_187] :
      ( k15_lattice3(A_186,a_2_1_lattice3(A_186,B_187)) = k16_lattice3(A_186,B_187)
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k15_lattice3(A_64,B_65),u1_struct_0(A_64))
      | ~ l3_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_453,plain,(
    ! [A_186,B_187] :
      ( m1_subset_1(k16_lattice3(A_186,B_187),u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186)
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_48])).

tff(c_466,plain,(
    ! [A_208,C_209] :
      ( r3_lattice3(A_208,k16_lattice3(A_208,C_209),C_209)
      | ~ m1_subset_1(k16_lattice3(A_208,C_209),u1_struct_0(A_208))
      | ~ l3_lattices(A_208)
      | ~ v4_lattice3(A_208)
      | ~ v10_lattices(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_469,plain,(
    ! [A_186,B_187] :
      ( r3_lattice3(A_186,k16_lattice3(A_186,B_187),B_187)
      | ~ v4_lattice3(A_186)
      | ~ v10_lattices(A_186)
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_453,c_466])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_536,plain,(
    ! [A_223,B_224,D_225,C_226] :
      ( r1_lattices(A_223,B_224,D_225)
      | ~ r2_hidden(D_225,C_226)
      | ~ m1_subset_1(D_225,u1_struct_0(A_223))
      | ~ r3_lattice3(A_223,B_224,C_226)
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l3_lattices(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_571,plain,(
    ! [A_230,B_231] :
      ( r1_lattices(A_230,B_231,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_230))
      | ~ r3_lattice3(A_230,B_231,'#skF_7')
      | ~ m1_subset_1(B_231,u1_struct_0(A_230))
      | ~ l3_lattices(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_62,c_536])).

tff(c_573,plain,(
    ! [B_231] :
      ( r1_lattices('#skF_5',B_231,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_231,'#skF_7')
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_571])).

tff(c_576,plain,(
    ! [B_231] :
      ( r1_lattices('#skF_5',B_231,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_231,'#skF_7')
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_573])).

tff(c_578,plain,(
    ! [B_232] :
      ( r1_lattices('#skF_5',B_232,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_232,'#skF_7')
      | ~ m1_subset_1(B_232,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_576])).

tff(c_590,plain,(
    ! [B_187] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_453,c_578])).

tff(c_608,plain,(
    ! [B_187] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_590])).

tff(c_616,plain,(
    ! [B_233] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_233),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_233),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_608])).

tff(c_620,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_469,c_616])).

tff(c_623,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_620])).

tff(c_624,plain,(
    r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_623])).

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

tff(c_625,plain,(
    ! [A_234,B_235,C_236] :
      ( r3_lattices(A_234,B_235,C_236)
      | ~ r1_lattices(A_234,B_235,C_236)
      | ~ m1_subset_1(C_236,u1_struct_0(A_234))
      | ~ m1_subset_1(B_235,u1_struct_0(A_234))
      | ~ l3_lattices(A_234)
      | ~ v9_lattices(A_234)
      | ~ v8_lattices(A_234)
      | ~ v6_lattices(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_635,plain,(
    ! [B_235] :
      ( r3_lattices('#skF_5',B_235,'#skF_6')
      | ~ r1_lattices('#skF_5',B_235,'#skF_6')
      | ~ m1_subset_1(B_235,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_625])).

tff(c_642,plain,(
    ! [B_235] :
      ( r3_lattices('#skF_5',B_235,'#skF_6')
      | ~ r1_lattices('#skF_5',B_235,'#skF_6')
      | ~ m1_subset_1(B_235,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_635])).

tff(c_643,plain,(
    ! [B_235] :
      ( r3_lattices('#skF_5',B_235,'#skF_6')
      | ~ r1_lattices('#skF_5',B_235,'#skF_6')
      | ~ m1_subset_1(B_235,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_642])).

tff(c_660,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_663,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_660])).

tff(c_666,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_663])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_666])).

tff(c_669,plain,(
    ! [B_235] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_235,'#skF_6')
      | ~ r1_lattices('#skF_5',B_235,'#skF_6')
      | ~ m1_subset_1(B_235,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_671,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_674,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_671])).

tff(c_677,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_674])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_677])).

tff(c_680,plain,(
    ! [B_235] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_235,'#skF_6')
      | ~ r1_lattices('#skF_5',B_235,'#skF_6')
      | ~ m1_subset_1(B_235,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_689,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_680])).

tff(c_692,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_689])).

tff(c_695,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_692])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_695])).

tff(c_701,plain,(
    ! [B_244] :
      ( r3_lattices('#skF_5',B_244,'#skF_6')
      | ~ r1_lattices('#skF_5',B_244,'#skF_6')
      | ~ m1_subset_1(B_244,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_680])).

tff(c_713,plain,(
    ! [B_187] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_453,c_701])).

tff(c_731,plain,(
    ! [B_187] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_187),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_713])).

tff(c_739,plain,(
    ! [B_245] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_245),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_245),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_731])).

tff(c_268,plain,(
    ! [A_151,B_152,C_153] :
      ( r3_lattices(A_151,B_152,C_153)
      | ~ r1_lattices(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l3_lattices(A_151)
      | ~ v9_lattices(A_151)
      | ~ v8_lattices(A_151)
      | ~ v6_lattices(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_278,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_268])).

tff(c_285,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_278])).

tff(c_286,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_285])).

tff(c_295,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_298,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_295])).

tff(c_301,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_301])).

tff(c_305,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_304,plain,(
    ! [B_152] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_307,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_310,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_307])).

tff(c_313,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_310])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_313])).

tff(c_316,plain,(
    ! [B_152] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_318,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_322,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_325,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_322])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_325])).

tff(c_329,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_317,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_100,plain,(
    ! [A_122,B_123] :
      ( r4_lattice3(A_122,k15_lattice3(A_122,B_123),B_123)
      | ~ m1_subset_1(k15_lattice3(A_122,B_123),u1_struct_0(A_122))
      | ~ v4_lattice3(A_122)
      | ~ v10_lattices(A_122)
      | ~ l3_lattices(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_105,plain,(
    ! [A_64,B_65] :
      ( r4_lattice3(A_64,k15_lattice3(A_64,B_65),B_65)
      | ~ v4_lattice3(A_64)
      | ~ v10_lattices(A_64)
      | ~ l3_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_180,plain,(
    ! [A_140,D_141,B_142,C_143] :
      ( r1_lattices(A_140,D_141,B_142)
      | ~ r2_hidden(D_141,C_143)
      | ~ m1_subset_1(D_141,u1_struct_0(A_140))
      | ~ r4_lattice3(A_140,B_142,C_143)
      | ~ m1_subset_1(B_142,u1_struct_0(A_140))
      | ~ l3_lattices(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_206,plain,(
    ! [A_146,B_147] :
      ( r1_lattices(A_146,'#skF_6',B_147)
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_146))
      | ~ r4_lattice3(A_146,B_147,'#skF_7')
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l3_lattices(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_208,plain,(
    ! [B_147] :
      ( r1_lattices('#skF_5','#skF_6',B_147)
      | ~ r4_lattice3('#skF_5',B_147,'#skF_7')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_206])).

tff(c_211,plain,(
    ! [B_147] :
      ( r1_lattices('#skF_5','#skF_6',B_147)
      | ~ r4_lattice3('#skF_5',B_147,'#skF_7')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_208])).

tff(c_213,plain,(
    ! [B_148] :
      ( r1_lattices('#skF_5','#skF_6',B_148)
      | ~ r4_lattice3('#skF_5',B_148,'#skF_7')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_211])).

tff(c_229,plain,(
    ! [B_65] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_65))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_65),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_213])).

tff(c_247,plain,(
    ! [B_65] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_65))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_65),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_229])).

tff(c_252,plain,(
    ! [B_150] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_150))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_150),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_247])).

tff(c_256,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_252])).

tff(c_263,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_256])).

tff(c_264,plain,(
    r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_263])).

tff(c_426,plain,(
    ! [A_178,B_179,B_180] :
      ( r3_lattices(A_178,B_179,k15_lattice3(A_178,B_180))
      | ~ r1_lattices(A_178,B_179,k15_lattice3(A_178,B_180))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ v9_lattices(A_178)
      | ~ v8_lattices(A_178)
      | ~ v6_lattices(A_178)
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_48,c_268])).

tff(c_60,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_76,plain,(
    ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_431,plain,
    ( ~ r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_426,c_76])).

tff(c_438,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_305,c_329,c_317,c_64,c_264,c_431])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_438])).

tff(c_441,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_744,plain,(
    ~ r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_739,c_441])).

tff(c_752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.22/1.51  
% 3.22/1.51  %Foreground sorts:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Background operators:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Foreground operators:
% 3.22/1.51  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.22/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.22/1.51  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.51  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.22/1.51  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.22/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.51  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.22/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.51  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.22/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.51  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.22/1.51  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.22/1.51  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 3.22/1.51  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.22/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.22/1.51  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.22/1.51  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.22/1.51  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.22/1.51  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.51  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.22/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.51  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.22/1.51  
% 3.22/1.53  tff(f_189, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.22/1.53  tff(f_138, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 3.22/1.53  tff(f_145, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 3.22/1.53  tff(f_169, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 3.22/1.53  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 3.22/1.53  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.22/1.53  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.22/1.53  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 3.22/1.53  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 3.22/1.53  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_66, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_70, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_68, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_447, plain, (![A_186, B_187]: (k15_lattice3(A_186, a_2_1_lattice3(A_186, B_187))=k16_lattice3(A_186, B_187) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.53  tff(c_48, plain, (![A_64, B_65]: (m1_subset_1(k15_lattice3(A_64, B_65), u1_struct_0(A_64)) | ~l3_lattices(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.22/1.53  tff(c_453, plain, (![A_186, B_187]: (m1_subset_1(k16_lattice3(A_186, B_187), u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(superposition, [status(thm), theory('equality')], [c_447, c_48])).
% 3.22/1.53  tff(c_466, plain, (![A_208, C_209]: (r3_lattice3(A_208, k16_lattice3(A_208, C_209), C_209) | ~m1_subset_1(k16_lattice3(A_208, C_209), u1_struct_0(A_208)) | ~l3_lattices(A_208) | ~v4_lattice3(A_208) | ~v10_lattices(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.22/1.53  tff(c_469, plain, (![A_186, B_187]: (r3_lattice3(A_186, k16_lattice3(A_186, B_187), B_187) | ~v4_lattice3(A_186) | ~v10_lattices(A_186) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_453, c_466])).
% 3.22/1.53  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_536, plain, (![A_223, B_224, D_225, C_226]: (r1_lattices(A_223, B_224, D_225) | ~r2_hidden(D_225, C_226) | ~m1_subset_1(D_225, u1_struct_0(A_223)) | ~r3_lattice3(A_223, B_224, C_226) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~l3_lattices(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.53  tff(c_571, plain, (![A_230, B_231]: (r1_lattices(A_230, B_231, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_230)) | ~r3_lattice3(A_230, B_231, '#skF_7') | ~m1_subset_1(B_231, u1_struct_0(A_230)) | ~l3_lattices(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_62, c_536])).
% 3.22/1.53  tff(c_573, plain, (![B_231]: (r1_lattices('#skF_5', B_231, '#skF_6') | ~r3_lattice3('#skF_5', B_231, '#skF_7') | ~m1_subset_1(B_231, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_571])).
% 3.22/1.53  tff(c_576, plain, (![B_231]: (r1_lattices('#skF_5', B_231, '#skF_6') | ~r3_lattice3('#skF_5', B_231, '#skF_7') | ~m1_subset_1(B_231, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_573])).
% 3.22/1.53  tff(c_578, plain, (![B_232]: (r1_lattices('#skF_5', B_232, '#skF_6') | ~r3_lattice3('#skF_5', B_232, '#skF_7') | ~m1_subset_1(B_232, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_576])).
% 3.22/1.53  tff(c_590, plain, (![B_187]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_453, c_578])).
% 3.22/1.53  tff(c_608, plain, (![B_187]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_590])).
% 3.22/1.53  tff(c_616, plain, (![B_233]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_233), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_233), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_608])).
% 3.22/1.53  tff(c_620, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_469, c_616])).
% 3.22/1.53  tff(c_623, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_620])).
% 3.22/1.53  tff(c_624, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_623])).
% 3.22/1.53  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.53  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.53  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.53  tff(c_625, plain, (![A_234, B_235, C_236]: (r3_lattices(A_234, B_235, C_236) | ~r1_lattices(A_234, B_235, C_236) | ~m1_subset_1(C_236, u1_struct_0(A_234)) | ~m1_subset_1(B_235, u1_struct_0(A_234)) | ~l3_lattices(A_234) | ~v9_lattices(A_234) | ~v8_lattices(A_234) | ~v6_lattices(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.53  tff(c_635, plain, (![B_235]: (r3_lattices('#skF_5', B_235, '#skF_6') | ~r1_lattices('#skF_5', B_235, '#skF_6') | ~m1_subset_1(B_235, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_625])).
% 3.22/1.53  tff(c_642, plain, (![B_235]: (r3_lattices('#skF_5', B_235, '#skF_6') | ~r1_lattices('#skF_5', B_235, '#skF_6') | ~m1_subset_1(B_235, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_635])).
% 3.22/1.53  tff(c_643, plain, (![B_235]: (r3_lattices('#skF_5', B_235, '#skF_6') | ~r1_lattices('#skF_5', B_235, '#skF_6') | ~m1_subset_1(B_235, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_642])).
% 3.22/1.53  tff(c_660, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_643])).
% 3.22/1.53  tff(c_663, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_660])).
% 3.22/1.53  tff(c_666, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_663])).
% 3.22/1.53  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_666])).
% 3.22/1.53  tff(c_669, plain, (![B_235]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_235, '#skF_6') | ~r1_lattices('#skF_5', B_235, '#skF_6') | ~m1_subset_1(B_235, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_643])).
% 3.22/1.53  tff(c_671, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_669])).
% 3.22/1.53  tff(c_674, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_671])).
% 3.22/1.53  tff(c_677, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_674])).
% 3.22/1.53  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_677])).
% 3.22/1.53  tff(c_680, plain, (![B_235]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_235, '#skF_6') | ~r1_lattices('#skF_5', B_235, '#skF_6') | ~m1_subset_1(B_235, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_669])).
% 3.22/1.53  tff(c_689, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_680])).
% 3.22/1.53  tff(c_692, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_689])).
% 3.22/1.53  tff(c_695, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_692])).
% 3.22/1.53  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_695])).
% 3.22/1.53  tff(c_701, plain, (![B_244]: (r3_lattices('#skF_5', B_244, '#skF_6') | ~r1_lattices('#skF_5', B_244, '#skF_6') | ~m1_subset_1(B_244, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_680])).
% 3.22/1.53  tff(c_713, plain, (![B_187]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_453, c_701])).
% 3.22/1.53  tff(c_731, plain, (![B_187]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_187), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_713])).
% 3.22/1.53  tff(c_739, plain, (![B_245]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_245), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_245), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_731])).
% 3.22/1.53  tff(c_268, plain, (![A_151, B_152, C_153]: (r3_lattices(A_151, B_152, C_153) | ~r1_lattices(A_151, B_152, C_153) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l3_lattices(A_151) | ~v9_lattices(A_151) | ~v8_lattices(A_151) | ~v6_lattices(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.53  tff(c_278, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_268])).
% 3.22/1.53  tff(c_285, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_278])).
% 3.22/1.53  tff(c_286, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_285])).
% 3.22/1.53  tff(c_295, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_286])).
% 3.22/1.53  tff(c_298, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_295])).
% 3.22/1.53  tff(c_301, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_298])).
% 3.22/1.53  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_301])).
% 3.22/1.53  tff(c_305, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_286])).
% 3.22/1.53  tff(c_304, plain, (![B_152]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_286])).
% 3.22/1.53  tff(c_307, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_304])).
% 3.22/1.53  tff(c_310, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_307])).
% 3.22/1.53  tff(c_313, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_310])).
% 3.22/1.53  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_313])).
% 3.22/1.53  tff(c_316, plain, (![B_152]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_304])).
% 3.22/1.53  tff(c_318, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_316])).
% 3.22/1.53  tff(c_322, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_318])).
% 3.22/1.53  tff(c_325, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_322])).
% 3.22/1.53  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_325])).
% 3.22/1.53  tff(c_329, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_316])).
% 3.22/1.53  tff(c_317, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_304])).
% 3.22/1.53  tff(c_100, plain, (![A_122, B_123]: (r4_lattice3(A_122, k15_lattice3(A_122, B_123), B_123) | ~m1_subset_1(k15_lattice3(A_122, B_123), u1_struct_0(A_122)) | ~v4_lattice3(A_122) | ~v10_lattices(A_122) | ~l3_lattices(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.53  tff(c_105, plain, (![A_64, B_65]: (r4_lattice3(A_64, k15_lattice3(A_64, B_65), B_65) | ~v4_lattice3(A_64) | ~v10_lattices(A_64) | ~l3_lattices(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.22/1.53  tff(c_180, plain, (![A_140, D_141, B_142, C_143]: (r1_lattices(A_140, D_141, B_142) | ~r2_hidden(D_141, C_143) | ~m1_subset_1(D_141, u1_struct_0(A_140)) | ~r4_lattice3(A_140, B_142, C_143) | ~m1_subset_1(B_142, u1_struct_0(A_140)) | ~l3_lattices(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.22/1.53  tff(c_206, plain, (![A_146, B_147]: (r1_lattices(A_146, '#skF_6', B_147) | ~m1_subset_1('#skF_6', u1_struct_0(A_146)) | ~r4_lattice3(A_146, B_147, '#skF_7') | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l3_lattices(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_62, c_180])).
% 3.22/1.53  tff(c_208, plain, (![B_147]: (r1_lattices('#skF_5', '#skF_6', B_147) | ~r4_lattice3('#skF_5', B_147, '#skF_7') | ~m1_subset_1(B_147, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_206])).
% 3.22/1.53  tff(c_211, plain, (![B_147]: (r1_lattices('#skF_5', '#skF_6', B_147) | ~r4_lattice3('#skF_5', B_147, '#skF_7') | ~m1_subset_1(B_147, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_208])).
% 3.22/1.53  tff(c_213, plain, (![B_148]: (r1_lattices('#skF_5', '#skF_6', B_148) | ~r4_lattice3('#skF_5', B_148, '#skF_7') | ~m1_subset_1(B_148, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_211])).
% 3.22/1.53  tff(c_229, plain, (![B_65]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_65)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_65), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_213])).
% 3.22/1.53  tff(c_247, plain, (![B_65]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_65)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_65), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_229])).
% 3.22/1.53  tff(c_252, plain, (![B_150]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_150)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_150), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_247])).
% 3.22/1.53  tff(c_256, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_105, c_252])).
% 3.22/1.53  tff(c_263, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_256])).
% 3.22/1.53  tff(c_264, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_263])).
% 3.22/1.53  tff(c_426, plain, (![A_178, B_179, B_180]: (r3_lattices(A_178, B_179, k15_lattice3(A_178, B_180)) | ~r1_lattices(A_178, B_179, k15_lattice3(A_178, B_180)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~v9_lattices(A_178) | ~v8_lattices(A_178) | ~v6_lattices(A_178) | ~l3_lattices(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_48, c_268])).
% 3.22/1.53  tff(c_60, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.22/1.53  tff(c_76, plain, (~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.22/1.53  tff(c_431, plain, (~r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_426, c_76])).
% 3.22/1.53  tff(c_438, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_305, c_329, c_317, c_64, c_264, c_431])).
% 3.22/1.53  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_438])).
% 3.22/1.53  tff(c_441, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 3.22/1.53  tff(c_744, plain, (~r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_739, c_441])).
% 3.22/1.53  tff(c_752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_624, c_744])).
% 3.22/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.53  
% 3.22/1.53  Inference rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Ref     : 0
% 3.22/1.53  #Sup     : 102
% 3.22/1.53  #Fact    : 0
% 3.22/1.53  #Define  : 0
% 3.22/1.53  #Split   : 13
% 3.22/1.53  #Chain   : 0
% 3.22/1.53  #Close   : 0
% 3.22/1.53  
% 3.22/1.53  Ordering : KBO
% 3.22/1.53  
% 3.22/1.53  Simplification rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Subsume      : 10
% 3.22/1.53  #Demod        : 106
% 3.22/1.53  #Tautology    : 12
% 3.22/1.53  #SimpNegUnit  : 58
% 3.22/1.53  #BackRed      : 0
% 3.22/1.53  
% 3.22/1.53  #Partial instantiations: 0
% 3.22/1.53  #Strategies tried      : 1
% 3.22/1.53  
% 3.22/1.53  Timing (in seconds)
% 3.22/1.53  ----------------------
% 3.22/1.53  Preprocessing        : 0.35
% 3.22/1.53  Parsing              : 0.18
% 3.22/1.53  CNF conversion       : 0.03
% 3.22/1.53  Main loop            : 0.39
% 3.22/1.53  Inferencing          : 0.15
% 3.22/1.53  Reduction            : 0.11
% 3.22/1.53  Demodulation         : 0.07
% 3.22/1.53  BG Simplification    : 0.03
% 3.22/1.54  Subsumption          : 0.07
% 3.22/1.54  Abstraction          : 0.02
% 3.22/1.54  MUC search           : 0.00
% 3.22/1.54  Cooper               : 0.00
% 3.22/1.54  Total                : 0.78
% 3.22/1.54  Index Insertion      : 0.00
% 3.22/1.54  Index Deletion       : 0.00
% 3.22/1.54  Index Matching       : 0.00
% 3.22/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
