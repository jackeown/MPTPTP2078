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

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 335 expanded)
%              Number of leaves         :   38 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  351 (1470 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(f_188,negated_conjecture,(
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

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_168,axiom,(
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

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_70,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k16_lattice3(A_63,B_64),u1_struct_0(A_63))
      | ~ l3_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_376,plain,(
    ! [A_194,C_195] :
      ( r3_lattice3(A_194,k16_lattice3(A_194,C_195),C_195)
      | ~ m1_subset_1(k16_lattice3(A_194,C_195),u1_struct_0(A_194))
      | ~ l3_lattices(A_194)
      | ~ v4_lattice3(A_194)
      | ~ v10_lattices(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_379,plain,(
    ! [A_63,B_64] :
      ( r3_lattice3(A_63,k16_lattice3(A_63,B_64),B_64)
      | ~ v4_lattice3(A_63)
      | ~ v10_lattices(A_63)
      | ~ l3_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_376])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_440,plain,(
    ! [A_209,B_210,D_211,C_212] :
      ( r1_lattices(A_209,B_210,D_211)
      | ~ r2_hidden(D_211,C_212)
      | ~ m1_subset_1(D_211,u1_struct_0(A_209))
      | ~ r3_lattice3(A_209,B_210,C_212)
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l3_lattices(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_461,plain,(
    ! [A_215,B_216] :
      ( r1_lattices(A_215,B_216,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_215))
      | ~ r3_lattice3(A_215,B_216,'#skF_7')
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l3_lattices(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_62,c_440])).

tff(c_463,plain,(
    ! [B_216] :
      ( r1_lattices('#skF_5',B_216,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_216,'#skF_7')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_461])).

tff(c_466,plain,(
    ! [B_216] :
      ( r1_lattices('#skF_5',B_216,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_216,'#skF_7')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_463])).

tff(c_468,plain,(
    ! [B_217] :
      ( r1_lattices('#skF_5',B_217,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_217,'#skF_7')
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_466])).

tff(c_480,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_468])).

tff(c_498,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_480])).

tff(c_525,plain,(
    ! [B_221] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_221),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_221),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_498])).

tff(c_529,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_379,c_525])).

tff(c_532,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_529])).

tff(c_533,plain,(
    r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_532])).

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

tff(c_506,plain,(
    ! [A_218,B_219,C_220] :
      ( r3_lattices(A_218,B_219,C_220)
      | ~ r1_lattices(A_218,B_219,C_220)
      | ~ m1_subset_1(C_220,u1_struct_0(A_218))
      | ~ m1_subset_1(B_219,u1_struct_0(A_218))
      | ~ l3_lattices(A_218)
      | ~ v9_lattices(A_218)
      | ~ v8_lattices(A_218)
      | ~ v6_lattices(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_516,plain,(
    ! [B_219] :
      ( r3_lattices('#skF_5',B_219,'#skF_6')
      | ~ r1_lattices('#skF_5',B_219,'#skF_6')
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_506])).

tff(c_523,plain,(
    ! [B_219] :
      ( r3_lattices('#skF_5',B_219,'#skF_6')
      | ~ r1_lattices('#skF_5',B_219,'#skF_6')
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_516])).

tff(c_524,plain,(
    ! [B_219] :
      ( r3_lattices('#skF_5',B_219,'#skF_6')
      | ~ r1_lattices('#skF_5',B_219,'#skF_6')
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_523])).

tff(c_535,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_538,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_541,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_538])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_541])).

tff(c_544,plain,(
    ! [B_219] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_219,'#skF_6')
      | ~ r1_lattices('#skF_5',B_219,'#skF_6')
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_546,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_549,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_546])).

tff(c_552,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_549])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_552])).

tff(c_555,plain,(
    ! [B_219] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_219,'#skF_6')
      | ~ r1_lattices('#skF_5',B_219,'#skF_6')
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_564,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_555])).

tff(c_567,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_564])).

tff(c_570,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_567])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_570])).

tff(c_576,plain,(
    ! [B_228] :
      ( r3_lattices('#skF_5',B_228,'#skF_6')
      | ~ r1_lattices('#skF_5',B_228,'#skF_6')
      | ~ m1_subset_1(B_228,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_555])).

tff(c_588,plain,(
    ! [B_64] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_576])).

tff(c_606,plain,(
    ! [B_64] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_64),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_588])).

tff(c_621,plain,(
    ! [B_230] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_230),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_230),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_606])).

tff(c_231,plain,(
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

tff(c_241,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_231])).

tff(c_248,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_241])).

tff(c_249,plain,(
    ! [B_152] :
      ( r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_248])).

tff(c_250,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_253,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_250])).

tff(c_256,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_253])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_256])).

tff(c_260,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_259,plain,(
    ! [B_152] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_262,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_265,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_262])).

tff(c_268,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_265])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_268])).

tff(c_271,plain,(
    ! [B_152] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_152,'#skF_6')
      | ~ r1_lattices('#skF_5',B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_273,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_276,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_273])).

tff(c_279,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_276])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_279])).

tff(c_283,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_272,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_46,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k15_lattice3(A_61,B_62),u1_struct_0(A_61))
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_88,plain,(
    ! [A_119,B_120] :
      ( r4_lattice3(A_119,k15_lattice3(A_119,B_120),B_120)
      | ~ m1_subset_1(k15_lattice3(A_119,B_120),u1_struct_0(A_119))
      | ~ v4_lattice3(A_119)
      | ~ v10_lattices(A_119)
      | ~ l3_lattices(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_91,plain,(
    ! [A_61,B_62] :
      ( r4_lattice3(A_61,k15_lattice3(A_61,B_62),B_62)
      | ~ v4_lattice3(A_61)
      | ~ v10_lattices(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_46,c_88])).

tff(c_97,plain,(
    ! [A_125,D_126,B_127,C_128] :
      ( r1_lattices(A_125,D_126,B_127)
      | ~ r2_hidden(D_126,C_128)
      | ~ m1_subset_1(D_126,u1_struct_0(A_125))
      | ~ r4_lattice3(A_125,B_127,C_128)
      | ~ m1_subset_1(B_127,u1_struct_0(A_125))
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_108,plain,(
    ! [A_131,B_132] :
      ( r1_lattices(A_131,'#skF_6',B_132)
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_131))
      | ~ r4_lattice3(A_131,B_132,'#skF_7')
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_62,c_97])).

tff(c_110,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_5','#skF_6',B_132)
      | ~ r4_lattice3('#skF_5',B_132,'#skF_7')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_113,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_5','#skF_6',B_132)
      | ~ r4_lattice3('#skF_5',B_132,'#skF_7')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_110])).

tff(c_115,plain,(
    ! [B_133] :
      ( r1_lattices('#skF_5','#skF_6',B_133)
      | ~ r4_lattice3('#skF_5',B_133,'#skF_7')
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_113])).

tff(c_131,plain,(
    ! [B_62] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_62))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_62),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_149,plain,(
    ! [B_62] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_62))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_62),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_131])).

tff(c_153,plain,(
    ! [B_134] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_134))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_134),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_149])).

tff(c_157,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_91,c_153])).

tff(c_160,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_157])).

tff(c_161,plain,(
    r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_160])).

tff(c_351,plain,(
    ! [A_166,B_167,B_168] :
      ( r3_lattices(A_166,B_167,k15_lattice3(A_166,B_168))
      | ~ r1_lattices(A_166,B_167,k15_lattice3(A_166,B_168))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ v9_lattices(A_166)
      | ~ v8_lattices(A_166)
      | ~ v6_lattices(A_166)
      | ~ l3_lattices(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_46,c_231])).

tff(c_60,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_76,plain,(
    ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_356,plain,
    ( ~ r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_351,c_76])).

tff(c_360,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_260,c_283,c_272,c_64,c_161,c_356])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_360])).

tff(c_363,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_626,plain,(
    ~ r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_621,c_363])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.20/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.50  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.20/1.50  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.20/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.50  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.20/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.50  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.20/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.50  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.20/1.50  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.20/1.50  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.50  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.20/1.50  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.20/1.50  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.50  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.50  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.20/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.50  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.20/1.50  
% 3.20/1.52  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.20/1.52  tff(f_144, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 3.20/1.52  tff(f_168, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 3.20/1.52  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 3.20/1.52  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.20/1.52  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.20/1.52  tff(f_137, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 3.20/1.52  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 3.20/1.52  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 3.20/1.52  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_66, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_70, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_68, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_48, plain, (![A_63, B_64]: (m1_subset_1(k16_lattice3(A_63, B_64), u1_struct_0(A_63)) | ~l3_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.20/1.52  tff(c_376, plain, (![A_194, C_195]: (r3_lattice3(A_194, k16_lattice3(A_194, C_195), C_195) | ~m1_subset_1(k16_lattice3(A_194, C_195), u1_struct_0(A_194)) | ~l3_lattices(A_194) | ~v4_lattice3(A_194) | ~v10_lattices(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.20/1.52  tff(c_379, plain, (![A_63, B_64]: (r3_lattice3(A_63, k16_lattice3(A_63, B_64), B_64) | ~v4_lattice3(A_63) | ~v10_lattices(A_63) | ~l3_lattices(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_48, c_376])).
% 3.20/1.52  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_440, plain, (![A_209, B_210, D_211, C_212]: (r1_lattices(A_209, B_210, D_211) | ~r2_hidden(D_211, C_212) | ~m1_subset_1(D_211, u1_struct_0(A_209)) | ~r3_lattice3(A_209, B_210, C_212) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l3_lattices(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.52  tff(c_461, plain, (![A_215, B_216]: (r1_lattices(A_215, B_216, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_215)) | ~r3_lattice3(A_215, B_216, '#skF_7') | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l3_lattices(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_62, c_440])).
% 3.20/1.52  tff(c_463, plain, (![B_216]: (r1_lattices('#skF_5', B_216, '#skF_6') | ~r3_lattice3('#skF_5', B_216, '#skF_7') | ~m1_subset_1(B_216, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_461])).
% 3.20/1.52  tff(c_466, plain, (![B_216]: (r1_lattices('#skF_5', B_216, '#skF_6') | ~r3_lattice3('#skF_5', B_216, '#skF_7') | ~m1_subset_1(B_216, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_463])).
% 3.20/1.52  tff(c_468, plain, (![B_217]: (r1_lattices('#skF_5', B_217, '#skF_6') | ~r3_lattice3('#skF_5', B_217, '#skF_7') | ~m1_subset_1(B_217, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_466])).
% 3.20/1.52  tff(c_480, plain, (![B_64]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_468])).
% 3.20/1.52  tff(c_498, plain, (![B_64]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_480])).
% 3.20/1.52  tff(c_525, plain, (![B_221]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_221), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_221), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_498])).
% 3.20/1.52  tff(c_529, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_379, c_525])).
% 3.20/1.52  tff(c_532, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_529])).
% 3.20/1.52  tff(c_533, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_532])).
% 3.20/1.52  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.52  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.52  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.52  tff(c_506, plain, (![A_218, B_219, C_220]: (r3_lattices(A_218, B_219, C_220) | ~r1_lattices(A_218, B_219, C_220) | ~m1_subset_1(C_220, u1_struct_0(A_218)) | ~m1_subset_1(B_219, u1_struct_0(A_218)) | ~l3_lattices(A_218) | ~v9_lattices(A_218) | ~v8_lattices(A_218) | ~v6_lattices(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.52  tff(c_516, plain, (![B_219]: (r3_lattices('#skF_5', B_219, '#skF_6') | ~r1_lattices('#skF_5', B_219, '#skF_6') | ~m1_subset_1(B_219, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_506])).
% 3.20/1.52  tff(c_523, plain, (![B_219]: (r3_lattices('#skF_5', B_219, '#skF_6') | ~r1_lattices('#skF_5', B_219, '#skF_6') | ~m1_subset_1(B_219, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_516])).
% 3.20/1.52  tff(c_524, plain, (![B_219]: (r3_lattices('#skF_5', B_219, '#skF_6') | ~r1_lattices('#skF_5', B_219, '#skF_6') | ~m1_subset_1(B_219, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_523])).
% 3.20/1.52  tff(c_535, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_524])).
% 3.20/1.52  tff(c_538, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_535])).
% 3.20/1.52  tff(c_541, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_538])).
% 3.20/1.52  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_541])).
% 3.20/1.52  tff(c_544, plain, (![B_219]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_219, '#skF_6') | ~r1_lattices('#skF_5', B_219, '#skF_6') | ~m1_subset_1(B_219, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_524])).
% 3.20/1.52  tff(c_546, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_544])).
% 3.20/1.52  tff(c_549, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_546])).
% 3.20/1.52  tff(c_552, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_549])).
% 3.20/1.52  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_552])).
% 3.20/1.52  tff(c_555, plain, (![B_219]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_219, '#skF_6') | ~r1_lattices('#skF_5', B_219, '#skF_6') | ~m1_subset_1(B_219, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_544])).
% 3.20/1.52  tff(c_564, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_555])).
% 3.20/1.52  tff(c_567, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_564])).
% 3.20/1.52  tff(c_570, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_567])).
% 3.20/1.52  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_570])).
% 3.20/1.52  tff(c_576, plain, (![B_228]: (r3_lattices('#skF_5', B_228, '#skF_6') | ~r1_lattices('#skF_5', B_228, '#skF_6') | ~m1_subset_1(B_228, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_555])).
% 3.20/1.52  tff(c_588, plain, (![B_64]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_576])).
% 3.20/1.52  tff(c_606, plain, (![B_64]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_64), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_588])).
% 3.20/1.52  tff(c_621, plain, (![B_230]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_230), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_230), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_606])).
% 3.20/1.52  tff(c_231, plain, (![A_151, B_152, C_153]: (r3_lattices(A_151, B_152, C_153) | ~r1_lattices(A_151, B_152, C_153) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l3_lattices(A_151) | ~v9_lattices(A_151) | ~v8_lattices(A_151) | ~v6_lattices(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.52  tff(c_241, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_231])).
% 3.20/1.52  tff(c_248, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_241])).
% 3.20/1.52  tff(c_249, plain, (![B_152]: (r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_248])).
% 3.20/1.52  tff(c_250, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_249])).
% 3.20/1.52  tff(c_253, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_250])).
% 3.20/1.52  tff(c_256, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_253])).
% 3.20/1.52  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_256])).
% 3.20/1.52  tff(c_260, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_249])).
% 3.20/1.52  tff(c_259, plain, (![B_152]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_249])).
% 3.20/1.52  tff(c_262, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_259])).
% 3.20/1.52  tff(c_265, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_262])).
% 3.20/1.52  tff(c_268, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_265])).
% 3.20/1.52  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_268])).
% 3.20/1.52  tff(c_271, plain, (![B_152]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_152, '#skF_6') | ~r1_lattices('#skF_5', B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_259])).
% 3.20/1.52  tff(c_273, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_271])).
% 3.20/1.52  tff(c_276, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_273])).
% 3.20/1.52  tff(c_279, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_276])).
% 3.20/1.52  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_279])).
% 3.20/1.52  tff(c_283, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_271])).
% 3.20/1.52  tff(c_272, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_259])).
% 3.20/1.52  tff(c_46, plain, (![A_61, B_62]: (m1_subset_1(k15_lattice3(A_61, B_62), u1_struct_0(A_61)) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.20/1.52  tff(c_88, plain, (![A_119, B_120]: (r4_lattice3(A_119, k15_lattice3(A_119, B_120), B_120) | ~m1_subset_1(k15_lattice3(A_119, B_120), u1_struct_0(A_119)) | ~v4_lattice3(A_119) | ~v10_lattices(A_119) | ~l3_lattices(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.52  tff(c_91, plain, (![A_61, B_62]: (r4_lattice3(A_61, k15_lattice3(A_61, B_62), B_62) | ~v4_lattice3(A_61) | ~v10_lattices(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_46, c_88])).
% 3.20/1.52  tff(c_97, plain, (![A_125, D_126, B_127, C_128]: (r1_lattices(A_125, D_126, B_127) | ~r2_hidden(D_126, C_128) | ~m1_subset_1(D_126, u1_struct_0(A_125)) | ~r4_lattice3(A_125, B_127, C_128) | ~m1_subset_1(B_127, u1_struct_0(A_125)) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.20/1.52  tff(c_108, plain, (![A_131, B_132]: (r1_lattices(A_131, '#skF_6', B_132) | ~m1_subset_1('#skF_6', u1_struct_0(A_131)) | ~r4_lattice3(A_131, B_132, '#skF_7') | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_62, c_97])).
% 3.20/1.52  tff(c_110, plain, (![B_132]: (r1_lattices('#skF_5', '#skF_6', B_132) | ~r4_lattice3('#skF_5', B_132, '#skF_7') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_108])).
% 3.20/1.52  tff(c_113, plain, (![B_132]: (r1_lattices('#skF_5', '#skF_6', B_132) | ~r4_lattice3('#skF_5', B_132, '#skF_7') | ~m1_subset_1(B_132, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_110])).
% 3.20/1.52  tff(c_115, plain, (![B_133]: (r1_lattices('#skF_5', '#skF_6', B_133) | ~r4_lattice3('#skF_5', B_133, '#skF_7') | ~m1_subset_1(B_133, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_113])).
% 3.20/1.52  tff(c_131, plain, (![B_62]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_62)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_62), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_115])).
% 3.20/1.52  tff(c_149, plain, (![B_62]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_62)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_62), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_131])).
% 3.20/1.52  tff(c_153, plain, (![B_134]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_134)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_134), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_149])).
% 3.20/1.52  tff(c_157, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_91, c_153])).
% 3.20/1.52  tff(c_160, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_157])).
% 3.20/1.52  tff(c_161, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_160])).
% 3.20/1.52  tff(c_351, plain, (![A_166, B_167, B_168]: (r3_lattices(A_166, B_167, k15_lattice3(A_166, B_168)) | ~r1_lattices(A_166, B_167, k15_lattice3(A_166, B_168)) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~v9_lattices(A_166) | ~v8_lattices(A_166) | ~v6_lattices(A_166) | ~l3_lattices(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_46, c_231])).
% 3.20/1.52  tff(c_60, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.20/1.52  tff(c_76, plain, (~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.20/1.52  tff(c_356, plain, (~r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_351, c_76])).
% 3.20/1.52  tff(c_360, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_260, c_283, c_272, c_64, c_161, c_356])).
% 3.20/1.52  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_360])).
% 3.20/1.52  tff(c_363, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 3.20/1.52  tff(c_626, plain, (~r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_621, c_363])).
% 3.20/1.52  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_626])).
% 3.20/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  Inference rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Ref     : 0
% 3.20/1.52  #Sup     : 80
% 3.20/1.52  #Fact    : 0
% 3.20/1.52  #Define  : 0
% 3.20/1.52  #Split   : 13
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 4
% 3.20/1.52  #Demod        : 96
% 3.20/1.52  #Tautology    : 9
% 3.20/1.52  #SimpNegUnit  : 48
% 3.20/1.52  #BackRed      : 0
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.20/1.52  Preprocessing        : 0.36
% 3.20/1.52  Parsing              : 0.21
% 3.20/1.52  CNF conversion       : 0.03
% 3.20/1.52  Main loop            : 0.37
% 3.20/1.52  Inferencing          : 0.14
% 3.20/1.52  Reduction            : 0.11
% 3.20/1.52  Demodulation         : 0.07
% 3.20/1.52  BG Simplification    : 0.03
% 3.20/1.52  Subsumption          : 0.07
% 3.20/1.52  Abstraction          : 0.02
% 3.20/1.52  MUC search           : 0.00
% 3.20/1.52  Cooper               : 0.00
% 3.20/1.52  Total                : 0.78
% 3.20/1.52  Index Insertion      : 0.00
% 3.20/1.52  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
