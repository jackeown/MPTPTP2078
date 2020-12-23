%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  195 (1013 expanded)
%              Number of leaves         :   44 ( 354 expanded)
%              Depth                    :   28
%              Number of atoms          :  597 (4301 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_213,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
              & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_54,axiom,(
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

tff(f_196,axiom,(
    ! [A] :
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_177,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_109,axiom,(
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

tff(f_73,axiom,(
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

tff(f_141,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_91,axiom,(
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

tff(f_165,axiom,(
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

tff(c_72,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_74,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_44,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k16_lattice3(A_56,B_57),u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_78,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_10,plain,(
    ! [A_6] :
      ( v8_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6] :
      ( v9_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_6] :
      ( v6_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_1113,plain,(
    ! [A_408,C_409,B_410] :
      ( r3_lattices(A_408,k16_lattice3(A_408,C_409),B_410)
      | ~ r2_hidden(B_410,C_409)
      | ~ m1_subset_1(B_410,u1_struct_0(A_408))
      | ~ l3_lattices(A_408)
      | ~ v4_lattice3(A_408)
      | ~ v10_lattices(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden('#skF_1'(A_106,B_107),B_107)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_42,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k15_lattice3(A_54,B_55),u1_struct_0(A_54))
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    ! [A_86,B_88] :
      ( k16_lattice3(A_86,a_2_2_lattice3(A_86,B_88)) = k15_lattice3(A_86,B_88)
      | ~ l3_lattices(A_86)
      | ~ v4_lattice3(A_86)
      | ~ v10_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_237,plain,(
    ! [A_175,C_176,B_177] :
      ( r3_lattices(A_175,k16_lattice3(A_175,C_176),B_177)
      | ~ r2_hidden(B_177,C_176)
      | ~ m1_subset_1(B_177,u1_struct_0(A_175))
      | ~ l3_lattices(A_175)
      | ~ v4_lattice3(A_175)
      | ~ v10_lattices(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_578,plain,(
    ! [A_305,B_306,B_307] :
      ( r3_lattices(A_305,k15_lattice3(A_305,B_306),B_307)
      | ~ r2_hidden(B_307,a_2_2_lattice3(A_305,B_306))
      | ~ m1_subset_1(B_307,u1_struct_0(A_305))
      | ~ l3_lattices(A_305)
      | ~ v4_lattice3(A_305)
      | ~ v10_lattices(A_305)
      | v2_struct_0(A_305)
      | ~ l3_lattices(A_305)
      | ~ v4_lattice3(A_305)
      | ~ v10_lattices(A_305)
      | v2_struct_0(A_305) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_237])).

tff(c_70,plain,
    ( ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7'))
    | ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_85,plain,(
    ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_583,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_578,c_85])).

tff(c_587,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_583])).

tff(c_588,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_587])).

tff(c_589,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_592,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_589])).

tff(c_595,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_592])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_595])).

tff(c_599,plain,(
    m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_155,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_3'(A_131,B_132,C_133),C_133)
      | r4_lattice3(A_131,B_132,C_133)
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_263,plain,(
    ! [A_185,B_186,C_187,B_188] :
      ( r2_hidden('#skF_3'(A_185,B_186,C_187),B_188)
      | ~ r1_tarski(C_187,B_188)
      | r4_lattice3(A_185,B_186,C_187)
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l3_lattices(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_424,plain,(
    ! [B_222,C_224,A_221,B_225,B_223] :
      ( r2_hidden('#skF_3'(A_221,B_223,C_224),B_225)
      | ~ r1_tarski(B_222,B_225)
      | ~ r1_tarski(C_224,B_222)
      | r4_lattice3(A_221,B_223,C_224)
      | ~ m1_subset_1(B_223,u1_struct_0(A_221))
      | ~ l3_lattices(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_431,plain,(
    ! [A_226,B_227,C_228] :
      ( r2_hidden('#skF_3'(A_226,B_227,C_228),'#skF_8')
      | ~ r1_tarski(C_228,'#skF_7')
      | r4_lattice3(A_226,B_227,C_228)
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l3_lattices(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_72,c_424])).

tff(c_440,plain,(
    ! [A_226,B_227,C_228,B_2] :
      ( r2_hidden('#skF_3'(A_226,B_227,C_228),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | ~ r1_tarski(C_228,'#skF_7')
      | r4_lattice3(A_226,B_227,C_228)
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l3_lattices(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_431,c_2])).

tff(c_40,plain,(
    ! [A_32,B_44,C_50] :
      ( m1_subset_1('#skF_3'(A_32,B_44,C_50),u1_struct_0(A_32))
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_218,plain,(
    ! [A_172,B_173,C_174] :
      ( r3_lattices(A_172,B_173,k15_lattice3(A_172,C_174))
      | ~ r2_hidden(B_173,C_174)
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l3_lattices(A_172)
      | ~ v4_lattice3(A_172)
      | ~ v10_lattices(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_221,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_218,c_85])).

tff(c_224,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_221])).

tff(c_225,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_224])).

tff(c_226,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_229,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_226])).

tff(c_232,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_229])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_232])).

tff(c_236,plain,(
    m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_355,plain,(
    ! [A_214,B_215,C_216] :
      ( r3_lattices(A_214,B_215,C_216)
      | ~ r1_lattices(A_214,B_215,C_216)
      | ~ m1_subset_1(C_216,u1_struct_0(A_214))
      | ~ m1_subset_1(B_215,u1_struct_0(A_214))
      | ~ l3_lattices(A_214)
      | ~ v9_lattices(A_214)
      | ~ v8_lattices(A_214)
      | ~ v6_lattices(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_357,plain,(
    ! [B_215] :
      ( r3_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_236,c_355])).

tff(c_370,plain,(
    ! [B_215] :
      ( r3_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_357])).

tff(c_371,plain,(
    ! [B_215] :
      ( r3_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_370])).

tff(c_377,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_380,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_377])).

tff(c_383,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_380])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_383])).

tff(c_387,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_386,plain,(
    ! [B_215] :
      ( ~ v8_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | r3_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_388,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_391,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_388])).

tff(c_394,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_391])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_394])).

tff(c_397,plain,(
    ! [B_215] :
      ( ~ v8_lattices('#skF_6')
      | r3_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_215,k15_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_399,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_402,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_399])).

tff(c_405,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_402])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_405])).

tff(c_409,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_398,plain,(
    v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_68,plain,(
    ! [A_89,B_93,C_95] :
      ( r3_lattices(A_89,B_93,k15_lattice3(A_89,C_95))
      | ~ r2_hidden(B_93,C_95)
      | ~ m1_subset_1(B_93,u1_struct_0(A_89))
      | ~ l3_lattices(A_89)
      | ~ v4_lattice3(A_89)
      | ~ v10_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_410,plain,(
    ! [A_217,B_218,C_219] :
      ( r1_lattices(A_217,B_218,C_219)
      | ~ r3_lattices(A_217,B_218,C_219)
      | ~ m1_subset_1(C_219,u1_struct_0(A_217))
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ l3_lattices(A_217)
      | ~ v9_lattices(A_217)
      | ~ v8_lattices(A_217)
      | ~ v6_lattices(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_753,plain,(
    ! [A_320,B_321,C_322] :
      ( r1_lattices(A_320,B_321,k15_lattice3(A_320,C_322))
      | ~ m1_subset_1(k15_lattice3(A_320,C_322),u1_struct_0(A_320))
      | ~ v9_lattices(A_320)
      | ~ v8_lattices(A_320)
      | ~ v6_lattices(A_320)
      | ~ r2_hidden(B_321,C_322)
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | ~ l3_lattices(A_320)
      | ~ v4_lattice3(A_320)
      | ~ v10_lattices(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_68,c_410])).

tff(c_755,plain,(
    ! [B_321] :
      ( r1_lattices('#skF_6',B_321,k15_lattice3('#skF_6','#skF_8'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | ~ r2_hidden(B_321,'#skF_8')
      | ~ m1_subset_1(B_321,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_599,c_753])).

tff(c_762,plain,(
    ! [B_321] :
      ( r1_lattices('#skF_6',B_321,k15_lattice3('#skF_6','#skF_8'))
      | ~ r2_hidden(B_321,'#skF_8')
      | ~ m1_subset_1(B_321,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_387,c_409,c_398,c_755])).

tff(c_782,plain,(
    ! [B_324] :
      ( r1_lattices('#skF_6',B_324,k15_lattice3('#skF_6','#skF_8'))
      | ~ r2_hidden(B_324,'#skF_8')
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_762])).

tff(c_36,plain,(
    ! [A_32,B_44,C_50] :
      ( ~ r1_lattices(A_32,'#skF_3'(A_32,B_44,C_50),B_44)
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_789,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_782,c_36])).

tff(c_795,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50)
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_599,c_789])).

tff(c_908,plain,(
    ! [C_332] :
      ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_332)
      | ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_332),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_332),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_795])).

tff(c_912,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),'#skF_8')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_908])).

tff(c_915,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50),'#skF_8')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_50)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_599,c_912])).

tff(c_917,plain,(
    ! [C_333] :
      ( ~ r2_hidden('#skF_3'('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_333),'#skF_8')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_333) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_915])).

tff(c_921,plain,(
    ! [C_228] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | ~ r1_tarski(C_228,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_228)
      | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_440,c_917])).

tff(c_936,plain,(
    ! [C_228] :
      ( ~ r1_tarski(C_228,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_228)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_599,c_94,c_921])).

tff(c_956,plain,(
    ! [C_334] :
      ( ~ r1_tarski(C_334,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_936])).

tff(c_46,plain,(
    ! [D_63,B_59,C_60] :
      ( r2_hidden(D_63,a_2_2_lattice3(B_59,C_60))
      | ~ r4_lattice3(B_59,D_63,C_60)
      | ~ m1_subset_1(D_63,u1_struct_0(B_59))
      | ~ l3_lattices(B_59)
      | ~ v4_lattice3(B_59)
      | ~ v10_lattices(B_59)
      | v2_struct_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_598,plain,(
    ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_608,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_598])).

tff(c_611,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_599,c_608])).

tff(c_612,plain,(
    ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_611])).

tff(c_959,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_956,c_612])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_959])).

tff(c_966,plain,(
    ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1116,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1113,c_966])).

tff(c_1122,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1116])).

tff(c_1123,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_6','#skF_7'),'#skF_8')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1122])).

tff(c_1124,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_1127,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1124])).

tff(c_1130,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1127])).

tff(c_1132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1130])).

tff(c_1134,plain,(
    m1_subset_1(k16_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1236,plain,(
    ! [A_445,B_446,C_447] :
      ( r3_lattices(A_445,B_446,C_447)
      | ~ r1_lattices(A_445,B_446,C_447)
      | ~ m1_subset_1(C_447,u1_struct_0(A_445))
      | ~ m1_subset_1(B_446,u1_struct_0(A_445))
      | ~ l3_lattices(A_445)
      | ~ v9_lattices(A_445)
      | ~ v8_lattices(A_445)
      | ~ v6_lattices(A_445)
      | v2_struct_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1238,plain,(
    ! [B_446] :
      ( r3_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1134,c_1236])).

tff(c_1251,plain,(
    ! [B_446] :
      ( r3_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1238])).

tff(c_1252,plain,(
    ! [B_446] :
      ( r3_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1251])).

tff(c_1258,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1261,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_1258])).

tff(c_1264,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_1261])).

tff(c_1266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1264])).

tff(c_1267,plain,(
    ! [B_446] :
      ( ~ v8_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | r3_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1269,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1267])).

tff(c_1272,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_1269])).

tff(c_1275,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_1272])).

tff(c_1277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1275])).

tff(c_1278,plain,(
    ! [B_446] :
      ( ~ v8_lattices('#skF_6')
      | r3_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_446,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_1280,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1278])).

tff(c_1283,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1280])).

tff(c_1286,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78,c_1283])).

tff(c_1288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1286])).

tff(c_1304,plain,(
    ! [B_451] :
      ( r3_lattices('#skF_6',B_451,k16_lattice3('#skF_6','#skF_7'))
      | ~ r1_lattices('#skF_6',B_451,k16_lattice3('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1278])).

tff(c_1314,plain,
    ( ~ r1_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1304,c_966])).

tff(c_1315,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1318,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1315])).

tff(c_1321,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1318])).

tff(c_1323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1321])).

tff(c_1325,plain,(
    m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_1074,plain,(
    ! [A_376,B_377,C_378] :
      ( r2_hidden('#skF_2'(A_376,B_377,C_378),C_378)
      | r3_lattice3(A_376,B_377,C_378)
      | ~ m1_subset_1(B_377,u1_struct_0(A_376))
      | ~ l3_lattices(A_376)
      | v2_struct_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1082,plain,(
    ! [A_376,B_377,C_378,B_2] :
      ( r2_hidden('#skF_2'(A_376,B_377,C_378),B_2)
      | ~ r1_tarski(C_378,B_2)
      | r3_lattice3(A_376,B_377,C_378)
      | ~ m1_subset_1(B_377,u1_struct_0(A_376))
      | ~ l3_lattices(A_376)
      | v2_struct_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_1074,c_2])).

tff(c_32,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(A_10))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1268,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1290,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1278])).

tff(c_1279,plain,(
    v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_66,plain,(
    ! [A_89,C_95,B_93] :
      ( r3_lattices(A_89,k16_lattice3(A_89,C_95),B_93)
      | ~ r2_hidden(B_93,C_95)
      | ~ m1_subset_1(B_93,u1_struct_0(A_89))
      | ~ l3_lattices(A_89)
      | ~ v4_lattice3(A_89)
      | ~ v10_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1291,plain,(
    ! [A_448,B_449,C_450] :
      ( r1_lattices(A_448,B_449,C_450)
      | ~ r3_lattices(A_448,B_449,C_450)
      | ~ m1_subset_1(C_450,u1_struct_0(A_448))
      | ~ m1_subset_1(B_449,u1_struct_0(A_448))
      | ~ l3_lattices(A_448)
      | ~ v9_lattices(A_448)
      | ~ v8_lattices(A_448)
      | ~ v6_lattices(A_448)
      | v2_struct_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1933,plain,(
    ! [A_577,C_578,B_579] :
      ( r1_lattices(A_577,k16_lattice3(A_577,C_578),B_579)
      | ~ m1_subset_1(k16_lattice3(A_577,C_578),u1_struct_0(A_577))
      | ~ v9_lattices(A_577)
      | ~ v8_lattices(A_577)
      | ~ v6_lattices(A_577)
      | ~ r2_hidden(B_579,C_578)
      | ~ m1_subset_1(B_579,u1_struct_0(A_577))
      | ~ l3_lattices(A_577)
      | ~ v4_lattice3(A_577)
      | ~ v10_lattices(A_577)
      | v2_struct_0(A_577) ) ),
    inference(resolution,[status(thm)],[c_66,c_1291])).

tff(c_1935,plain,(
    ! [B_579] :
      ( r1_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),B_579)
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | ~ r2_hidden(B_579,'#skF_8')
      | ~ m1_subset_1(B_579,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1325,c_1933])).

tff(c_1944,plain,(
    ! [B_579] :
      ( r1_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),B_579)
      | ~ r2_hidden(B_579,'#skF_8')
      | ~ m1_subset_1(B_579,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1268,c_1290,c_1279,c_1935])).

tff(c_1960,plain,(
    ! [B_581] :
      ( r1_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),B_581)
      | ~ r2_hidden(B_581,'#skF_8')
      | ~ m1_subset_1(B_581,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1944])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( ~ r1_lattices(A_10,B_22,'#skF_2'(A_10,B_22,C_28))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1967,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),'#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1960,c_28])).

tff(c_1973,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28)
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),'#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1325,c_1967])).

tff(c_2010,plain,(
    ! [C_585] :
      ( r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_585)
      | ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_585),'#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_585),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1973])).

tff(c_2014,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_2010])).

tff(c_2017,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28),'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_28)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1325,c_2014])).

tff(c_2019,plain,(
    ! [C_586] :
      ( ~ r2_hidden('#skF_2'('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_586),'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_586) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2017])).

tff(c_2031,plain,(
    ! [C_378] :
      ( ~ r1_tarski(C_378,'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_378)
      | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1082,c_2019])).

tff(c_2046,plain,(
    ! [C_378] :
      ( ~ r1_tarski(C_378,'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_378)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1325,c_2031])).

tff(c_2068,plain,(
    ! [C_590] :
      ( ~ r1_tarski(C_590,'#skF_8')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_590) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2046])).

tff(c_1548,plain,(
    ! [A_521,D_522,C_523] :
      ( r3_lattices(A_521,D_522,k16_lattice3(A_521,C_523))
      | ~ r3_lattice3(A_521,D_522,C_523)
      | ~ m1_subset_1(D_522,u1_struct_0(A_521))
      | ~ m1_subset_1(k16_lattice3(A_521,C_523),u1_struct_0(A_521))
      | ~ l3_lattices(A_521)
      | ~ v4_lattice3(A_521)
      | ~ v10_lattices(A_521)
      | v2_struct_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1552,plain,(
    ! [D_522] :
      ( r3_lattices('#skF_6',D_522,k16_lattice3('#skF_6','#skF_7'))
      | ~ r3_lattice3('#skF_6',D_522,'#skF_7')
      | ~ m1_subset_1(D_522,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1134,c_1548])).

tff(c_1563,plain,(
    ! [D_522] :
      ( r3_lattices('#skF_6',D_522,k16_lattice3('#skF_6','#skF_7'))
      | ~ r3_lattice3('#skF_6',D_522,'#skF_7')
      | ~ m1_subset_1(D_522,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1552])).

tff(c_1566,plain,(
    ! [D_524] :
      ( r3_lattices('#skF_6',D_524,k16_lattice3('#skF_6','#skF_7'))
      | ~ r3_lattice3('#skF_6',D_524,'#skF_7')
      | ~ m1_subset_1(D_524,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1563])).

tff(c_1575,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1566,c_966])).

tff(c_1586,plain,(
    ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1575])).

tff(c_2071,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_2068,c_1586])).

tff(c_2075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n003.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:17:57 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.01  
% 5.34/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.01  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 5.34/2.01  
% 5.34/2.01  %Foreground sorts:
% 5.34/2.01  
% 5.34/2.01  
% 5.34/2.01  %Background operators:
% 5.34/2.01  
% 5.34/2.01  
% 5.34/2.01  %Foreground operators:
% 5.34/2.01  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.34/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.34/2.01  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.34/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.34/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.34/2.01  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 5.34/2.01  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 5.34/2.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.34/2.01  tff('#skF_7', type, '#skF_7': $i).
% 5.34/2.01  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.34/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.34/2.01  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.34/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.34/2.01  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.34/2.01  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.34/2.01  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.34/2.01  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 5.34/2.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.34/2.01  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 5.34/2.01  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.34/2.01  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.34/2.01  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 5.34/2.01  tff('#skF_8', type, '#skF_8': $i).
% 5.34/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.34/2.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.34/2.01  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.34/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.34/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.34/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.34/2.01  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 5.34/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.34/2.01  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.34/2.01  
% 5.34/2.04  tff(f_213, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 5.34/2.04  tff(f_123, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 5.34/2.04  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 5.34/2.04  tff(f_196, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 5.34/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.34/2.04  tff(f_116, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 5.34/2.04  tff(f_177, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 5.34/2.04  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 5.34/2.04  tff(f_73, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.34/2.04  tff(f_141, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 5.34/2.04  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 5.34/2.04  tff(f_165, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 5.34/2.04  tff(c_72, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_80, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_74, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_44, plain, (![A_56, B_57]: (m1_subset_1(k16_lattice3(A_56, B_57), u1_struct_0(A_56)) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.34/2.04  tff(c_78, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_10, plain, (![A_6]: (v8_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.34/2.04  tff(c_8, plain, (![A_6]: (v9_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.34/2.04  tff(c_14, plain, (![A_6]: (v6_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.34/2.04  tff(c_76, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_1113, plain, (![A_408, C_409, B_410]: (r3_lattices(A_408, k16_lattice3(A_408, C_409), B_410) | ~r2_hidden(B_410, C_409) | ~m1_subset_1(B_410, u1_struct_0(A_408)) | ~l3_lattices(A_408) | ~v4_lattice3(A_408) | ~v10_lattices(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.34/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.04  tff(c_89, plain, (![A_106, B_107]: (~r2_hidden('#skF_1'(A_106, B_107), B_107) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.04  tff(c_94, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_89])).
% 5.34/2.04  tff(c_42, plain, (![A_54, B_55]: (m1_subset_1(k15_lattice3(A_54, B_55), u1_struct_0(A_54)) | ~l3_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.34/2.04  tff(c_64, plain, (![A_86, B_88]: (k16_lattice3(A_86, a_2_2_lattice3(A_86, B_88))=k15_lattice3(A_86, B_88) | ~l3_lattices(A_86) | ~v4_lattice3(A_86) | ~v10_lattices(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.34/2.04  tff(c_237, plain, (![A_175, C_176, B_177]: (r3_lattices(A_175, k16_lattice3(A_175, C_176), B_177) | ~r2_hidden(B_177, C_176) | ~m1_subset_1(B_177, u1_struct_0(A_175)) | ~l3_lattices(A_175) | ~v4_lattice3(A_175) | ~v10_lattices(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.34/2.04  tff(c_578, plain, (![A_305, B_306, B_307]: (r3_lattices(A_305, k15_lattice3(A_305, B_306), B_307) | ~r2_hidden(B_307, a_2_2_lattice3(A_305, B_306)) | ~m1_subset_1(B_307, u1_struct_0(A_305)) | ~l3_lattices(A_305) | ~v4_lattice3(A_305) | ~v10_lattices(A_305) | v2_struct_0(A_305) | ~l3_lattices(A_305) | ~v4_lattice3(A_305) | ~v10_lattices(A_305) | v2_struct_0(A_305))), inference(superposition, [status(thm), theory('equality')], [c_64, c_237])).
% 5.34/2.04  tff(c_70, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 5.34/2.04  tff(c_85, plain, (~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_70])).
% 5.34/2.04  tff(c_583, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_578, c_85])).
% 5.34/2.04  tff(c_587, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_583])).
% 5.34/2.04  tff(c_588, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_587])).
% 5.34/2.04  tff(c_589, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_588])).
% 5.34/2.04  tff(c_592, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_589])).
% 5.34/2.04  tff(c_595, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_592])).
% 5.34/2.04  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_595])).
% 5.34/2.04  tff(c_599, plain, (m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_588])).
% 5.34/2.04  tff(c_155, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_3'(A_131, B_132, C_133), C_133) | r4_lattice3(A_131, B_132, C_133) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.34/2.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.04  tff(c_263, plain, (![A_185, B_186, C_187, B_188]: (r2_hidden('#skF_3'(A_185, B_186, C_187), B_188) | ~r1_tarski(C_187, B_188) | r4_lattice3(A_185, B_186, C_187) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l3_lattices(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_155, c_2])).
% 5.34/2.04  tff(c_424, plain, (![B_222, C_224, A_221, B_225, B_223]: (r2_hidden('#skF_3'(A_221, B_223, C_224), B_225) | ~r1_tarski(B_222, B_225) | ~r1_tarski(C_224, B_222) | r4_lattice3(A_221, B_223, C_224) | ~m1_subset_1(B_223, u1_struct_0(A_221)) | ~l3_lattices(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_263, c_2])).
% 5.34/2.04  tff(c_431, plain, (![A_226, B_227, C_228]: (r2_hidden('#skF_3'(A_226, B_227, C_228), '#skF_8') | ~r1_tarski(C_228, '#skF_7') | r4_lattice3(A_226, B_227, C_228) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l3_lattices(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_72, c_424])).
% 5.34/2.04  tff(c_440, plain, (![A_226, B_227, C_228, B_2]: (r2_hidden('#skF_3'(A_226, B_227, C_228), B_2) | ~r1_tarski('#skF_8', B_2) | ~r1_tarski(C_228, '#skF_7') | r4_lattice3(A_226, B_227, C_228) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l3_lattices(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_431, c_2])).
% 5.34/2.04  tff(c_40, plain, (![A_32, B_44, C_50]: (m1_subset_1('#skF_3'(A_32, B_44, C_50), u1_struct_0(A_32)) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.34/2.04  tff(c_218, plain, (![A_172, B_173, C_174]: (r3_lattices(A_172, B_173, k15_lattice3(A_172, C_174)) | ~r2_hidden(B_173, C_174) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l3_lattices(A_172) | ~v4_lattice3(A_172) | ~v10_lattices(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.34/2.04  tff(c_221, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_218, c_85])).
% 5.34/2.04  tff(c_224, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_221])).
% 5.34/2.04  tff(c_225, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_224])).
% 5.34/2.04  tff(c_226, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_225])).
% 5.34/2.04  tff(c_229, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_226])).
% 5.34/2.04  tff(c_232, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_229])).
% 5.34/2.04  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_232])).
% 5.34/2.04  tff(c_236, plain, (m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_225])).
% 5.34/2.04  tff(c_355, plain, (![A_214, B_215, C_216]: (r3_lattices(A_214, B_215, C_216) | ~r1_lattices(A_214, B_215, C_216) | ~m1_subset_1(C_216, u1_struct_0(A_214)) | ~m1_subset_1(B_215, u1_struct_0(A_214)) | ~l3_lattices(A_214) | ~v9_lattices(A_214) | ~v8_lattices(A_214) | ~v6_lattices(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.34/2.04  tff(c_357, plain, (![B_215]: (r3_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_215, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_236, c_355])).
% 5.34/2.04  tff(c_370, plain, (![B_215]: (r3_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_215, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_357])).
% 5.34/2.04  tff(c_371, plain, (![B_215]: (r3_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_215, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_370])).
% 5.34/2.04  tff(c_377, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_371])).
% 5.34/2.04  tff(c_380, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_14, c_377])).
% 5.34/2.04  tff(c_383, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_380])).
% 5.34/2.04  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_383])).
% 5.34/2.04  tff(c_387, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_371])).
% 5.34/2.04  tff(c_386, plain, (![B_215]: (~v8_lattices('#skF_6') | ~v9_lattices('#skF_6') | r3_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_215, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_371])).
% 5.34/2.04  tff(c_388, plain, (~v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_386])).
% 5.34/2.04  tff(c_391, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_388])).
% 5.34/2.04  tff(c_394, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_391])).
% 5.34/2.04  tff(c_396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_394])).
% 5.34/2.04  tff(c_397, plain, (![B_215]: (~v8_lattices('#skF_6') | r3_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_215, k15_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_215, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_386])).
% 5.34/2.04  tff(c_399, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_397])).
% 5.34/2.04  tff(c_402, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_10, c_399])).
% 5.34/2.04  tff(c_405, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_402])).
% 5.34/2.04  tff(c_407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_405])).
% 5.34/2.04  tff(c_409, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_397])).
% 5.34/2.04  tff(c_398, plain, (v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_386])).
% 5.34/2.04  tff(c_68, plain, (![A_89, B_93, C_95]: (r3_lattices(A_89, B_93, k15_lattice3(A_89, C_95)) | ~r2_hidden(B_93, C_95) | ~m1_subset_1(B_93, u1_struct_0(A_89)) | ~l3_lattices(A_89) | ~v4_lattice3(A_89) | ~v10_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.34/2.04  tff(c_410, plain, (![A_217, B_218, C_219]: (r1_lattices(A_217, B_218, C_219) | ~r3_lattices(A_217, B_218, C_219) | ~m1_subset_1(C_219, u1_struct_0(A_217)) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~l3_lattices(A_217) | ~v9_lattices(A_217) | ~v8_lattices(A_217) | ~v6_lattices(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.34/2.04  tff(c_753, plain, (![A_320, B_321, C_322]: (r1_lattices(A_320, B_321, k15_lattice3(A_320, C_322)) | ~m1_subset_1(k15_lattice3(A_320, C_322), u1_struct_0(A_320)) | ~v9_lattices(A_320) | ~v8_lattices(A_320) | ~v6_lattices(A_320) | ~r2_hidden(B_321, C_322) | ~m1_subset_1(B_321, u1_struct_0(A_320)) | ~l3_lattices(A_320) | ~v4_lattice3(A_320) | ~v10_lattices(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_68, c_410])).
% 5.34/2.04  tff(c_755, plain, (![B_321]: (r1_lattices('#skF_6', B_321, k15_lattice3('#skF_6', '#skF_8')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | ~r2_hidden(B_321, '#skF_8') | ~m1_subset_1(B_321, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_599, c_753])).
% 5.34/2.04  tff(c_762, plain, (![B_321]: (r1_lattices('#skF_6', B_321, k15_lattice3('#skF_6', '#skF_8')) | ~r2_hidden(B_321, '#skF_8') | ~m1_subset_1(B_321, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_387, c_409, c_398, c_755])).
% 5.34/2.04  tff(c_782, plain, (![B_324]: (r1_lattices('#skF_6', B_324, k15_lattice3('#skF_6', '#skF_8')) | ~r2_hidden(B_324, '#skF_8') | ~m1_subset_1(B_324, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_762])).
% 5.34/2.04  tff(c_36, plain, (![A_32, B_44, C_50]: (~r1_lattices(A_32, '#skF_3'(A_32, B_44, C_50), B_44) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.34/2.04  tff(c_789, plain, (![C_50]: (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_782, c_36])).
% 5.34/2.04  tff(c_795, plain, (![C_50]: (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50) | v2_struct_0('#skF_6') | ~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_599, c_789])).
% 5.34/2.04  tff(c_908, plain, (![C_332]: (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_332) | ~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_332), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_332), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_795])).
% 5.34/2.04  tff(c_912, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), '#skF_8') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_908])).
% 5.34/2.04  tff(c_915, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50), '#skF_8') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_50) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_599, c_912])).
% 5.34/2.04  tff(c_917, plain, (![C_333]: (~r2_hidden('#skF_3'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_333), '#skF_8') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_333))), inference(negUnitSimplification, [status(thm)], [c_80, c_915])).
% 5.34/2.04  tff(c_921, plain, (![C_228]: (~r1_tarski('#skF_8', '#skF_8') | ~r1_tarski(C_228, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_228) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_440, c_917])).
% 5.34/2.04  tff(c_936, plain, (![C_228]: (~r1_tarski(C_228, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_228) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_599, c_94, c_921])).
% 5.34/2.04  tff(c_956, plain, (![C_334]: (~r1_tarski(C_334, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_334))), inference(negUnitSimplification, [status(thm)], [c_80, c_936])).
% 5.34/2.04  tff(c_46, plain, (![D_63, B_59, C_60]: (r2_hidden(D_63, a_2_2_lattice3(B_59, C_60)) | ~r4_lattice3(B_59, D_63, C_60) | ~m1_subset_1(D_63, u1_struct_0(B_59)) | ~l3_lattices(B_59) | ~v4_lattice3(B_59) | ~v10_lattices(B_59) | v2_struct_0(B_59))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.34/2.04  tff(c_598, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_588])).
% 5.34/2.04  tff(c_608, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_598])).
% 5.34/2.04  tff(c_611, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_599, c_608])).
% 5.34/2.04  tff(c_612, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_611])).
% 5.34/2.04  tff(c_959, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_956, c_612])).
% 5.34/2.04  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_959])).
% 5.34/2.04  tff(c_966, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_70])).
% 5.34/2.04  tff(c_1116, plain, (~r2_hidden(k16_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1113, c_966])).
% 5.34/2.04  tff(c_1122, plain, (~r2_hidden(k16_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1116])).
% 5.34/2.04  tff(c_1123, plain, (~r2_hidden(k16_lattice3('#skF_6', '#skF_7'), '#skF_8') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1122])).
% 5.34/2.04  tff(c_1124, plain, (~m1_subset_1(k16_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1123])).
% 5.34/2.04  tff(c_1127, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_1124])).
% 5.34/2.04  tff(c_1130, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1127])).
% 5.34/2.04  tff(c_1132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1130])).
% 5.34/2.04  tff(c_1134, plain, (m1_subset_1(k16_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1123])).
% 5.34/2.04  tff(c_1236, plain, (![A_445, B_446, C_447]: (r3_lattices(A_445, B_446, C_447) | ~r1_lattices(A_445, B_446, C_447) | ~m1_subset_1(C_447, u1_struct_0(A_445)) | ~m1_subset_1(B_446, u1_struct_0(A_445)) | ~l3_lattices(A_445) | ~v9_lattices(A_445) | ~v8_lattices(A_445) | ~v6_lattices(A_445) | v2_struct_0(A_445))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.34/2.04  tff(c_1238, plain, (![B_446]: (r3_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_446, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1134, c_1236])).
% 5.34/2.04  tff(c_1251, plain, (![B_446]: (r3_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_446, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1238])).
% 5.34/2.04  tff(c_1252, plain, (![B_446]: (r3_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_446, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1251])).
% 5.34/2.04  tff(c_1258, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_1252])).
% 5.34/2.04  tff(c_1261, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_14, c_1258])).
% 5.34/2.04  tff(c_1264, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_1261])).
% 5.34/2.04  tff(c_1266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1264])).
% 5.34/2.04  tff(c_1267, plain, (![B_446]: (~v8_lattices('#skF_6') | ~v9_lattices('#skF_6') | r3_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_446, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1252])).
% 5.34/2.04  tff(c_1269, plain, (~v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_1267])).
% 5.34/2.04  tff(c_1272, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_1269])).
% 5.34/2.04  tff(c_1275, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_1272])).
% 5.34/2.04  tff(c_1277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1275])).
% 5.34/2.04  tff(c_1278, plain, (![B_446]: (~v8_lattices('#skF_6') | r3_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_446, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_446, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1267])).
% 5.34/2.04  tff(c_1280, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_1278])).
% 5.34/2.04  tff(c_1283, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_10, c_1280])).
% 5.34/2.04  tff(c_1286, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78, c_1283])).
% 5.34/2.04  tff(c_1288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1286])).
% 5.34/2.04  tff(c_1304, plain, (![B_451]: (r3_lattices('#skF_6', B_451, k16_lattice3('#skF_6', '#skF_7')) | ~r1_lattices('#skF_6', B_451, k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(B_451, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1278])).
% 5.34/2.04  tff(c_1314, plain, (~r1_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1304, c_966])).
% 5.34/2.04  tff(c_1315, plain, (~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1314])).
% 5.34/2.04  tff(c_1318, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_1315])).
% 5.34/2.04  tff(c_1321, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1318])).
% 5.34/2.04  tff(c_1323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1321])).
% 5.34/2.04  tff(c_1325, plain, (m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1314])).
% 5.34/2.04  tff(c_1074, plain, (![A_376, B_377, C_378]: (r2_hidden('#skF_2'(A_376, B_377, C_378), C_378) | r3_lattice3(A_376, B_377, C_378) | ~m1_subset_1(B_377, u1_struct_0(A_376)) | ~l3_lattices(A_376) | v2_struct_0(A_376))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.34/2.04  tff(c_1082, plain, (![A_376, B_377, C_378, B_2]: (r2_hidden('#skF_2'(A_376, B_377, C_378), B_2) | ~r1_tarski(C_378, B_2) | r3_lattice3(A_376, B_377, C_378) | ~m1_subset_1(B_377, u1_struct_0(A_376)) | ~l3_lattices(A_376) | v2_struct_0(A_376))), inference(resolution, [status(thm)], [c_1074, c_2])).
% 5.34/2.04  tff(c_32, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_2'(A_10, B_22, C_28), u1_struct_0(A_10)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.34/2.04  tff(c_1268, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_1252])).
% 5.34/2.04  tff(c_1290, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_1278])).
% 5.34/2.04  tff(c_1279, plain, (v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_1267])).
% 5.34/2.04  tff(c_66, plain, (![A_89, C_95, B_93]: (r3_lattices(A_89, k16_lattice3(A_89, C_95), B_93) | ~r2_hidden(B_93, C_95) | ~m1_subset_1(B_93, u1_struct_0(A_89)) | ~l3_lattices(A_89) | ~v4_lattice3(A_89) | ~v10_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.34/2.04  tff(c_1291, plain, (![A_448, B_449, C_450]: (r1_lattices(A_448, B_449, C_450) | ~r3_lattices(A_448, B_449, C_450) | ~m1_subset_1(C_450, u1_struct_0(A_448)) | ~m1_subset_1(B_449, u1_struct_0(A_448)) | ~l3_lattices(A_448) | ~v9_lattices(A_448) | ~v8_lattices(A_448) | ~v6_lattices(A_448) | v2_struct_0(A_448))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.34/2.04  tff(c_1933, plain, (![A_577, C_578, B_579]: (r1_lattices(A_577, k16_lattice3(A_577, C_578), B_579) | ~m1_subset_1(k16_lattice3(A_577, C_578), u1_struct_0(A_577)) | ~v9_lattices(A_577) | ~v8_lattices(A_577) | ~v6_lattices(A_577) | ~r2_hidden(B_579, C_578) | ~m1_subset_1(B_579, u1_struct_0(A_577)) | ~l3_lattices(A_577) | ~v4_lattice3(A_577) | ~v10_lattices(A_577) | v2_struct_0(A_577))), inference(resolution, [status(thm)], [c_66, c_1291])).
% 5.34/2.04  tff(c_1935, plain, (![B_579]: (r1_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), B_579) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | ~r2_hidden(B_579, '#skF_8') | ~m1_subset_1(B_579, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1325, c_1933])).
% 5.34/2.04  tff(c_1944, plain, (![B_579]: (r1_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), B_579) | ~r2_hidden(B_579, '#skF_8') | ~m1_subset_1(B_579, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1268, c_1290, c_1279, c_1935])).
% 5.34/2.04  tff(c_1960, plain, (![B_581]: (r1_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), B_581) | ~r2_hidden(B_581, '#skF_8') | ~m1_subset_1(B_581, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1944])).
% 5.34/2.04  tff(c_28, plain, (![A_10, B_22, C_28]: (~r1_lattices(A_10, B_22, '#skF_2'(A_10, B_22, C_28)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.34/2.04  tff(c_1967, plain, (![C_28]: (r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28) | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), '#skF_8') | ~m1_subset_1('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1960, c_28])).
% 5.34/2.04  tff(c_1973, plain, (![C_28]: (r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28) | v2_struct_0('#skF_6') | ~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), '#skF_8') | ~m1_subset_1('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1325, c_1967])).
% 5.34/2.04  tff(c_2010, plain, (![C_585]: (r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_585) | ~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_585), '#skF_8') | ~m1_subset_1('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_585), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1973])).
% 5.34/2.04  tff(c_2014, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28) | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_2010])).
% 5.34/2.04  tff(c_2017, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28), '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_28) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1325, c_2014])).
% 5.34/2.04  tff(c_2019, plain, (![C_586]: (~r2_hidden('#skF_2'('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_586), '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_586))), inference(negUnitSimplification, [status(thm)], [c_80, c_2017])).
% 5.34/2.04  tff(c_2031, plain, (![C_378]: (~r1_tarski(C_378, '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_378) | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1082, c_2019])).
% 5.34/2.04  tff(c_2046, plain, (![C_378]: (~r1_tarski(C_378, '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_378) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1325, c_2031])).
% 5.34/2.04  tff(c_2068, plain, (![C_590]: (~r1_tarski(C_590, '#skF_8') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_590))), inference(negUnitSimplification, [status(thm)], [c_80, c_2046])).
% 5.34/2.04  tff(c_1548, plain, (![A_521, D_522, C_523]: (r3_lattices(A_521, D_522, k16_lattice3(A_521, C_523)) | ~r3_lattice3(A_521, D_522, C_523) | ~m1_subset_1(D_522, u1_struct_0(A_521)) | ~m1_subset_1(k16_lattice3(A_521, C_523), u1_struct_0(A_521)) | ~l3_lattices(A_521) | ~v4_lattice3(A_521) | ~v10_lattices(A_521) | v2_struct_0(A_521))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.34/2.04  tff(c_1552, plain, (![D_522]: (r3_lattices('#skF_6', D_522, k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattice3('#skF_6', D_522, '#skF_7') | ~m1_subset_1(D_522, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1134, c_1548])).
% 5.34/2.04  tff(c_1563, plain, (![D_522]: (r3_lattices('#skF_6', D_522, k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattice3('#skF_6', D_522, '#skF_7') | ~m1_subset_1(D_522, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1552])).
% 5.34/2.04  tff(c_1566, plain, (![D_524]: (r3_lattices('#skF_6', D_524, k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattice3('#skF_6', D_524, '#skF_7') | ~m1_subset_1(D_524, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1563])).
% 5.34/2.04  tff(c_1575, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1566, c_966])).
% 5.34/2.04  tff(c_1586, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1575])).
% 5.34/2.04  tff(c_2071, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_2068, c_1586])).
% 5.34/2.04  tff(c_2075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_2071])).
% 5.34/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.04  
% 5.34/2.04  Inference rules
% 5.34/2.04  ----------------------
% 5.34/2.04  #Ref     : 0
% 5.34/2.04  #Sup     : 388
% 5.34/2.04  #Fact    : 0
% 5.34/2.04  #Define  : 0
% 5.34/2.04  #Split   : 13
% 5.34/2.04  #Chain   : 0
% 5.34/2.04  #Close   : 0
% 5.34/2.04  
% 5.34/2.04  Ordering : KBO
% 5.34/2.04  
% 5.34/2.04  Simplification rules
% 5.34/2.04  ----------------------
% 5.34/2.04  #Subsume      : 52
% 5.34/2.04  #Demod        : 361
% 5.34/2.04  #Tautology    : 53
% 5.34/2.04  #SimpNegUnit  : 110
% 5.34/2.04  #BackRed      : 0
% 5.34/2.04  
% 5.34/2.04  #Partial instantiations: 0
% 5.34/2.04  #Strategies tried      : 1
% 5.34/2.04  
% 5.34/2.04  Timing (in seconds)
% 5.34/2.04  ----------------------
% 5.34/2.05  Preprocessing        : 0.37
% 5.34/2.05  Parsing              : 0.20
% 5.34/2.05  CNF conversion       : 0.03
% 5.34/2.05  Main loop            : 0.86
% 5.34/2.05  Inferencing          : 0.36
% 5.34/2.05  Reduction            : 0.23
% 5.34/2.05  Demodulation         : 0.15
% 5.34/2.05  BG Simplification    : 0.04
% 5.34/2.05  Subsumption          : 0.16
% 5.34/2.05  Abstraction          : 0.04
% 5.34/2.05  MUC search           : 0.00
% 5.34/2.05  Cooper               : 0.00
% 5.34/2.05  Total                : 1.29
% 5.34/2.05  Index Insertion      : 0.00
% 5.34/2.05  Index Deletion       : 0.00
% 5.34/2.05  Index Matching       : 0.00
% 5.34/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
