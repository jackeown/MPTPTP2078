%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:48 EST 2020

% Result     : Theorem 18.19s
% Output     : CNFRefutation 19.00s
% Verified   : 
% Statistics : Number of formulae       :  566 (79452 expanded)
%              Number of leaves         :   36 (27301 expanded)
%              Depth                    :   65
%              Number of atoms          : 2089 (386395 expanded)
%              Number of equality atoms :  229 (48483 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r3_lattice3(A,B,C) )
               => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_145,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_43,axiom,(
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

tff(f_121,axiom,(
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

tff(f_61,axiom,(
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

tff(f_89,axiom,(
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

tff(f_157,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
             => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    k16_lattice3('#skF_7','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    v4_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_66,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_60,plain,(
    r3_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_50,plain,(
    ! [A_69,B_81,C_87] :
      ( r3_lattice3(A_69,'#skF_6'(A_69,B_81,C_87),C_87)
      | k16_lattice3(A_69,C_87) = B_81
      | ~ r3_lattice3(A_69,B_81,C_87)
      | ~ m1_subset_1(B_81,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    ! [A_69,B_81,C_87] :
      ( m1_subset_1('#skF_6'(A_69,B_81,C_87),u1_struct_0(A_69))
      | k16_lattice3(A_69,C_87) = B_81
      | ~ r3_lattice3(A_69,B_81,C_87)
      | ~ m1_subset_1(B_81,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    ! [D_62,B_58,C_59] :
      ( r2_hidden(D_62,a_2_1_lattice3(B_58,C_59))
      | ~ r3_lattice3(B_58,D_62,C_59)
      | ~ m1_subset_1(D_62,u1_struct_0(B_58))
      | ~ l3_lattices(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_330,plain,(
    ! [A_197,B_198,C_199] :
      ( r3_lattice3(A_197,'#skF_6'(A_197,B_198,C_199),C_199)
      | k16_lattice3(A_197,C_199) = B_198
      | ~ r3_lattice3(A_197,B_198,C_199)
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l3_lattices(A_197)
      | ~ v4_lattice3(A_197)
      | ~ v10_lattices(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_85,plain,(
    ! [D_116,B_117,C_118] :
      ( r2_hidden(D_116,a_2_1_lattice3(B_117,C_118))
      | ~ r3_lattice3(B_117,D_116,C_118)
      | ~ m1_subset_1(D_116,u1_struct_0(B_117))
      | ~ l3_lattices(B_117)
      | v2_struct_0(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_57,B_58,C_59] :
      ( '#skF_4'(A_57,B_58,C_59) = A_57
      | ~ r2_hidden(A_57,a_2_1_lattice3(B_58,C_59))
      | ~ l3_lattices(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    ! [D_116,B_117,C_118] :
      ( '#skF_4'(D_116,B_117,C_118) = D_116
      | ~ r3_lattice3(B_117,D_116,C_118)
      | ~ m1_subset_1(D_116,u1_struct_0(B_117))
      | ~ l3_lattices(B_117)
      | v2_struct_0(B_117) ) ),
    inference(resolution,[status(thm)],[c_85,c_32])).

tff(c_2189,plain,(
    ! [A_422,B_423,C_424] :
      ( '#skF_4'('#skF_6'(A_422,B_423,C_424),A_422,C_424) = '#skF_6'(A_422,B_423,C_424)
      | ~ m1_subset_1('#skF_6'(A_422,B_423,C_424),u1_struct_0(A_422))
      | k16_lattice3(A_422,C_424) = B_423
      | ~ r3_lattice3(A_422,B_423,C_424)
      | ~ m1_subset_1(B_423,u1_struct_0(A_422))
      | ~ l3_lattices(A_422)
      | ~ v4_lattice3(A_422)
      | ~ v10_lattices(A_422)
      | v2_struct_0(A_422) ) ),
    inference(resolution,[status(thm)],[c_330,c_89])).

tff(c_2234,plain,(
    ! [A_428,B_429,C_430] :
      ( '#skF_4'('#skF_6'(A_428,B_429,C_430),A_428,C_430) = '#skF_6'(A_428,B_429,C_430)
      | k16_lattice3(A_428,C_430) = B_429
      | ~ r3_lattice3(A_428,B_429,C_430)
      | ~ m1_subset_1(B_429,u1_struct_0(A_428))
      | ~ l3_lattices(A_428)
      | ~ v4_lattice3(A_428)
      | ~ v10_lattices(A_428)
      | v2_struct_0(A_428) ) ),
    inference(resolution,[status(thm)],[c_52,c_2189])).

tff(c_2248,plain,(
    ! [C_430] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_430),'#skF_7',C_430) = '#skF_6'('#skF_7','#skF_8',C_430)
      | k16_lattice3('#skF_7',C_430) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_430)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_2234])).

tff(c_2257,plain,(
    ! [C_430] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_430),'#skF_7',C_430) = '#skF_6'('#skF_7','#skF_8',C_430)
      | k16_lattice3('#skF_7',C_430) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_430)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2248])).

tff(c_2259,plain,(
    ! [C_431] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_431),'#skF_7',C_431) = '#skF_6'('#skF_7','#skF_8',C_431)
      | k16_lattice3('#skF_7',C_431) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2257])).

tff(c_30,plain,(
    ! [B_58,A_57,C_59] :
      ( r3_lattice3(B_58,'#skF_4'(A_57,B_58,C_59),C_59)
      | ~ r2_hidden(A_57,a_2_1_lattice3(B_58,C_59))
      | ~ l3_lattices(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1('#skF_4'(A_57,B_58,C_59),u1_struct_0(B_58))
      | ~ r2_hidden(A_57,a_2_1_lattice3(B_58,C_59))
      | ~ l3_lattices(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_162,plain,(
    ! [A_162,B_163,D_164,C_165] :
      ( r1_lattices(A_162,B_163,D_164)
      | ~ r2_hidden(D_164,C_165)
      | ~ m1_subset_1(D_164,u1_struct_0(A_162))
      | ~ r3_lattice3(A_162,B_163,C_165)
      | ~ m1_subset_1(B_163,u1_struct_0(A_162))
      | ~ l3_lattices(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [A_166,B_167] :
      ( r1_lattices(A_166,B_167,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_166))
      | ~ r3_lattice3(A_166,B_167,'#skF_9')
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l3_lattices(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_62,c_162])).

tff(c_180,plain,(
    ! [B_167] :
      ( r1_lattices('#skF_7',B_167,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_167,'#skF_9')
      | ~ m1_subset_1(B_167,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_178])).

tff(c_183,plain,(
    ! [B_167] :
      ( r1_lattices('#skF_7',B_167,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_167,'#skF_9')
      | ~ m1_subset_1(B_167,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180])).

tff(c_185,plain,(
    ! [B_168] :
      ( r1_lattices('#skF_7',B_168,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_168,'#skF_9')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_183])).

tff(c_201,plain,(
    ! [A_57,C_59] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_9')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7',C_59))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_219,plain,(
    ! [A_57,C_59] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_9')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7',C_59))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_201])).

tff(c_225,plain,(
    ! [A_171,C_172] :
      ( r1_lattices('#skF_7','#skF_4'(A_171,'#skF_7',C_172),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_171,'#skF_7',C_172),'#skF_9')
      | ~ r2_hidden(A_171,a_2_1_lattice3('#skF_7',C_172)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_219])).

tff(c_232,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_225])).

tff(c_237,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_232])).

tff(c_238,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_237])).

tff(c_2285,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_238])).

tff(c_2306,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2285])).

tff(c_2307,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2306])).

tff(c_2315,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2307])).

tff(c_2318,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_2315])).

tff(c_2321,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2318])).

tff(c_2322,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2321])).

tff(c_2323,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2322])).

tff(c_2330,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_2323])).

tff(c_2333,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_2330])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_2333])).

tff(c_2336,plain,(
    ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2322])).

tff(c_2390,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_2336])).

tff(c_2393,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_2390])).

tff(c_2395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_2393])).

tff(c_2397,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2307])).

tff(c_2291,plain,(
    ! [C_431] :
      ( m1_subset_1('#skF_6'('#skF_7','#skF_8',C_431),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_6'('#skF_7','#skF_8',C_431),a_2_1_lattice3('#skF_7',C_431))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k16_lattice3('#skF_7',C_431) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_34])).

tff(c_2309,plain,(
    ! [C_431] :
      ( m1_subset_1('#skF_6'('#skF_7','#skF_8',C_431),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_6'('#skF_7','#skF_8',C_431),a_2_1_lattice3('#skF_7',C_431))
      | v2_struct_0('#skF_7')
      | k16_lattice3('#skF_7',C_431) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2291])).

tff(c_2310,plain,(
    ! [C_431] :
      ( m1_subset_1('#skF_6'('#skF_7','#skF_8',C_431),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_6'('#skF_7','#skF_8',C_431),a_2_1_lattice3('#skF_7',C_431))
      | k16_lattice3('#skF_7',C_431) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2309])).

tff(c_2409,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2397,c_2310])).

tff(c_2421,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2409])).

tff(c_2422,plain,(
    m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2421])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | r3_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_13,C_19] :
      ( r2_hidden('#skF_1'(A_1,B_13,C_19),C_19)
      | r3_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [A_125,B_126,C_127] :
      ( '#skF_5'(A_125,B_126,C_127) = A_125
      | ~ r2_hidden(A_125,a_2_2_lattice3(B_126,C_127))
      | ~ l3_lattices(B_126)
      | ~ v4_lattice3(B_126)
      | ~ v10_lattices(B_126)
      | v2_struct_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1286,plain,(
    ! [A_320,B_321,B_322,C_323] :
      ( '#skF_5'('#skF_1'(A_320,B_321,a_2_2_lattice3(B_322,C_323)),B_322,C_323) = '#skF_1'(A_320,B_321,a_2_2_lattice3(B_322,C_323))
      | ~ l3_lattices(B_322)
      | ~ v4_lattice3(B_322)
      | ~ v10_lattices(B_322)
      | v2_struct_0(B_322)
      | r3_lattice3(A_320,B_321,a_2_2_lattice3(B_322,C_323))
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | ~ l3_lattices(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_38,plain,(
    ! [B_64,A_63,C_65] :
      ( r4_lattice3(B_64,'#skF_5'(A_63,B_64,C_65),C_65)
      | ~ r2_hidden(A_63,a_2_2_lattice3(B_64,C_65))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_25893,plain,(
    ! [B_1832,A_1833,B_1834,C_1835] :
      ( r4_lattice3(B_1832,'#skF_1'(A_1833,B_1834,a_2_2_lattice3(B_1832,C_1835)),C_1835)
      | ~ r2_hidden('#skF_1'(A_1833,B_1834,a_2_2_lattice3(B_1832,C_1835)),a_2_2_lattice3(B_1832,C_1835))
      | ~ l3_lattices(B_1832)
      | ~ v4_lattice3(B_1832)
      | ~ v10_lattices(B_1832)
      | v2_struct_0(B_1832)
      | ~ l3_lattices(B_1832)
      | ~ v4_lattice3(B_1832)
      | ~ v10_lattices(B_1832)
      | v2_struct_0(B_1832)
      | r3_lattice3(A_1833,B_1834,a_2_2_lattice3(B_1832,C_1835))
      | ~ m1_subset_1(B_1834,u1_struct_0(A_1833))
      | ~ l3_lattices(A_1833)
      | v2_struct_0(A_1833) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_38])).

tff(c_25921,plain,(
    ! [B_1838,A_1839,B_1840,C_1841] :
      ( r4_lattice3(B_1838,'#skF_1'(A_1839,B_1840,a_2_2_lattice3(B_1838,C_1841)),C_1841)
      | ~ l3_lattices(B_1838)
      | ~ v4_lattice3(B_1838)
      | ~ v10_lattices(B_1838)
      | v2_struct_0(B_1838)
      | r3_lattice3(A_1839,B_1840,a_2_2_lattice3(B_1838,C_1841))
      | ~ m1_subset_1(B_1840,u1_struct_0(A_1839))
      | ~ l3_lattices(A_1839)
      | v2_struct_0(A_1839) ) ),
    inference(resolution,[status(thm)],[c_6,c_25893])).

tff(c_10,plain,(
    ! [A_23,D_44,B_35,C_41] :
      ( r1_lattices(A_23,D_44,B_35)
      | ~ r2_hidden(D_44,C_41)
      | ~ m1_subset_1(D_44,u1_struct_0(A_23))
      | ~ r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2789,plain,(
    ! [A_450,B_451] :
      ( r1_lattices(A_450,'#skF_6'('#skF_7','#skF_8','#skF_9'),B_451)
      | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0(A_450))
      | ~ r4_lattice3(A_450,B_451,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_451,u1_struct_0(A_450))
      | ~ l3_lattices(A_450)
      | v2_struct_0(A_450) ) ),
    inference(resolution,[status(thm)],[c_2397,c_10])).

tff(c_2791,plain,(
    ! [B_451] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_451)
      | ~ r4_lattice3('#skF_7',B_451,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2422,c_2789])).

tff(c_2797,plain,(
    ! [B_451] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_451)
      | ~ r4_lattice3('#skF_7',B_451,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2791])).

tff(c_2798,plain,(
    ! [B_451] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_451)
      | ~ r4_lattice3('#skF_7',B_451,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2797])).

tff(c_25950,plain,(
    ! [A_1839,B_1840] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1840,u1_struct_0(A_1839))
      | ~ l3_lattices(A_1839)
      | v2_struct_0(A_1839) ) ),
    inference(resolution,[status(thm)],[c_25921,c_2798])).

tff(c_25984,plain,(
    ! [A_1839,B_1840] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_1839,B_1840,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1840,u1_struct_0(A_1839))
      | ~ l3_lattices(A_1839)
      | v2_struct_0(A_1839) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_25950])).

tff(c_26218,plain,(
    ! [A_1854,B_1855] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1854,B_1855,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1854,B_1855,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | r3_lattice3(A_1854,B_1855,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1855,u1_struct_0(A_1854))
      | ~ l3_lattices(A_1854)
      | v2_struct_0(A_1854) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_25984])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ r1_lattices(A_1,B_13,'#skF_1'(A_1,B_13,C_19))
      | r3_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26222,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_26218,c_4])).

tff(c_26225,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_26222])).

tff(c_26226,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26225])).

tff(c_26227,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_26226])).

tff(c_26230,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_26227])).

tff(c_26233,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_26230])).

tff(c_26234,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26233])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_128,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden('#skF_2'(A_128,B_129,C_130),C_130)
      | r4_lattice3(A_128,B_129,C_130)
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l3_lattices(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_728,plain,(
    ! [A_266,B_267,B_268,C_269] :
      ( '#skF_4'('#skF_2'(A_266,B_267,a_2_1_lattice3(B_268,C_269)),B_268,C_269) = '#skF_2'(A_266,B_267,a_2_1_lattice3(B_268,C_269))
      | ~ l3_lattices(B_268)
      | v2_struct_0(B_268)
      | r4_lattice3(A_266,B_267,a_2_1_lattice3(B_268,C_269))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l3_lattices(A_266)
      | v2_struct_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_128,c_32])).

tff(c_739,plain,(
    ! [A_266,B_267] :
      ( r1_lattices('#skF_7','#skF_2'(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | r4_lattice3(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l3_lattices(A_266)
      | v2_struct_0(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_238])).

tff(c_758,plain,(
    ! [A_266,B_267] :
      ( r1_lattices('#skF_7','#skF_2'(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | v2_struct_0('#skF_7')
      | r4_lattice3(A_266,B_267,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l3_lattices(A_266)
      | v2_struct_0(A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_739])).

tff(c_881,plain,(
    ! [A_282,B_283] :
      ( r1_lattices('#skF_7','#skF_2'(A_282,B_283,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_282,B_283,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | r4_lattice3(A_282,B_283,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_283,u1_struct_0(A_282))
      | ~ l3_lattices(A_282)
      | v2_struct_0(A_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_758])).

tff(c_907,plain,(
    ! [A_286,B_287] :
      ( r1_lattices('#skF_7','#skF_2'(A_286,B_287,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | r4_lattice3(A_286,B_287,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_287,u1_struct_0(A_286))
      | ~ l3_lattices(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_14,c_881])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_911,plain,
    ( r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_907,c_12])).

tff(c_914,plain,
    ( r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_911])).

tff(c_915,plain,(
    r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_914])).

tff(c_20,plain,(
    ! [A_45,B_52,C_53] :
      ( r4_lattice3(A_45,'#skF_3'(A_45,B_52,C_53),B_52)
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    ! [A_45,B_52,C_53] :
      ( m1_subset_1('#skF_3'(A_45,B_52,C_53),u1_struct_0(A_45))
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [D_68,B_64,C_65] :
      ( r2_hidden(D_68,a_2_2_lattice3(B_64,C_65))
      | ~ r4_lattice3(B_64,D_68,C_65)
      | ~ m1_subset_1(D_68,u1_struct_0(B_64))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_381,plain,(
    ! [A_216,B_217,C_218] :
      ( r4_lattice3(A_216,'#skF_3'(A_216,B_217,C_218),B_217)
      | k15_lattice3(A_216,B_217) = C_218
      | ~ r4_lattice3(A_216,C_218,B_217)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ v4_lattice3(A_216)
      | ~ v10_lattices(A_216)
      | ~ l3_lattices(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_149,plain,(
    ! [D_153,B_154,C_155] :
      ( r2_hidden(D_153,a_2_2_lattice3(B_154,C_155))
      | ~ r4_lattice3(B_154,D_153,C_155)
      | ~ m1_subset_1(D_153,u1_struct_0(B_154))
      | ~ l3_lattices(B_154)
      | ~ v4_lattice3(B_154)
      | ~ v10_lattices(B_154)
      | v2_struct_0(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ! [A_63,B_64,C_65] :
      ( '#skF_5'(A_63,B_64,C_65) = A_63
      | ~ r2_hidden(A_63,a_2_2_lattice3(B_64,C_65))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_153,plain,(
    ! [D_153,B_154,C_155] :
      ( '#skF_5'(D_153,B_154,C_155) = D_153
      | ~ r4_lattice3(B_154,D_153,C_155)
      | ~ m1_subset_1(D_153,u1_struct_0(B_154))
      | ~ l3_lattices(B_154)
      | ~ v4_lattice3(B_154)
      | ~ v10_lattices(B_154)
      | v2_struct_0(B_154) ) ),
    inference(resolution,[status(thm)],[c_149,c_40])).

tff(c_2564,plain,(
    ! [A_436,B_437,C_438] :
      ( '#skF_5'('#skF_3'(A_436,B_437,C_438),A_436,B_437) = '#skF_3'(A_436,B_437,C_438)
      | ~ m1_subset_1('#skF_3'(A_436,B_437,C_438),u1_struct_0(A_436))
      | k15_lattice3(A_436,B_437) = C_438
      | ~ r4_lattice3(A_436,C_438,B_437)
      | ~ m1_subset_1(C_438,u1_struct_0(A_436))
      | ~ v4_lattice3(A_436)
      | ~ v10_lattices(A_436)
      | ~ l3_lattices(A_436)
      | v2_struct_0(A_436) ) ),
    inference(resolution,[status(thm)],[c_381,c_153])).

tff(c_3064,plain,(
    ! [A_471,B_472,C_473] :
      ( '#skF_5'('#skF_3'(A_471,B_472,C_473),A_471,B_472) = '#skF_3'(A_471,B_472,C_473)
      | k15_lattice3(A_471,B_472) = C_473
      | ~ r4_lattice3(A_471,C_473,B_472)
      | ~ m1_subset_1(C_473,u1_struct_0(A_471))
      | ~ v4_lattice3(A_471)
      | ~ v10_lattices(A_471)
      | ~ l3_lattices(A_471)
      | v2_struct_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_22,c_2564])).

tff(c_3082,plain,(
    ! [B_472] :
      ( '#skF_5'('#skF_3'('#skF_7',B_472,'#skF_8'),'#skF_7',B_472) = '#skF_3'('#skF_7',B_472,'#skF_8')
      | k15_lattice3('#skF_7',B_472) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_472)
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_3064])).

tff(c_3096,plain,(
    ! [B_472] :
      ( '#skF_5'('#skF_3'('#skF_7',B_472,'#skF_8'),'#skF_7',B_472) = '#skF_3'('#skF_7',B_472,'#skF_8')
      | k15_lattice3('#skF_7',B_472) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_472)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_3082])).

tff(c_3097,plain,(
    ! [B_472] :
      ( '#skF_5'('#skF_3'('#skF_7',B_472,'#skF_8'),'#skF_7',B_472) = '#skF_3'('#skF_7',B_472,'#skF_8')
      | k15_lattice3('#skF_7',B_472) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3096])).

tff(c_2418,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2397,c_32])).

tff(c_2431,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2418])).

tff(c_2432,plain,(
    '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2431])).

tff(c_2514,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_30])).

tff(c_2544,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2397,c_2514])).

tff(c_2545,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2544])).

tff(c_2192,plain,(
    ! [A_69,B_81,C_87] :
      ( '#skF_4'('#skF_6'(A_69,B_81,C_87),A_69,C_87) = '#skF_6'(A_69,B_81,C_87)
      | k16_lattice3(A_69,C_87) = B_81
      | ~ r3_lattice3(A_69,B_81,C_87)
      | ~ m1_subset_1(B_81,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_52,c_2189])).

tff(c_2434,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2422,c_2192])).

tff(c_2455,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2434])).

tff(c_3298,plain,(
    ! [C_486] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_486),'#skF_7',C_486) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_486)
      | k16_lattice3('#skF_7',C_486) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2455])).

tff(c_3328,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3298,c_238])).

tff(c_3349,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2545,c_3328])).

tff(c_3357,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3349])).

tff(c_3360,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3357])).

tff(c_3363,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3360])).

tff(c_3364,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3363])).

tff(c_3365,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3364])).

tff(c_3368,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_3365])).

tff(c_3371,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2422,c_2545,c_3368])).

tff(c_3372,plain,(
    k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3371])).

tff(c_3385,plain,(
    '#skF_6'('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3372,c_58])).

tff(c_6926,plain,(
    ! [B_798,A_799,B_800,C_801] :
      ( r4_lattice3(B_798,'#skF_1'(A_799,B_800,a_2_2_lattice3(B_798,C_801)),C_801)
      | ~ r2_hidden('#skF_1'(A_799,B_800,a_2_2_lattice3(B_798,C_801)),a_2_2_lattice3(B_798,C_801))
      | ~ l3_lattices(B_798)
      | ~ v4_lattice3(B_798)
      | ~ v10_lattices(B_798)
      | v2_struct_0(B_798)
      | ~ l3_lattices(B_798)
      | ~ v4_lattice3(B_798)
      | ~ v10_lattices(B_798)
      | v2_struct_0(B_798)
      | r3_lattice3(A_799,B_800,a_2_2_lattice3(B_798,C_801))
      | ~ m1_subset_1(B_800,u1_struct_0(A_799))
      | ~ l3_lattices(A_799)
      | v2_struct_0(A_799) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_38])).

tff(c_6937,plain,(
    ! [B_802,A_803,B_804,C_805] :
      ( r4_lattice3(B_802,'#skF_1'(A_803,B_804,a_2_2_lattice3(B_802,C_805)),C_805)
      | ~ l3_lattices(B_802)
      | ~ v4_lattice3(B_802)
      | ~ v10_lattices(B_802)
      | v2_struct_0(B_802)
      | r3_lattice3(A_803,B_804,a_2_2_lattice3(B_802,C_805))
      | ~ m1_subset_1(B_804,u1_struct_0(A_803))
      | ~ l3_lattices(A_803)
      | v2_struct_0(A_803) ) ),
    inference(resolution,[status(thm)],[c_6,c_6926])).

tff(c_6962,plain,(
    ! [A_803,B_804] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_804,u1_struct_0(A_803))
      | ~ l3_lattices(A_803)
      | v2_struct_0(A_803) ) ),
    inference(resolution,[status(thm)],[c_6937,c_2798])).

tff(c_6992,plain,(
    ! [A_803,B_804] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_803,B_804,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_804,u1_struct_0(A_803))
      | ~ l3_lattices(A_803)
      | v2_struct_0(A_803) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_6962])).

tff(c_7126,plain,(
    ! [A_809,B_810] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_809,B_810,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_809,B_810,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | r3_lattice3(A_809,B_810,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_810,u1_struct_0(A_809))
      | ~ l3_lattices(A_809)
      | v2_struct_0(A_809) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6992])).

tff(c_7130,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_7126,c_4])).

tff(c_7133,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_7130])).

tff(c_7134,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7133])).

tff(c_7135,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_7134])).

tff(c_7138,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_7135])).

tff(c_7141,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_7138])).

tff(c_7142,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7141])).

tff(c_3098,plain,(
    ! [B_474] :
      ( '#skF_5'('#skF_3'('#skF_7',B_474,'#skF_8'),'#skF_7',B_474) = '#skF_3'('#skF_7',B_474,'#skF_8')
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3096])).

tff(c_2803,plain,(
    ! [B_452] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_452)
      | ~ r4_lattice3('#skF_7',B_452,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_452,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2797])).

tff(c_2814,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_2803])).

tff(c_2824,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2814])).

tff(c_2825,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2824])).

tff(c_3105,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3098,c_2825])).

tff(c_3147,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_3105])).

tff(c_8237,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_8240,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_8237])).

tff(c_8243,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_8240])).

tff(c_8244,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8243])).

tff(c_8245,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8244])).

tff(c_8248,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_8245])).

tff(c_8251,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_8248])).

tff(c_8252,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8251])).

tff(c_54,plain,(
    ! [A_91,B_93] :
      ( k16_lattice3(A_91,a_2_2_lattice3(A_91,B_93)) = k15_lattice3(A_91,B_93)
      | ~ l3_lattices(A_91)
      | ~ v4_lattice3(A_91)
      | ~ v10_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_158,plain,(
    ! [A_159,B_160,C_161] :
      ( r3_lattices(A_159,B_160,k16_lattice3(A_159,C_161))
      | ~ r3_lattice3(A_159,B_160,C_161)
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l3_lattices(A_159)
      | ~ v4_lattice3(A_159)
      | ~ v10_lattices(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_161,plain,(
    ! [A_91,B_160,B_93] :
      ( r3_lattices(A_91,B_160,k15_lattice3(A_91,B_93))
      | ~ r3_lattice3(A_91,B_160,a_2_2_lattice3(A_91,B_93))
      | ~ m1_subset_1(B_160,u1_struct_0(A_91))
      | ~ l3_lattices(A_91)
      | ~ v4_lattice3(A_91)
      | ~ v10_lattices(A_91)
      | v2_struct_0(A_91)
      | ~ l3_lattices(A_91)
      | ~ v4_lattice3(A_91)
      | ~ v10_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_158])).

tff(c_8331,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8252,c_161])).

tff(c_8364,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_8331])).

tff(c_8603,plain,(
    ! [B_904] :
      ( r3_lattices('#skF_7',B_904,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_904,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_904,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8364])).

tff(c_8609,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_7142,c_8603])).

tff(c_8643,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_8609])).

tff(c_48,plain,(
    ! [A_69,B_81,C_87] :
      ( ~ r3_lattices(A_69,'#skF_6'(A_69,B_81,C_87),B_81)
      | k16_lattice3(A_69,C_87) = B_81
      | ~ r3_lattice3(A_69,B_81,C_87)
      | ~ m1_subset_1(B_81,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8674,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8643,c_48])).

tff(c_8677,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_8674])).

tff(c_8679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_8677])).

tff(c_8680,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_8244])).

tff(c_8782,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_8680])).

tff(c_8785,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_8782])).

tff(c_8786,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8785])).

tff(c_8823,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8786,c_161])).

tff(c_8856,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_8823])).

tff(c_9095,plain,(
    ! [B_912] :
      ( r3_lattices('#skF_7',B_912,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_912,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_912,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8856])).

tff(c_9101,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_7142,c_9095])).

tff(c_9135,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_9101])).

tff(c_9183,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9135,c_48])).

tff(c_9186,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_9183])).

tff(c_9188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_9186])).

tff(c_9190,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_9211,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9190,c_40])).

tff(c_9232,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_9211])).

tff(c_9233,plain,(
    '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9232])).

tff(c_42,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1('#skF_5'(A_63,B_64,C_65),u1_struct_0(B_64))
      | ~ r2_hidden(A_63,a_2_2_lattice3(B_64,C_65))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_239,plain,(
    ! [A_173,D_174,B_175,C_176] :
      ( r1_lattices(A_173,D_174,B_175)
      | ~ r2_hidden(D_174,C_176)
      | ~ m1_subset_1(D_174,u1_struct_0(A_173))
      | ~ r4_lattice3(A_173,B_175,C_176)
      | ~ m1_subset_1(B_175,u1_struct_0(A_173))
      | ~ l3_lattices(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_764,plain,(
    ! [B_270,A_271,C_274,D_272,B_273] :
      ( r1_lattices(A_271,D_272,B_273)
      | ~ m1_subset_1(D_272,u1_struct_0(A_271))
      | ~ r4_lattice3(A_271,B_273,a_2_1_lattice3(B_270,C_274))
      | ~ m1_subset_1(B_273,u1_struct_0(A_271))
      | ~ l3_lattices(A_271)
      | v2_struct_0(A_271)
      | ~ r3_lattice3(B_270,D_272,C_274)
      | ~ m1_subset_1(D_272,u1_struct_0(B_270))
      | ~ l3_lattices(B_270)
      | v2_struct_0(B_270) ) ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_778,plain,(
    ! [B_273,B_270,C_274] :
      ( r1_lattices('#skF_7','#skF_8',B_273)
      | ~ r4_lattice3('#skF_7',B_273,a_2_1_lattice3(B_270,C_274))
      | ~ m1_subset_1(B_273,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r3_lattice3(B_270,'#skF_8',C_274)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_270))
      | ~ l3_lattices(B_270)
      | v2_struct_0(B_270) ) ),
    inference(resolution,[status(thm)],[c_64,c_764])).

tff(c_787,plain,(
    ! [B_273,B_270,C_274] :
      ( r1_lattices('#skF_7','#skF_8',B_273)
      | ~ r4_lattice3('#skF_7',B_273,a_2_1_lattice3(B_270,C_274))
      | ~ m1_subset_1(B_273,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ r3_lattice3(B_270,'#skF_8',C_274)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_270))
      | ~ l3_lattices(B_270)
      | v2_struct_0(B_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_778])).

tff(c_789,plain,(
    ! [B_275,B_276,C_277] :
      ( r1_lattices('#skF_7','#skF_8',B_275)
      | ~ r4_lattice3('#skF_7',B_275,a_2_1_lattice3(B_276,C_277))
      | ~ m1_subset_1(B_275,u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_276,'#skF_8',C_277)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_276))
      | ~ l3_lattices(B_276)
      | v2_struct_0(B_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_787])).

tff(c_797,plain,(
    ! [A_63,B_276,C_277] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_276,C_277)))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_276,C_277)),u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_276,'#skF_8',C_277)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_276))
      | ~ l3_lattices(B_276)
      | v2_struct_0(B_276)
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_276,C_277)))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_789])).

tff(c_804,plain,(
    ! [A_63,B_276,C_277] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_276,C_277)))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_276,C_277)),u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_276,'#skF_8',C_277)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_276))
      | ~ l3_lattices(B_276)
      | v2_struct_0(B_276)
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_276,C_277)))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_797])).

tff(c_1434,plain,(
    ! [A_339,B_340,C_341] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_339,'#skF_7',a_2_1_lattice3(B_340,C_341)))
      | ~ m1_subset_1('#skF_5'(A_339,'#skF_7',a_2_1_lattice3(B_340,C_341)),u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_340,'#skF_8',C_341)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_340))
      | ~ l3_lattices(B_340)
      | v2_struct_0(B_340)
      | ~ r2_hidden(A_339,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_340,C_341))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_804])).

tff(c_1453,plain,(
    ! [A_63,B_340,C_341] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_340,C_341)))
      | ~ r3_lattice3(B_340,'#skF_8',C_341)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_340))
      | ~ l3_lattices(B_340)
      | v2_struct_0(B_340)
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_340,C_341)))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1434])).

tff(c_1465,plain,(
    ! [A_63,B_340,C_341] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_340,C_341)))
      | ~ r3_lattice3(B_340,'#skF_8',C_341)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_340))
      | ~ l3_lattices(B_340)
      | v2_struct_0(B_340)
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_340,C_341)))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1453])).

tff(c_1466,plain,(
    ! [A_63,B_340,C_341] :
      ( r1_lattices('#skF_7','#skF_8','#skF_5'(A_63,'#skF_7',a_2_1_lattice3(B_340,C_341)))
      | ~ r3_lattice3(B_340,'#skF_8',C_341)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_340))
      | ~ l3_lattices(B_340)
      | v2_struct_0(B_340)
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3(B_340,C_341))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1465])).

tff(c_9276,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9233,c_1466])).

tff(c_9327,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9190,c_66,c_64,c_60,c_9276])).

tff(c_9328,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9327])).

tff(c_18,plain,(
    ! [A_45,C_53,B_52] :
      ( ~ r1_lattices(A_45,C_53,'#skF_3'(A_45,B_52,C_53))
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9345,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9328,c_18])).

tff(c_9348,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_9345])).

tff(c_9349,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9348])).

tff(c_9386,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9349,c_161])).

tff(c_9419,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_9386])).

tff(c_9783,plain,(
    ! [B_926] :
      ( r3_lattices('#skF_7',B_926,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_926,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_926,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9419])).

tff(c_9789,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_7142,c_9783])).

tff(c_9823,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_9789])).

tff(c_9902,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9823,c_48])).

tff(c_9905,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_9902])).

tff(c_9907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_9905])).

tff(c_9908,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_7134])).

tff(c_11034,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_11037,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_11034])).

tff(c_11040,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_11037])).

tff(c_11041,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11040])).

tff(c_11042,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_11041])).

tff(c_11045,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_11042])).

tff(c_11048,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_11045])).

tff(c_11049,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11048])).

tff(c_11086,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11049,c_161])).

tff(c_11119,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_11086])).

tff(c_11394,plain,(
    ! [B_1023] :
      ( r3_lattices('#skF_7',B_1023,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1023,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1023,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11119])).

tff(c_11400,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9908,c_11394])).

tff(c_11434,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_11400])).

tff(c_11465,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_11434,c_48])).

tff(c_11468,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_11465])).

tff(c_11470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_11468])).

tff(c_11471,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11041])).

tff(c_11573,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_11471])).

tff(c_11576,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_11573])).

tff(c_11577,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11576])).

tff(c_11614,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11577,c_161])).

tff(c_11647,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_11614])).

tff(c_11880,plain,(
    ! [B_1031] :
      ( r3_lattices('#skF_7',B_1031,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1031,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1031,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11647])).

tff(c_11886,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9908,c_11880])).

tff(c_11920,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_11886])).

tff(c_11999,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_11920,c_48])).

tff(c_12002,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_11999])).

tff(c_12004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_12002])).

tff(c_12006,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_3138,plain,(
    ! [B_474] :
      ( m1_subset_1('#skF_3'('#skF_7',B_474,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3098,c_42])).

tff(c_3155,plain,(
    ! [B_474] :
      ( m1_subset_1('#skF_3'('#skF_7',B_474,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3138])).

tff(c_3156,plain,(
    ! [B_474] :
      ( m1_subset_1('#skF_3'('#skF_7',B_474,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3155])).

tff(c_12018,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_12006,c_3156])).

tff(c_12039,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_12018])).

tff(c_12050,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12039])).

tff(c_12196,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12050,c_161])).

tff(c_12229,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_12196])).

tff(c_12624,plain,(
    ! [B_1045] :
      ( r3_lattices('#skF_7',B_1045,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1045,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1045,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12229])).

tff(c_12630,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9908,c_12624])).

tff(c_12664,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_12630])).

tff(c_12695,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12664,c_48])).

tff(c_12698,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_3372,c_12695])).

tff(c_12700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3385,c_12698])).

tff(c_12702,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12039])).

tff(c_12027,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12006,c_40])).

tff(c_12048,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_12027])).

tff(c_12049,plain,(
    '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12048])).

tff(c_12843,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12049,c_1466])).

tff(c_12897,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12006,c_66,c_64,c_60,c_12843])).

tff(c_12898,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12897])).

tff(c_12916,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12898,c_18])).

tff(c_12919,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_12916])).

tff(c_12921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12702,c_12919])).

tff(c_12922,plain,(
    ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3364])).

tff(c_12982,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_12922])).

tff(c_12985,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2422,c_2545,c_12982])).

tff(c_12986,plain,(
    k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12985])).

tff(c_12988,plain,(
    '#skF_6'('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12986,c_58])).

tff(c_15571,plain,(
    ! [A_1291,B_1292,B_1293,C_1294] :
      ( m1_subset_1('#skF_1'(A_1291,B_1292,a_2_2_lattice3(B_1293,C_1294)),u1_struct_0(B_1293))
      | ~ r2_hidden('#skF_1'(A_1291,B_1292,a_2_2_lattice3(B_1293,C_1294)),a_2_2_lattice3(B_1293,C_1294))
      | ~ l3_lattices(B_1293)
      | ~ v4_lattice3(B_1293)
      | ~ v10_lattices(B_1293)
      | v2_struct_0(B_1293)
      | ~ l3_lattices(B_1293)
      | ~ v4_lattice3(B_1293)
      | ~ v10_lattices(B_1293)
      | v2_struct_0(B_1293)
      | r3_lattice3(A_1291,B_1292,a_2_2_lattice3(B_1293,C_1294))
      | ~ m1_subset_1(B_1292,u1_struct_0(A_1291))
      | ~ l3_lattices(A_1291)
      | v2_struct_0(A_1291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_42])).

tff(c_15581,plain,(
    ! [A_1,B_13,B_1293,C_1294] :
      ( m1_subset_1('#skF_1'(A_1,B_13,a_2_2_lattice3(B_1293,C_1294)),u1_struct_0(B_1293))
      | ~ l3_lattices(B_1293)
      | ~ v4_lattice3(B_1293)
      | ~ v10_lattices(B_1293)
      | v2_struct_0(B_1293)
      | r3_lattice3(A_1,B_13,a_2_2_lattice3(B_1293,C_1294))
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_15571])).

tff(c_16755,plain,(
    ! [B_1383,A_1384,B_1385,C_1386] :
      ( r4_lattice3(B_1383,'#skF_1'(A_1384,B_1385,a_2_2_lattice3(B_1383,C_1386)),C_1386)
      | ~ r2_hidden('#skF_1'(A_1384,B_1385,a_2_2_lattice3(B_1383,C_1386)),a_2_2_lattice3(B_1383,C_1386))
      | ~ l3_lattices(B_1383)
      | ~ v4_lattice3(B_1383)
      | ~ v10_lattices(B_1383)
      | v2_struct_0(B_1383)
      | ~ l3_lattices(B_1383)
      | ~ v4_lattice3(B_1383)
      | ~ v10_lattices(B_1383)
      | v2_struct_0(B_1383)
      | r3_lattice3(A_1384,B_1385,a_2_2_lattice3(B_1383,C_1386))
      | ~ m1_subset_1(B_1385,u1_struct_0(A_1384))
      | ~ l3_lattices(A_1384)
      | v2_struct_0(A_1384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_38])).

tff(c_16766,plain,(
    ! [B_1387,A_1388,B_1389,C_1390] :
      ( r4_lattice3(B_1387,'#skF_1'(A_1388,B_1389,a_2_2_lattice3(B_1387,C_1390)),C_1390)
      | ~ l3_lattices(B_1387)
      | ~ v4_lattice3(B_1387)
      | ~ v10_lattices(B_1387)
      | v2_struct_0(B_1387)
      | r3_lattice3(A_1388,B_1389,a_2_2_lattice3(B_1387,C_1390))
      | ~ m1_subset_1(B_1389,u1_struct_0(A_1388))
      | ~ l3_lattices(A_1388)
      | v2_struct_0(A_1388) ) ),
    inference(resolution,[status(thm)],[c_6,c_16755])).

tff(c_16795,plain,(
    ! [A_1388,B_1389] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1389,u1_struct_0(A_1388))
      | ~ l3_lattices(A_1388)
      | v2_struct_0(A_1388) ) ),
    inference(resolution,[status(thm)],[c_16766,c_2798])).

tff(c_16829,plain,(
    ! [A_1388,B_1389] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | r3_lattice3(A_1388,B_1389,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1389,u1_struct_0(A_1388))
      | ~ l3_lattices(A_1388)
      | v2_struct_0(A_1388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_16795])).

tff(c_16853,plain,(
    ! [A_1392,B_1393] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_1'(A_1392,B_1393,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1392,B_1393,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
      | r3_lattice3(A_1392,B_1393,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1393,u1_struct_0(A_1392))
      | ~ l3_lattices(A_1392)
      | v2_struct_0(A_1392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16829])).

tff(c_16857,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_16853,c_4])).

tff(c_16860,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_16857])).

tff(c_16861,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7'))
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16860])).

tff(c_16862,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_16861])).

tff(c_16865,plain,
    ( ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_15581,c_16862])).

tff(c_16871,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422,c_70,c_68,c_16865])).

tff(c_16872,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16871])).

tff(c_18427,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_18430,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_18427])).

tff(c_18433,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_18430])).

tff(c_18434,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18433])).

tff(c_18435,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_18434])).

tff(c_18438,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_18435])).

tff(c_18441,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_18438])).

tff(c_18442,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18441])).

tff(c_18496,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18442,c_161])).

tff(c_18529,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_18496])).

tff(c_18768,plain,(
    ! [B_1477] :
      ( r3_lattices('#skF_7',B_1477,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1477,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1477,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18529])).

tff(c_18774,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_16872,c_18768])).

tff(c_18808,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_18774])).

tff(c_18839,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_18808,c_48])).

tff(c_18842,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_18839])).

tff(c_18844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_18842])).

tff(c_18845,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_18434])).

tff(c_18922,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_18845])).

tff(c_18925,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_18922])).

tff(c_18926,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18925])).

tff(c_18963,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18926,c_161])).

tff(c_18996,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_18963])).

tff(c_19235,plain,(
    ! [B_1485] :
      ( r3_lattices('#skF_7',B_1485,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1485,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1485,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18996])).

tff(c_19241,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_16872,c_19235])).

tff(c_19275,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_19241])).

tff(c_19354,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_19275,c_48])).

tff(c_19357,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_19354])).

tff(c_19359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_19357])).

tff(c_19361,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_19382,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_19361,c_40])).

tff(c_19403,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_19382])).

tff(c_19404,plain,(
    '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19403])).

tff(c_19447,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19404,c_1466])).

tff(c_19498,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19361,c_66,c_64,c_60,c_19447])).

tff(c_19499,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19498])).

tff(c_19516,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_19499,c_18])).

tff(c_19519,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_19516])).

tff(c_19520,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19519])).

tff(c_19557,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19520,c_161])).

tff(c_19590,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_19557])).

tff(c_19966,plain,(
    ! [B_1499] :
      ( r3_lattices('#skF_7',B_1499,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1499,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1499,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19590])).

tff(c_19972,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_16872,c_19966])).

tff(c_20006,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_19972])).

tff(c_20054,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20006,c_48])).

tff(c_20057,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_20054])).

tff(c_20059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_20057])).

tff(c_20060,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_16861])).

tff(c_21606,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_21609,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_21606])).

tff(c_21612,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_21609])).

tff(c_21613,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21612])).

tff(c_21614,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_21613])).

tff(c_21658,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_21614])).

tff(c_21661,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_21658])).

tff(c_21662,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21661])).

tff(c_21699,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21662,c_161])).

tff(c_21732,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_21699])).

tff(c_22013,plain,(
    ! [B_1586] :
      ( r3_lattices('#skF_7',B_1586,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1586,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1586,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21732])).

tff(c_22019,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_20060,c_22013])).

tff(c_22053,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_22019])).

tff(c_22084,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22053,c_48])).

tff(c_22087,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_22084])).

tff(c_22089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_22087])).

tff(c_22090,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_21613])).

tff(c_22150,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_22090])).

tff(c_22153,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_22150])).

tff(c_22154,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_22153])).

tff(c_22191,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22154,c_161])).

tff(c_22224,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_22191])).

tff(c_22505,plain,(
    ! [B_1594] :
      ( r3_lattices('#skF_7',B_1594,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1594,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1594,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_22224])).

tff(c_22511,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_20060,c_22505])).

tff(c_22545,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_22511])).

tff(c_22576,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22545,c_48])).

tff(c_22579,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_22576])).

tff(c_22581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_22579])).

tff(c_22583,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_22595,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_22583,c_3156])).

tff(c_22616,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_22595])).

tff(c_22627,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_22616])).

tff(c_22706,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22627,c_161])).

tff(c_22739,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_22706])).

tff(c_22978,plain,(
    ! [B_1602] :
      ( r3_lattices('#skF_7',B_1602,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_1602,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_1602,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_22739])).

tff(c_22984,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_20060,c_22978])).

tff(c_23018,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_22984])).

tff(c_23049,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_23018,c_48])).

tff(c_23052,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_12986,c_23049])).

tff(c_23054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12988,c_23052])).

tff(c_23056,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_22616])).

tff(c_22604,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22583,c_40])).

tff(c_22625,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_22604])).

tff(c_22626,plain,(
    '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_22625])).

tff(c_23197,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22626,c_1466])).

tff(c_23251,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22583,c_66,c_64,c_60,c_23197])).

tff(c_23252,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23251])).

tff(c_23270,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_23252,c_18])).

tff(c_23273,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_23270])).

tff(c_23275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23056,c_23273])).

tff(c_23277,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3349])).

tff(c_23286,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_23277,c_32])).

tff(c_23295,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23286])).

tff(c_23296,plain,(
    '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23295])).

tff(c_23325,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_23296,c_34])).

tff(c_23354,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23277,c_23325])).

tff(c_23355,plain,(
    m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23354])).

tff(c_23328,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_23296,c_30])).

tff(c_23357,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23277,c_23328])).

tff(c_23358,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23357])).

tff(c_23366,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_23355,c_2192])).

tff(c_23391,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_23366])).

tff(c_26837,plain,(
    ! [C_1930] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_1930),'#skF_7',C_1930) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_1930)
      | k16_lattice3('#skF_7',C_1930) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_1930) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23391])).

tff(c_26877,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_26837,c_238])).

tff(c_26904,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23358,c_26877])).

tff(c_26912,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_26904])).

tff(c_26915,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_26912])).

tff(c_26918,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26915])).

tff(c_26919,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26918])).

tff(c_26920,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_26919])).

tff(c_26923,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_26920])).

tff(c_26926,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_23355,c_23358,c_26923])).

tff(c_26927,plain,(
    '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26926])).

tff(c_23770,plain,(
    ! [A_1651,B_1652] :
      ( r1_lattices(A_1651,'#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_1652)
      | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0(A_1651))
      | ~ r4_lattice3(A_1651,B_1652,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_1652,u1_struct_0(A_1651))
      | ~ l3_lattices(A_1651)
      | v2_struct_0(A_1651) ) ),
    inference(resolution,[status(thm)],[c_23277,c_10])).

tff(c_23772,plain,(
    ! [B_1652] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_1652)
      | ~ r4_lattice3('#skF_7',B_1652,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_1652,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_23355,c_23770])).

tff(c_23778,plain,(
    ! [B_1652] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_1652)
      | ~ r4_lattice3('#skF_7',B_1652,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_1652,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23772])).

tff(c_23779,plain,(
    ! [B_1652] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_1652)
      | ~ r4_lattice3('#skF_7',B_1652,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_1652,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23778])).

tff(c_27549,plain,(
    ! [B_1950] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),B_1950)
      | ~ r4_lattice3('#skF_7',B_1950,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_1950,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26927,c_23779])).

tff(c_27568,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_27549])).

tff(c_27586,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_27568])).

tff(c_28069,plain,(
    ! [A_1988] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_1988,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_1988,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_1988,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_27586])).

tff(c_28097,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3097,c_28069])).

tff(c_28138,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_28097])).

tff(c_29042,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_28138])).

tff(c_29045,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_29042])).

tff(c_29048,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_29045])).

tff(c_29049,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29048])).

tff(c_29050,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_29049])).

tff(c_29053,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_29050])).

tff(c_29056,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_29053])).

tff(c_29057,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29056])).

tff(c_29098,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29057,c_161])).

tff(c_29133,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_29098])).

tff(c_29384,plain,(
    ! [B_2082] :
      ( r3_lattices('#skF_7',B_2082,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2082,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2082,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29133])).

tff(c_29393,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26234,c_29384])).

tff(c_29430,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_29393])).

tff(c_29461,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_29430,c_48])).

tff(c_29464,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_29461])).

tff(c_29466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_29464])).

tff(c_29467,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_29049])).

tff(c_29532,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_29467])).

tff(c_29535,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_29532])).

tff(c_29536,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29535])).

tff(c_29579,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29536,c_161])).

tff(c_29617,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_29579])).

tff(c_29858,plain,(
    ! [B_2087] :
      ( r3_lattices('#skF_7',B_2087,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2087,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2087,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29617])).

tff(c_29867,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26234,c_29858])).

tff(c_29904,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_29867])).

tff(c_29940,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_29904,c_48])).

tff(c_29943,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_29940])).

tff(c_29945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_29943])).

tff(c_29947,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_28138])).

tff(c_30040,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_29947,c_3156])).

tff(c_30061,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_30040])).

tff(c_30072,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_30061])).

tff(c_30113,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30072,c_161])).

tff(c_30148,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_30113])).

tff(c_30399,plain,(
    ! [B_2099] :
      ( r3_lattices('#skF_7',B_2099,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2099,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2099,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_30148])).

tff(c_30408,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26234,c_30399])).

tff(c_30445,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_30408])).

tff(c_30476,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_30445,c_48])).

tff(c_30479,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_30476])).

tff(c_30481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_30479])).

tff(c_30483,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30061])).

tff(c_30482,plain,(
    m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_30061])).

tff(c_3141,plain,(
    ! [B_474] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_474,'#skF_8'),B_474)
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3098,c_38])).

tff(c_3158,plain,(
    ! [B_474] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_474,'#skF_8'),B_474)
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3141])).

tff(c_3159,plain,(
    ! [B_474] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_474,'#skF_8'),B_474)
      | ~ r2_hidden('#skF_3'('#skF_7',B_474,'#skF_8'),a_2_2_lattice3('#skF_7',B_474))
      | k15_lattice3('#skF_7',B_474) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3158])).

tff(c_30037,plain,
    ( r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_29947,c_3159])).

tff(c_30058,plain,
    ( r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_30037])).

tff(c_30545,plain,(
    r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_30483,c_30058])).

tff(c_788,plain,(
    ! [B_273,B_270,C_274] :
      ( r1_lattices('#skF_7','#skF_8',B_273)
      | ~ r4_lattice3('#skF_7',B_273,a_2_1_lattice3(B_270,C_274))
      | ~ m1_subset_1(B_273,u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_270,'#skF_8',C_274)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_270))
      | ~ l3_lattices(B_270)
      | v2_struct_0(B_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_787])).

tff(c_30570,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_30545,c_788])).

tff(c_30613,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_30482,c_30570])).

tff(c_30614,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_30613])).

tff(c_30621,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_30614,c_18])).

tff(c_30624,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_30621])).

tff(c_30626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_30483,c_30624])).

tff(c_30627,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_26226])).

tff(c_31473,plain,(
    ! [C_2194] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_2194),'#skF_7',C_2194) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_2194)
      | k16_lattice3('#skF_7',C_2194) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_2194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23391])).

tff(c_31513,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_31473,c_238])).

tff(c_31540,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23358,c_31513])).

tff(c_31548,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_31540])).

tff(c_31598,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_31548])).

tff(c_31601,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_31598])).

tff(c_31602,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_31601])).

tff(c_31604,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_31602])).

tff(c_31607,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_31604])).

tff(c_31610,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_23355,c_23358,c_31607])).

tff(c_31611,plain,(
    '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_31610])).

tff(c_32204,plain,(
    ! [B_2216] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),B_2216)
      | ~ r4_lattice3('#skF_7',B_2216,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_2216,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31611,c_23779])).

tff(c_32223,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_32204])).

tff(c_32241,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_32223])).

tff(c_32810,plain,(
    ! [A_2256] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_2256,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_2256,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_2256,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_32241])).

tff(c_32842,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3097,c_32810])).

tff(c_32883,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_32842])).

tff(c_33621,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_32883])).

tff(c_33624,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_33621])).

tff(c_33627,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_33624])).

tff(c_33628,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_33627])).

tff(c_33629,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_33628])).

tff(c_33713,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_33629])).

tff(c_33716,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_33713])).

tff(c_33717,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_33716])).

tff(c_33760,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33717,c_161])).

tff(c_33798,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_33760])).

tff(c_34048,plain,(
    ! [B_2339] :
      ( r3_lattices('#skF_7',B_2339,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2339,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2339,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_33798])).

tff(c_34057,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_30627,c_34048])).

tff(c_34094,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_34057])).

tff(c_34125,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_34094,c_48])).

tff(c_34128,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_34125])).

tff(c_34130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_34128])).

tff(c_34131,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_33628])).

tff(c_34191,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_34131])).

tff(c_34194,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_34191])).

tff(c_34195,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_34194])).

tff(c_34238,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34195,c_161])).

tff(c_34276,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_34238])).

tff(c_34522,plain,(
    ! [B_2345] :
      ( r3_lattices('#skF_7',B_2345,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2345,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2345,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_34276])).

tff(c_34531,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_30627,c_34522])).

tff(c_34568,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_34531])).

tff(c_34599,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_34568,c_48])).

tff(c_34602,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_34599])).

tff(c_34604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_34602])).

tff(c_34606,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_32883])).

tff(c_34623,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_34606,c_3156])).

tff(c_34644,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_34623])).

tff(c_34655,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_34644])).

tff(c_34698,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34655,c_161])).

tff(c_34736,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_7',B_160,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_160,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_70,c_68,c_66,c_34698])).

tff(c_34977,plain,(
    ! [B_2351] :
      ( r3_lattices('#skF_7',B_2351,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_2351,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1(B_2351,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_34736])).

tff(c_34986,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_30627,c_34977])).

tff(c_35023,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_34986])).

tff(c_35059,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_35023,c_48])).

tff(c_35062,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_35059])).

tff(c_35064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_35062])).

tff(c_35066,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_34644])).

tff(c_34632,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_34606,c_40])).

tff(c_34653,plain,
    ( '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_34632])).

tff(c_34654,plain,(
    '#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_34653])).

tff(c_35100,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34654,c_1466])).

tff(c_35143,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34606,c_66,c_64,c_60,c_35100])).

tff(c_35144,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_35143])).

tff(c_35217,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_35144,c_18])).

tff(c_35220,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_915,c_35217])).

tff(c_35222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_35066,c_35220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.19/8.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.60/8.93  
% 18.60/8.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.60/8.93  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 18.60/8.93  
% 18.60/8.93  %Foreground sorts:
% 18.60/8.93  
% 18.60/8.93  
% 18.60/8.93  %Background operators:
% 18.60/8.93  
% 18.60/8.93  
% 18.60/8.93  %Foreground operators:
% 18.60/8.93  tff(l3_lattices, type, l3_lattices: $i > $o).
% 18.60/8.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 18.60/8.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.60/8.93  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 18.60/8.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.60/8.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.60/8.93  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 18.60/8.93  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 18.60/8.93  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 18.60/8.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.60/8.93  tff('#skF_7', type, '#skF_7': $i).
% 18.60/8.93  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 18.60/8.93  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 18.60/8.93  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 18.60/8.93  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 18.60/8.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.60/8.93  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 18.60/8.93  tff(v10_lattices, type, v10_lattices: $i > $o).
% 18.60/8.93  tff('#skF_9', type, '#skF_9': $i).
% 18.60/8.93  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 18.60/8.93  tff('#skF_8', type, '#skF_8': $i).
% 18.60/8.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.60/8.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.60/8.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.60/8.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.60/8.93  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 18.60/8.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.60/8.93  
% 19.00/8.99  tff(f_194, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 19.00/8.99  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 19.00/8.99  tff(f_103, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 19.00/8.99  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 19.00/8.99  tff(f_121, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 19.00/8.99  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 19.00/8.99  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 19.00/8.99  tff(f_157, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 19.00/8.99  tff(f_174, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 19.00/8.99  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_58, plain, (k16_lattice3('#skF_7', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_70, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_68, plain, (v4_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_66, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_60, plain, (r3_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_50, plain, (![A_69, B_81, C_87]: (r3_lattice3(A_69, '#skF_6'(A_69, B_81, C_87), C_87) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.00/8.99  tff(c_52, plain, (![A_69, B_81, C_87]: (m1_subset_1('#skF_6'(A_69, B_81, C_87), u1_struct_0(A_69)) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.00/8.99  tff(c_28, plain, (![D_62, B_58, C_59]: (r2_hidden(D_62, a_2_1_lattice3(B_58, C_59)) | ~r3_lattice3(B_58, D_62, C_59) | ~m1_subset_1(D_62, u1_struct_0(B_58)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.00/8.99  tff(c_330, plain, (![A_197, B_198, C_199]: (r3_lattice3(A_197, '#skF_6'(A_197, B_198, C_199), C_199) | k16_lattice3(A_197, C_199)=B_198 | ~r3_lattice3(A_197, B_198, C_199) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l3_lattices(A_197) | ~v4_lattice3(A_197) | ~v10_lattices(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.00/8.99  tff(c_85, plain, (![D_116, B_117, C_118]: (r2_hidden(D_116, a_2_1_lattice3(B_117, C_118)) | ~r3_lattice3(B_117, D_116, C_118) | ~m1_subset_1(D_116, u1_struct_0(B_117)) | ~l3_lattices(B_117) | v2_struct_0(B_117))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.00/8.99  tff(c_32, plain, (![A_57, B_58, C_59]: ('#skF_4'(A_57, B_58, C_59)=A_57 | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.00/8.99  tff(c_89, plain, (![D_116, B_117, C_118]: ('#skF_4'(D_116, B_117, C_118)=D_116 | ~r3_lattice3(B_117, D_116, C_118) | ~m1_subset_1(D_116, u1_struct_0(B_117)) | ~l3_lattices(B_117) | v2_struct_0(B_117))), inference(resolution, [status(thm)], [c_85, c_32])).
% 19.00/8.99  tff(c_2189, plain, (![A_422, B_423, C_424]: ('#skF_4'('#skF_6'(A_422, B_423, C_424), A_422, C_424)='#skF_6'(A_422, B_423, C_424) | ~m1_subset_1('#skF_6'(A_422, B_423, C_424), u1_struct_0(A_422)) | k16_lattice3(A_422, C_424)=B_423 | ~r3_lattice3(A_422, B_423, C_424) | ~m1_subset_1(B_423, u1_struct_0(A_422)) | ~l3_lattices(A_422) | ~v4_lattice3(A_422) | ~v10_lattices(A_422) | v2_struct_0(A_422))), inference(resolution, [status(thm)], [c_330, c_89])).
% 19.00/8.99  tff(c_2234, plain, (![A_428, B_429, C_430]: ('#skF_4'('#skF_6'(A_428, B_429, C_430), A_428, C_430)='#skF_6'(A_428, B_429, C_430) | k16_lattice3(A_428, C_430)=B_429 | ~r3_lattice3(A_428, B_429, C_430) | ~m1_subset_1(B_429, u1_struct_0(A_428)) | ~l3_lattices(A_428) | ~v4_lattice3(A_428) | ~v10_lattices(A_428) | v2_struct_0(A_428))), inference(resolution, [status(thm)], [c_52, c_2189])).
% 19.00/8.99  tff(c_2248, plain, (![C_430]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_430), '#skF_7', C_430)='#skF_6'('#skF_7', '#skF_8', C_430) | k16_lattice3('#skF_7', C_430)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_430) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_2234])).
% 19.00/8.99  tff(c_2257, plain, (![C_430]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_430), '#skF_7', C_430)='#skF_6'('#skF_7', '#skF_8', C_430) | k16_lattice3('#skF_7', C_430)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_430) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2248])).
% 19.00/8.99  tff(c_2259, plain, (![C_431]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_431), '#skF_7', C_431)='#skF_6'('#skF_7', '#skF_8', C_431) | k16_lattice3('#skF_7', C_431)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_431))), inference(negUnitSimplification, [status(thm)], [c_72, c_2257])).
% 19.00/8.99  tff(c_30, plain, (![B_58, A_57, C_59]: (r3_lattice3(B_58, '#skF_4'(A_57, B_58, C_59), C_59) | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.00/8.99  tff(c_34, plain, (![A_57, B_58, C_59]: (m1_subset_1('#skF_4'(A_57, B_58, C_59), u1_struct_0(B_58)) | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.00/8.99  tff(c_62, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_194])).
% 19.00/8.99  tff(c_162, plain, (![A_162, B_163, D_164, C_165]: (r1_lattices(A_162, B_163, D_164) | ~r2_hidden(D_164, C_165) | ~m1_subset_1(D_164, u1_struct_0(A_162)) | ~r3_lattice3(A_162, B_163, C_165) | ~m1_subset_1(B_163, u1_struct_0(A_162)) | ~l3_lattices(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.00/8.99  tff(c_178, plain, (![A_166, B_167]: (r1_lattices(A_166, B_167, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0(A_166)) | ~r3_lattice3(A_166, B_167, '#skF_9') | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l3_lattices(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_62, c_162])).
% 19.00/8.99  tff(c_180, plain, (![B_167]: (r1_lattices('#skF_7', B_167, '#skF_8') | ~r3_lattice3('#skF_7', B_167, '#skF_9') | ~m1_subset_1(B_167, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_178])).
% 19.00/8.99  tff(c_183, plain, (![B_167]: (r1_lattices('#skF_7', B_167, '#skF_8') | ~r3_lattice3('#skF_7', B_167, '#skF_9') | ~m1_subset_1(B_167, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180])).
% 19.00/8.99  tff(c_185, plain, (![B_168]: (r1_lattices('#skF_7', B_168, '#skF_8') | ~r3_lattice3('#skF_7', B_168, '#skF_9') | ~m1_subset_1(B_168, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_183])).
% 19.00/8.99  tff(c_201, plain, (![A_57, C_59]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_9') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', C_59)) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_185])).
% 19.00/8.99  tff(c_219, plain, (![A_57, C_59]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_9') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', C_59)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_201])).
% 19.00/8.99  tff(c_225, plain, (![A_171, C_172]: (r1_lattices('#skF_7', '#skF_4'(A_171, '#skF_7', C_172), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_171, '#skF_7', C_172), '#skF_9') | ~r2_hidden(A_171, a_2_1_lattice3('#skF_7', C_172)))), inference(negUnitSimplification, [status(thm)], [c_72, c_219])).
% 19.00/8.99  tff(c_232, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_225])).
% 19.00/8.99  tff(c_237, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_232])).
% 19.00/8.99  tff(c_238, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_237])).
% 19.00/8.99  tff(c_2285, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2259, c_238])).
% 19.00/8.99  tff(c_2306, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2285])).
% 19.00/8.99  tff(c_2307, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2306])).
% 19.00/8.99  tff(c_2315, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_2307])).
% 19.00/8.99  tff(c_2318, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_2315])).
% 19.00/8.99  tff(c_2321, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2318])).
% 19.00/8.99  tff(c_2322, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2321])).
% 19.00/8.99  tff(c_2323, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2322])).
% 19.00/8.99  tff(c_2330, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_2323])).
% 19.00/8.99  tff(c_2333, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_2330])).
% 19.00/8.99  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_2333])).
% 19.00/8.99  tff(c_2336, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_2322])).
% 19.00/8.99  tff(c_2390, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_2336])).
% 19.00/8.99  tff(c_2393, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_2390])).
% 19.00/8.99  tff(c_2395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_2393])).
% 19.00/8.99  tff(c_2397, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_2307])).
% 19.00/8.99  tff(c_2291, plain, (![C_431]: (m1_subset_1('#skF_6'('#skF_7', '#skF_8', C_431), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', C_431), a_2_1_lattice3('#skF_7', C_431)) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | k16_lattice3('#skF_7', C_431)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_431))), inference(superposition, [status(thm), theory('equality')], [c_2259, c_34])).
% 19.00/8.99  tff(c_2309, plain, (![C_431]: (m1_subset_1('#skF_6'('#skF_7', '#skF_8', C_431), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', C_431), a_2_1_lattice3('#skF_7', C_431)) | v2_struct_0('#skF_7') | k16_lattice3('#skF_7', C_431)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_431))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2291])).
% 19.00/8.99  tff(c_2310, plain, (![C_431]: (m1_subset_1('#skF_6'('#skF_7', '#skF_8', C_431), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', C_431), a_2_1_lattice3('#skF_7', C_431)) | k16_lattice3('#skF_7', C_431)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_431))), inference(negUnitSimplification, [status(thm)], [c_72, c_2309])).
% 19.00/8.99  tff(c_2409, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2397, c_2310])).
% 19.00/8.99  tff(c_2421, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2409])).
% 19.00/8.99  tff(c_2422, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2421])).
% 19.00/8.99  tff(c_8, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | r3_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.00/8.99  tff(c_6, plain, (![A_1, B_13, C_19]: (r2_hidden('#skF_1'(A_1, B_13, C_19), C_19) | r3_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.00/8.99  tff(c_122, plain, (![A_125, B_126, C_127]: ('#skF_5'(A_125, B_126, C_127)=A_125 | ~r2_hidden(A_125, a_2_2_lattice3(B_126, C_127)) | ~l3_lattices(B_126) | ~v4_lattice3(B_126) | ~v10_lattices(B_126) | v2_struct_0(B_126))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_1286, plain, (![A_320, B_321, B_322, C_323]: ('#skF_5'('#skF_1'(A_320, B_321, a_2_2_lattice3(B_322, C_323)), B_322, C_323)='#skF_1'(A_320, B_321, a_2_2_lattice3(B_322, C_323)) | ~l3_lattices(B_322) | ~v4_lattice3(B_322) | ~v10_lattices(B_322) | v2_struct_0(B_322) | r3_lattice3(A_320, B_321, a_2_2_lattice3(B_322, C_323)) | ~m1_subset_1(B_321, u1_struct_0(A_320)) | ~l3_lattices(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_6, c_122])).
% 19.00/8.99  tff(c_38, plain, (![B_64, A_63, C_65]: (r4_lattice3(B_64, '#skF_5'(A_63, B_64, C_65), C_65) | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_25893, plain, (![B_1832, A_1833, B_1834, C_1835]: (r4_lattice3(B_1832, '#skF_1'(A_1833, B_1834, a_2_2_lattice3(B_1832, C_1835)), C_1835) | ~r2_hidden('#skF_1'(A_1833, B_1834, a_2_2_lattice3(B_1832, C_1835)), a_2_2_lattice3(B_1832, C_1835)) | ~l3_lattices(B_1832) | ~v4_lattice3(B_1832) | ~v10_lattices(B_1832) | v2_struct_0(B_1832) | ~l3_lattices(B_1832) | ~v4_lattice3(B_1832) | ~v10_lattices(B_1832) | v2_struct_0(B_1832) | r3_lattice3(A_1833, B_1834, a_2_2_lattice3(B_1832, C_1835)) | ~m1_subset_1(B_1834, u1_struct_0(A_1833)) | ~l3_lattices(A_1833) | v2_struct_0(A_1833))), inference(superposition, [status(thm), theory('equality')], [c_1286, c_38])).
% 19.00/8.99  tff(c_25921, plain, (![B_1838, A_1839, B_1840, C_1841]: (r4_lattice3(B_1838, '#skF_1'(A_1839, B_1840, a_2_2_lattice3(B_1838, C_1841)), C_1841) | ~l3_lattices(B_1838) | ~v4_lattice3(B_1838) | ~v10_lattices(B_1838) | v2_struct_0(B_1838) | r3_lattice3(A_1839, B_1840, a_2_2_lattice3(B_1838, C_1841)) | ~m1_subset_1(B_1840, u1_struct_0(A_1839)) | ~l3_lattices(A_1839) | v2_struct_0(A_1839))), inference(resolution, [status(thm)], [c_6, c_25893])).
% 19.00/8.99  tff(c_10, plain, (![A_23, D_44, B_35, C_41]: (r1_lattices(A_23, D_44, B_35) | ~r2_hidden(D_44, C_41) | ~m1_subset_1(D_44, u1_struct_0(A_23)) | ~r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.00/8.99  tff(c_2789, plain, (![A_450, B_451]: (r1_lattices(A_450, '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_451) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(A_450)) | ~r4_lattice3(A_450, B_451, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_451, u1_struct_0(A_450)) | ~l3_lattices(A_450) | v2_struct_0(A_450))), inference(resolution, [status(thm)], [c_2397, c_10])).
% 19.00/8.99  tff(c_2791, plain, (![B_451]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_451) | ~r4_lattice3('#skF_7', B_451, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_451, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2422, c_2789])).
% 19.00/8.99  tff(c_2797, plain, (![B_451]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_451) | ~r4_lattice3('#skF_7', B_451, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_451, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2791])).
% 19.00/8.99  tff(c_2798, plain, (![B_451]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_451) | ~r4_lattice3('#skF_7', B_451, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_451, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_2797])).
% 19.00/8.99  tff(c_25950, plain, (![A_1839, B_1840]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | r3_lattice3(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1840, u1_struct_0(A_1839)) | ~l3_lattices(A_1839) | v2_struct_0(A_1839))), inference(resolution, [status(thm)], [c_25921, c_2798])).
% 19.00/8.99  tff(c_25984, plain, (![A_1839, B_1840]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | r3_lattice3(A_1839, B_1840, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1840, u1_struct_0(A_1839)) | ~l3_lattices(A_1839) | v2_struct_0(A_1839))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_25950])).
% 19.00/8.99  tff(c_26218, plain, (![A_1854, B_1855]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1854, B_1855, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1854, B_1855, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3(A_1854, B_1855, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1855, u1_struct_0(A_1854)) | ~l3_lattices(A_1854) | v2_struct_0(A_1854))), inference(negUnitSimplification, [status(thm)], [c_72, c_25984])).
% 19.00/8.99  tff(c_4, plain, (![A_1, B_13, C_19]: (~r1_lattices(A_1, B_13, '#skF_1'(A_1, B_13, C_19)) | r3_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.00/8.99  tff(c_26222, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_26218, c_4])).
% 19.00/8.99  tff(c_26225, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_26222])).
% 19.00/8.99  tff(c_26226, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_26225])).
% 19.00/8.99  tff(c_26227, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_26226])).
% 19.00/8.99  tff(c_26230, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8, c_26227])).
% 19.00/8.99  tff(c_26233, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_26230])).
% 19.00/8.99  tff(c_26234, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_26233])).
% 19.00/8.99  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.00/8.99  tff(c_128, plain, (![A_128, B_129, C_130]: (r2_hidden('#skF_2'(A_128, B_129, C_130), C_130) | r4_lattice3(A_128, B_129, C_130) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l3_lattices(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.00/8.99  tff(c_728, plain, (![A_266, B_267, B_268, C_269]: ('#skF_4'('#skF_2'(A_266, B_267, a_2_1_lattice3(B_268, C_269)), B_268, C_269)='#skF_2'(A_266, B_267, a_2_1_lattice3(B_268, C_269)) | ~l3_lattices(B_268) | v2_struct_0(B_268) | r4_lattice3(A_266, B_267, a_2_1_lattice3(B_268, C_269)) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l3_lattices(A_266) | v2_struct_0(A_266))), inference(resolution, [status(thm)], [c_128, c_32])).
% 19.00/8.99  tff(c_739, plain, (![A_266, B_267]: (r1_lattices('#skF_7', '#skF_2'(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | r4_lattice3(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l3_lattices(A_266) | v2_struct_0(A_266))), inference(superposition, [status(thm), theory('equality')], [c_728, c_238])).
% 19.00/8.99  tff(c_758, plain, (![A_266, B_267]: (r1_lattices('#skF_7', '#skF_2'(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7') | r4_lattice3(A_266, B_267, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l3_lattices(A_266) | v2_struct_0(A_266))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_739])).
% 19.00/8.99  tff(c_881, plain, (![A_282, B_283]: (r1_lattices('#skF_7', '#skF_2'(A_282, B_283, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_282, B_283, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | r4_lattice3(A_282, B_283, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_283, u1_struct_0(A_282)) | ~l3_lattices(A_282) | v2_struct_0(A_282))), inference(negUnitSimplification, [status(thm)], [c_72, c_758])).
% 19.00/8.99  tff(c_907, plain, (![A_286, B_287]: (r1_lattices('#skF_7', '#skF_2'(A_286, B_287, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | r4_lattice3(A_286, B_287, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_287, u1_struct_0(A_286)) | ~l3_lattices(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_14, c_881])).
% 19.00/8.99  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.00/8.99  tff(c_911, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_907, c_12])).
% 19.00/8.99  tff(c_914, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_911])).
% 19.00/8.99  tff(c_915, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_914])).
% 19.00/8.99  tff(c_20, plain, (![A_45, B_52, C_53]: (r4_lattice3(A_45, '#skF_3'(A_45, B_52, C_53), B_52) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.00/8.99  tff(c_22, plain, (![A_45, B_52, C_53]: (m1_subset_1('#skF_3'(A_45, B_52, C_53), u1_struct_0(A_45)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.00/8.99  tff(c_36, plain, (![D_68, B_64, C_65]: (r2_hidden(D_68, a_2_2_lattice3(B_64, C_65)) | ~r4_lattice3(B_64, D_68, C_65) | ~m1_subset_1(D_68, u1_struct_0(B_64)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_381, plain, (![A_216, B_217, C_218]: (r4_lattice3(A_216, '#skF_3'(A_216, B_217, C_218), B_217) | k15_lattice3(A_216, B_217)=C_218 | ~r4_lattice3(A_216, C_218, B_217) | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~v4_lattice3(A_216) | ~v10_lattices(A_216) | ~l3_lattices(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.00/8.99  tff(c_149, plain, (![D_153, B_154, C_155]: (r2_hidden(D_153, a_2_2_lattice3(B_154, C_155)) | ~r4_lattice3(B_154, D_153, C_155) | ~m1_subset_1(D_153, u1_struct_0(B_154)) | ~l3_lattices(B_154) | ~v4_lattice3(B_154) | ~v10_lattices(B_154) | v2_struct_0(B_154))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_40, plain, (![A_63, B_64, C_65]: ('#skF_5'(A_63, B_64, C_65)=A_63 | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_153, plain, (![D_153, B_154, C_155]: ('#skF_5'(D_153, B_154, C_155)=D_153 | ~r4_lattice3(B_154, D_153, C_155) | ~m1_subset_1(D_153, u1_struct_0(B_154)) | ~l3_lattices(B_154) | ~v4_lattice3(B_154) | ~v10_lattices(B_154) | v2_struct_0(B_154))), inference(resolution, [status(thm)], [c_149, c_40])).
% 19.00/8.99  tff(c_2564, plain, (![A_436, B_437, C_438]: ('#skF_5'('#skF_3'(A_436, B_437, C_438), A_436, B_437)='#skF_3'(A_436, B_437, C_438) | ~m1_subset_1('#skF_3'(A_436, B_437, C_438), u1_struct_0(A_436)) | k15_lattice3(A_436, B_437)=C_438 | ~r4_lattice3(A_436, C_438, B_437) | ~m1_subset_1(C_438, u1_struct_0(A_436)) | ~v4_lattice3(A_436) | ~v10_lattices(A_436) | ~l3_lattices(A_436) | v2_struct_0(A_436))), inference(resolution, [status(thm)], [c_381, c_153])).
% 19.00/8.99  tff(c_3064, plain, (![A_471, B_472, C_473]: ('#skF_5'('#skF_3'(A_471, B_472, C_473), A_471, B_472)='#skF_3'(A_471, B_472, C_473) | k15_lattice3(A_471, B_472)=C_473 | ~r4_lattice3(A_471, C_473, B_472) | ~m1_subset_1(C_473, u1_struct_0(A_471)) | ~v4_lattice3(A_471) | ~v10_lattices(A_471) | ~l3_lattices(A_471) | v2_struct_0(A_471))), inference(resolution, [status(thm)], [c_22, c_2564])).
% 19.00/8.99  tff(c_3082, plain, (![B_472]: ('#skF_5'('#skF_3'('#skF_7', B_472, '#skF_8'), '#skF_7', B_472)='#skF_3'('#skF_7', B_472, '#skF_8') | k15_lattice3('#skF_7', B_472)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_472) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_3064])).
% 19.00/8.99  tff(c_3096, plain, (![B_472]: ('#skF_5'('#skF_3'('#skF_7', B_472, '#skF_8'), '#skF_7', B_472)='#skF_3'('#skF_7', B_472, '#skF_8') | k15_lattice3('#skF_7', B_472)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_472) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_3082])).
% 19.00/8.99  tff(c_3097, plain, (![B_472]: ('#skF_5'('#skF_3'('#skF_7', B_472, '#skF_8'), '#skF_7', B_472)='#skF_3'('#skF_7', B_472, '#skF_8') | k15_lattice3('#skF_7', B_472)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_472))), inference(negUnitSimplification, [status(thm)], [c_72, c_3096])).
% 19.00/8.99  tff(c_2418, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2397, c_32])).
% 19.00/8.99  tff(c_2431, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2418])).
% 19.00/8.99  tff(c_2432, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_2431])).
% 19.00/8.99  tff(c_2514, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2432, c_30])).
% 19.00/8.99  tff(c_2544, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2397, c_2514])).
% 19.00/8.99  tff(c_2545, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_2544])).
% 19.00/8.99  tff(c_2192, plain, (![A_69, B_81, C_87]: ('#skF_4'('#skF_6'(A_69, B_81, C_87), A_69, C_87)='#skF_6'(A_69, B_81, C_87) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_52, c_2189])).
% 19.00/8.99  tff(c_2434, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2422, c_2192])).
% 19.00/8.99  tff(c_2455, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2434])).
% 19.00/8.99  tff(c_3298, plain, (![C_486]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_486), '#skF_7', C_486)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_486) | k16_lattice3('#skF_7', C_486)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_486))), inference(negUnitSimplification, [status(thm)], [c_72, c_2455])).
% 19.00/8.99  tff(c_3328, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3298, c_238])).
% 19.00/8.99  tff(c_3349, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2545, c_3328])).
% 19.00/8.99  tff(c_3357, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_3349])).
% 19.00/8.99  tff(c_3360, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3357])).
% 19.00/8.99  tff(c_3363, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3360])).
% 19.00/8.99  tff(c_3364, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3363])).
% 19.00/8.99  tff(c_3365, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_3364])).
% 19.00/8.99  tff(c_3368, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_3365])).
% 19.00/8.99  tff(c_3371, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2422, c_2545, c_3368])).
% 19.00/8.99  tff(c_3372, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_3371])).
% 19.00/8.99  tff(c_3385, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3372, c_58])).
% 19.00/8.99  tff(c_6926, plain, (![B_798, A_799, B_800, C_801]: (r4_lattice3(B_798, '#skF_1'(A_799, B_800, a_2_2_lattice3(B_798, C_801)), C_801) | ~r2_hidden('#skF_1'(A_799, B_800, a_2_2_lattice3(B_798, C_801)), a_2_2_lattice3(B_798, C_801)) | ~l3_lattices(B_798) | ~v4_lattice3(B_798) | ~v10_lattices(B_798) | v2_struct_0(B_798) | ~l3_lattices(B_798) | ~v4_lattice3(B_798) | ~v10_lattices(B_798) | v2_struct_0(B_798) | r3_lattice3(A_799, B_800, a_2_2_lattice3(B_798, C_801)) | ~m1_subset_1(B_800, u1_struct_0(A_799)) | ~l3_lattices(A_799) | v2_struct_0(A_799))), inference(superposition, [status(thm), theory('equality')], [c_1286, c_38])).
% 19.00/8.99  tff(c_6937, plain, (![B_802, A_803, B_804, C_805]: (r4_lattice3(B_802, '#skF_1'(A_803, B_804, a_2_2_lattice3(B_802, C_805)), C_805) | ~l3_lattices(B_802) | ~v4_lattice3(B_802) | ~v10_lattices(B_802) | v2_struct_0(B_802) | r3_lattice3(A_803, B_804, a_2_2_lattice3(B_802, C_805)) | ~m1_subset_1(B_804, u1_struct_0(A_803)) | ~l3_lattices(A_803) | v2_struct_0(A_803))), inference(resolution, [status(thm)], [c_6, c_6926])).
% 19.00/8.99  tff(c_6962, plain, (![A_803, B_804]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | r3_lattice3(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_804, u1_struct_0(A_803)) | ~l3_lattices(A_803) | v2_struct_0(A_803))), inference(resolution, [status(thm)], [c_6937, c_2798])).
% 19.00/8.99  tff(c_6992, plain, (![A_803, B_804]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | r3_lattice3(A_803, B_804, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_804, u1_struct_0(A_803)) | ~l3_lattices(A_803) | v2_struct_0(A_803))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_6962])).
% 19.00/8.99  tff(c_7126, plain, (![A_809, B_810]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_809, B_810, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_809, B_810, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3(A_809, B_810, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_810, u1_struct_0(A_809)) | ~l3_lattices(A_809) | v2_struct_0(A_809))), inference(negUnitSimplification, [status(thm)], [c_72, c_6992])).
% 19.00/8.99  tff(c_7130, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_7126, c_4])).
% 19.00/8.99  tff(c_7133, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_7130])).
% 19.00/8.99  tff(c_7134, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_7133])).
% 19.00/8.99  tff(c_7135, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_7134])).
% 19.00/8.99  tff(c_7138, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8, c_7135])).
% 19.00/8.99  tff(c_7141, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_7138])).
% 19.00/8.99  tff(c_7142, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_7141])).
% 19.00/8.99  tff(c_3098, plain, (![B_474]: ('#skF_5'('#skF_3'('#skF_7', B_474, '#skF_8'), '#skF_7', B_474)='#skF_3'('#skF_7', B_474, '#skF_8') | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(negUnitSimplification, [status(thm)], [c_72, c_3096])).
% 19.00/8.99  tff(c_2803, plain, (![B_452]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_452) | ~r4_lattice3('#skF_7', B_452, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_452, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_2797])).
% 19.00/8.99  tff(c_2814, plain, (![A_63]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_2803])).
% 19.00/8.99  tff(c_2824, plain, (![A_63]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2814])).
% 19.00/8.99  tff(c_2825, plain, (![A_63]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_2824])).
% 19.00/8.99  tff(c_3105, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3098, c_2825])).
% 19.00/8.99  tff(c_3147, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_3105])).
% 19.00/8.99  tff(c_8237, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_8240, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_8237])).
% 19.00/8.99  tff(c_8243, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_8240])).
% 19.00/8.99  tff(c_8244, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_8243])).
% 19.00/8.99  tff(c_8245, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_8244])).
% 19.00/8.99  tff(c_8248, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_8245])).
% 19.00/8.99  tff(c_8251, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_8248])).
% 19.00/8.99  tff(c_8252, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_8251])).
% 19.00/8.99  tff(c_54, plain, (![A_91, B_93]: (k16_lattice3(A_91, a_2_2_lattice3(A_91, B_93))=k15_lattice3(A_91, B_93) | ~l3_lattices(A_91) | ~v4_lattice3(A_91) | ~v10_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_157])).
% 19.00/8.99  tff(c_158, plain, (![A_159, B_160, C_161]: (r3_lattices(A_159, B_160, k16_lattice3(A_159, C_161)) | ~r3_lattice3(A_159, B_160, C_161) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l3_lattices(A_159) | ~v4_lattice3(A_159) | ~v10_lattices(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_174])).
% 19.00/8.99  tff(c_161, plain, (![A_91, B_160, B_93]: (r3_lattices(A_91, B_160, k15_lattice3(A_91, B_93)) | ~r3_lattice3(A_91, B_160, a_2_2_lattice3(A_91, B_93)) | ~m1_subset_1(B_160, u1_struct_0(A_91)) | ~l3_lattices(A_91) | ~v4_lattice3(A_91) | ~v10_lattices(A_91) | v2_struct_0(A_91) | ~l3_lattices(A_91) | ~v4_lattice3(A_91) | ~v10_lattices(A_91) | v2_struct_0(A_91))), inference(superposition, [status(thm), theory('equality')], [c_54, c_158])).
% 19.00/8.99  tff(c_8331, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8252, c_161])).
% 19.00/8.99  tff(c_8364, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_8331])).
% 19.00/8.99  tff(c_8603, plain, (![B_904]: (r3_lattices('#skF_7', B_904, '#skF_8') | ~r3_lattice3('#skF_7', B_904, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_904, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_8364])).
% 19.00/8.99  tff(c_8609, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_7142, c_8603])).
% 19.00/8.99  tff(c_8643, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_8609])).
% 19.00/8.99  tff(c_48, plain, (![A_69, B_81, C_87]: (~r3_lattices(A_69, '#skF_6'(A_69, B_81, C_87), B_81) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.00/8.99  tff(c_8674, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8643, c_48])).
% 19.00/8.99  tff(c_8677, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_8674])).
% 19.00/8.99  tff(c_8679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_8677])).
% 19.00/8.99  tff(c_8680, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_8244])).
% 19.00/8.99  tff(c_8782, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_8680])).
% 19.00/8.99  tff(c_8785, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_8782])).
% 19.00/8.99  tff(c_8786, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_8785])).
% 19.00/8.99  tff(c_8823, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8786, c_161])).
% 19.00/8.99  tff(c_8856, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_8823])).
% 19.00/8.99  tff(c_9095, plain, (![B_912]: (r3_lattices('#skF_7', B_912, '#skF_8') | ~r3_lattice3('#skF_7', B_912, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_912, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_8856])).
% 19.00/8.99  tff(c_9101, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_7142, c_9095])).
% 19.00/8.99  tff(c_9135, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_9101])).
% 19.00/8.99  tff(c_9183, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9135, c_48])).
% 19.00/8.99  tff(c_9186, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_9183])).
% 19.00/8.99  tff(c_9188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_9186])).
% 19.00/8.99  tff(c_9190, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_9211, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9190, c_40])).
% 19.00/8.99  tff(c_9232, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_9211])).
% 19.00/8.99  tff(c_9233, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_9232])).
% 19.00/8.99  tff(c_42, plain, (![A_63, B_64, C_65]: (m1_subset_1('#skF_5'(A_63, B_64, C_65), u1_struct_0(B_64)) | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.00/8.99  tff(c_239, plain, (![A_173, D_174, B_175, C_176]: (r1_lattices(A_173, D_174, B_175) | ~r2_hidden(D_174, C_176) | ~m1_subset_1(D_174, u1_struct_0(A_173)) | ~r4_lattice3(A_173, B_175, C_176) | ~m1_subset_1(B_175, u1_struct_0(A_173)) | ~l3_lattices(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.00/8.99  tff(c_764, plain, (![B_270, A_271, C_274, D_272, B_273]: (r1_lattices(A_271, D_272, B_273) | ~m1_subset_1(D_272, u1_struct_0(A_271)) | ~r4_lattice3(A_271, B_273, a_2_1_lattice3(B_270, C_274)) | ~m1_subset_1(B_273, u1_struct_0(A_271)) | ~l3_lattices(A_271) | v2_struct_0(A_271) | ~r3_lattice3(B_270, D_272, C_274) | ~m1_subset_1(D_272, u1_struct_0(B_270)) | ~l3_lattices(B_270) | v2_struct_0(B_270))), inference(resolution, [status(thm)], [c_28, c_239])).
% 19.00/8.99  tff(c_778, plain, (![B_273, B_270, C_274]: (r1_lattices('#skF_7', '#skF_8', B_273) | ~r4_lattice3('#skF_7', B_273, a_2_1_lattice3(B_270, C_274)) | ~m1_subset_1(B_273, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r3_lattice3(B_270, '#skF_8', C_274) | ~m1_subset_1('#skF_8', u1_struct_0(B_270)) | ~l3_lattices(B_270) | v2_struct_0(B_270))), inference(resolution, [status(thm)], [c_64, c_764])).
% 19.00/8.99  tff(c_787, plain, (![B_273, B_270, C_274]: (r1_lattices('#skF_7', '#skF_8', B_273) | ~r4_lattice3('#skF_7', B_273, a_2_1_lattice3(B_270, C_274)) | ~m1_subset_1(B_273, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~r3_lattice3(B_270, '#skF_8', C_274) | ~m1_subset_1('#skF_8', u1_struct_0(B_270)) | ~l3_lattices(B_270) | v2_struct_0(B_270))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_778])).
% 19.00/8.99  tff(c_789, plain, (![B_275, B_276, C_277]: (r1_lattices('#skF_7', '#skF_8', B_275) | ~r4_lattice3('#skF_7', B_275, a_2_1_lattice3(B_276, C_277)) | ~m1_subset_1(B_275, u1_struct_0('#skF_7')) | ~r3_lattice3(B_276, '#skF_8', C_277) | ~m1_subset_1('#skF_8', u1_struct_0(B_276)) | ~l3_lattices(B_276) | v2_struct_0(B_276))), inference(negUnitSimplification, [status(thm)], [c_72, c_787])).
% 19.00/8.99  tff(c_797, plain, (![A_63, B_276, C_277]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_276, C_277))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_276, C_277)), u1_struct_0('#skF_7')) | ~r3_lattice3(B_276, '#skF_8', C_277) | ~m1_subset_1('#skF_8', u1_struct_0(B_276)) | ~l3_lattices(B_276) | v2_struct_0(B_276) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_276, C_277))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_789])).
% 19.00/8.99  tff(c_804, plain, (![A_63, B_276, C_277]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_276, C_277))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_276, C_277)), u1_struct_0('#skF_7')) | ~r3_lattice3(B_276, '#skF_8', C_277) | ~m1_subset_1('#skF_8', u1_struct_0(B_276)) | ~l3_lattices(B_276) | v2_struct_0(B_276) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_276, C_277))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_797])).
% 19.00/8.99  tff(c_1434, plain, (![A_339, B_340, C_341]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_339, '#skF_7', a_2_1_lattice3(B_340, C_341))) | ~m1_subset_1('#skF_5'(A_339, '#skF_7', a_2_1_lattice3(B_340, C_341)), u1_struct_0('#skF_7')) | ~r3_lattice3(B_340, '#skF_8', C_341) | ~m1_subset_1('#skF_8', u1_struct_0(B_340)) | ~l3_lattices(B_340) | v2_struct_0(B_340) | ~r2_hidden(A_339, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_340, C_341))))), inference(negUnitSimplification, [status(thm)], [c_72, c_804])).
% 19.00/8.99  tff(c_1453, plain, (![A_63, B_340, C_341]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_340, C_341))) | ~r3_lattice3(B_340, '#skF_8', C_341) | ~m1_subset_1('#skF_8', u1_struct_0(B_340)) | ~l3_lattices(B_340) | v2_struct_0(B_340) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_340, C_341))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1434])).
% 19.00/8.99  tff(c_1465, plain, (![A_63, B_340, C_341]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_340, C_341))) | ~r3_lattice3(B_340, '#skF_8', C_341) | ~m1_subset_1('#skF_8', u1_struct_0(B_340)) | ~l3_lattices(B_340) | v2_struct_0(B_340) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_340, C_341))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1453])).
% 19.00/8.99  tff(c_1466, plain, (![A_63, B_340, C_341]: (r1_lattices('#skF_7', '#skF_8', '#skF_5'(A_63, '#skF_7', a_2_1_lattice3(B_340, C_341))) | ~r3_lattice3(B_340, '#skF_8', C_341) | ~m1_subset_1('#skF_8', u1_struct_0(B_340)) | ~l3_lattices(B_340) | v2_struct_0(B_340) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3(B_340, C_341))))), inference(negUnitSimplification, [status(thm)], [c_72, c_1465])).
% 19.00/8.99  tff(c_9276, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_9233, c_1466])).
% 19.00/8.99  tff(c_9327, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9190, c_66, c_64, c_60, c_9276])).
% 19.00/8.99  tff(c_9328, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_9327])).
% 19.00/8.99  tff(c_18, plain, (![A_45, C_53, B_52]: (~r1_lattices(A_45, C_53, '#skF_3'(A_45, B_52, C_53)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.00/8.99  tff(c_9345, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9328, c_18])).
% 19.00/8.99  tff(c_9348, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_9345])).
% 19.00/8.99  tff(c_9349, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_9348])).
% 19.00/8.99  tff(c_9386, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9349, c_161])).
% 19.00/8.99  tff(c_9419, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_9386])).
% 19.00/8.99  tff(c_9783, plain, (![B_926]: (r3_lattices('#skF_7', B_926, '#skF_8') | ~r3_lattice3('#skF_7', B_926, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_926, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_9419])).
% 19.00/8.99  tff(c_9789, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_7142, c_9783])).
% 19.00/8.99  tff(c_9823, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_9789])).
% 19.00/8.99  tff(c_9902, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9823, c_48])).
% 19.00/8.99  tff(c_9905, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_9902])).
% 19.00/8.99  tff(c_9907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_9905])).
% 19.00/8.99  tff(c_9908, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_7134])).
% 19.00/8.99  tff(c_11034, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_11037, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_11034])).
% 19.00/8.99  tff(c_11040, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_11037])).
% 19.00/8.99  tff(c_11041, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_11040])).
% 19.00/8.99  tff(c_11042, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_11041])).
% 19.00/8.99  tff(c_11045, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_11042])).
% 19.00/8.99  tff(c_11048, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_11045])).
% 19.00/8.99  tff(c_11049, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_11048])).
% 19.00/8.99  tff(c_11086, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_11049, c_161])).
% 19.00/8.99  tff(c_11119, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_11086])).
% 19.00/8.99  tff(c_11394, plain, (![B_1023]: (r3_lattices('#skF_7', B_1023, '#skF_8') | ~r3_lattice3('#skF_7', B_1023, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1023, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_11119])).
% 19.00/8.99  tff(c_11400, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_9908, c_11394])).
% 19.00/8.99  tff(c_11434, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_11400])).
% 19.00/8.99  tff(c_11465, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_11434, c_48])).
% 19.00/8.99  tff(c_11468, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_11465])).
% 19.00/8.99  tff(c_11470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_11468])).
% 19.00/8.99  tff(c_11471, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_11041])).
% 19.00/8.99  tff(c_11573, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_11471])).
% 19.00/8.99  tff(c_11576, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_11573])).
% 19.00/8.99  tff(c_11577, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_11576])).
% 19.00/8.99  tff(c_11614, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_11577, c_161])).
% 19.00/8.99  tff(c_11647, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_11614])).
% 19.00/8.99  tff(c_11880, plain, (![B_1031]: (r3_lattices('#skF_7', B_1031, '#skF_8') | ~r3_lattice3('#skF_7', B_1031, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1031, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_11647])).
% 19.00/8.99  tff(c_11886, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_9908, c_11880])).
% 19.00/8.99  tff(c_11920, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_11886])).
% 19.00/8.99  tff(c_11999, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_11920, c_48])).
% 19.00/8.99  tff(c_12002, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_11999])).
% 19.00/8.99  tff(c_12004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_12002])).
% 19.00/8.99  tff(c_12006, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_3138, plain, (![B_474]: (m1_subset_1('#skF_3'('#skF_7', B_474, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(superposition, [status(thm), theory('equality')], [c_3098, c_42])).
% 19.00/8.99  tff(c_3155, plain, (![B_474]: (m1_subset_1('#skF_3'('#skF_7', B_474, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3138])).
% 19.00/8.99  tff(c_3156, plain, (![B_474]: (m1_subset_1('#skF_3'('#skF_7', B_474, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(negUnitSimplification, [status(thm)], [c_72, c_3155])).
% 19.00/8.99  tff(c_12018, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_12006, c_3156])).
% 19.00/8.99  tff(c_12039, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_12018])).
% 19.00/8.99  tff(c_12050, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(splitLeft, [status(thm)], [c_12039])).
% 19.00/8.99  tff(c_12196, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12050, c_161])).
% 19.00/8.99  tff(c_12229, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_12196])).
% 19.00/8.99  tff(c_12624, plain, (![B_1045]: (r3_lattices('#skF_7', B_1045, '#skF_8') | ~r3_lattice3('#skF_7', B_1045, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1045, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_12229])).
% 19.00/8.99  tff(c_12630, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_9908, c_12624])).
% 19.00/8.99  tff(c_12664, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_12630])).
% 19.00/8.99  tff(c_12695, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_12664, c_48])).
% 19.00/8.99  tff(c_12698, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_3372, c_12695])).
% 19.00/8.99  tff(c_12700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3385, c_12698])).
% 19.00/8.99  tff(c_12702, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))!='#skF_8'), inference(splitRight, [status(thm)], [c_12039])).
% 19.00/8.99  tff(c_12027, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_12006, c_40])).
% 19.00/8.99  tff(c_12048, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_12027])).
% 19.00/8.99  tff(c_12049, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_12048])).
% 19.00/8.99  tff(c_12843, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_12049, c_1466])).
% 19.00/8.99  tff(c_12897, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12006, c_66, c_64, c_60, c_12843])).
% 19.00/8.99  tff(c_12898, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_12897])).
% 19.00/8.99  tff(c_12916, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_12898, c_18])).
% 19.00/8.99  tff(c_12919, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_12916])).
% 19.00/8.99  tff(c_12921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12702, c_12919])).
% 19.00/8.99  tff(c_12922, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_3364])).
% 19.00/8.99  tff(c_12982, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_12922])).
% 19.00/8.99  tff(c_12985, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2422, c_2545, c_12982])).
% 19.00/8.99  tff(c_12986, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_12985])).
% 19.00/8.99  tff(c_12988, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12986, c_58])).
% 19.00/8.99  tff(c_15571, plain, (![A_1291, B_1292, B_1293, C_1294]: (m1_subset_1('#skF_1'(A_1291, B_1292, a_2_2_lattice3(B_1293, C_1294)), u1_struct_0(B_1293)) | ~r2_hidden('#skF_1'(A_1291, B_1292, a_2_2_lattice3(B_1293, C_1294)), a_2_2_lattice3(B_1293, C_1294)) | ~l3_lattices(B_1293) | ~v4_lattice3(B_1293) | ~v10_lattices(B_1293) | v2_struct_0(B_1293) | ~l3_lattices(B_1293) | ~v4_lattice3(B_1293) | ~v10_lattices(B_1293) | v2_struct_0(B_1293) | r3_lattice3(A_1291, B_1292, a_2_2_lattice3(B_1293, C_1294)) | ~m1_subset_1(B_1292, u1_struct_0(A_1291)) | ~l3_lattices(A_1291) | v2_struct_0(A_1291))), inference(superposition, [status(thm), theory('equality')], [c_1286, c_42])).
% 19.00/8.99  tff(c_15581, plain, (![A_1, B_13, B_1293, C_1294]: (m1_subset_1('#skF_1'(A_1, B_13, a_2_2_lattice3(B_1293, C_1294)), u1_struct_0(B_1293)) | ~l3_lattices(B_1293) | ~v4_lattice3(B_1293) | ~v10_lattices(B_1293) | v2_struct_0(B_1293) | r3_lattice3(A_1, B_13, a_2_2_lattice3(B_1293, C_1294)) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(resolution, [status(thm)], [c_6, c_15571])).
% 19.00/8.99  tff(c_16755, plain, (![B_1383, A_1384, B_1385, C_1386]: (r4_lattice3(B_1383, '#skF_1'(A_1384, B_1385, a_2_2_lattice3(B_1383, C_1386)), C_1386) | ~r2_hidden('#skF_1'(A_1384, B_1385, a_2_2_lattice3(B_1383, C_1386)), a_2_2_lattice3(B_1383, C_1386)) | ~l3_lattices(B_1383) | ~v4_lattice3(B_1383) | ~v10_lattices(B_1383) | v2_struct_0(B_1383) | ~l3_lattices(B_1383) | ~v4_lattice3(B_1383) | ~v10_lattices(B_1383) | v2_struct_0(B_1383) | r3_lattice3(A_1384, B_1385, a_2_2_lattice3(B_1383, C_1386)) | ~m1_subset_1(B_1385, u1_struct_0(A_1384)) | ~l3_lattices(A_1384) | v2_struct_0(A_1384))), inference(superposition, [status(thm), theory('equality')], [c_1286, c_38])).
% 19.00/8.99  tff(c_16766, plain, (![B_1387, A_1388, B_1389, C_1390]: (r4_lattice3(B_1387, '#skF_1'(A_1388, B_1389, a_2_2_lattice3(B_1387, C_1390)), C_1390) | ~l3_lattices(B_1387) | ~v4_lattice3(B_1387) | ~v10_lattices(B_1387) | v2_struct_0(B_1387) | r3_lattice3(A_1388, B_1389, a_2_2_lattice3(B_1387, C_1390)) | ~m1_subset_1(B_1389, u1_struct_0(A_1388)) | ~l3_lattices(A_1388) | v2_struct_0(A_1388))), inference(resolution, [status(thm)], [c_6, c_16755])).
% 19.00/8.99  tff(c_16795, plain, (![A_1388, B_1389]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | r3_lattice3(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1389, u1_struct_0(A_1388)) | ~l3_lattices(A_1388) | v2_struct_0(A_1388))), inference(resolution, [status(thm)], [c_16766, c_2798])).
% 19.00/8.99  tff(c_16829, plain, (![A_1388, B_1389]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | r3_lattice3(A_1388, B_1389, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1389, u1_struct_0(A_1388)) | ~l3_lattices(A_1388) | v2_struct_0(A_1388))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_16795])).
% 19.00/8.99  tff(c_16853, plain, (![A_1392, B_1393]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_1'(A_1392, B_1393, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1392, B_1393, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3(A_1392, B_1393, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1393, u1_struct_0(A_1392)) | ~l3_lattices(A_1392) | v2_struct_0(A_1392))), inference(negUnitSimplification, [status(thm)], [c_72, c_16829])).
% 19.00/8.99  tff(c_16857, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_16853, c_4])).
% 19.00/8.99  tff(c_16860, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_16857])).
% 19.00/8.99  tff(c_16861, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7')) | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_16860])).
% 19.00/8.99  tff(c_16862, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_16861])).
% 19.00/8.99  tff(c_16865, plain, (~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_15581, c_16862])).
% 19.00/8.99  tff(c_16871, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422, c_70, c_68, c_16865])).
% 19.00/8.99  tff(c_16872, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_16871])).
% 19.00/8.99  tff(c_18427, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_18430, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_18427])).
% 19.00/8.99  tff(c_18433, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_18430])).
% 19.00/8.99  tff(c_18434, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_18433])).
% 19.00/8.99  tff(c_18435, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_18434])).
% 19.00/8.99  tff(c_18438, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_18435])).
% 19.00/8.99  tff(c_18441, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_18438])).
% 19.00/8.99  tff(c_18442, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_18441])).
% 19.00/8.99  tff(c_18496, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_18442, c_161])).
% 19.00/8.99  tff(c_18529, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_18496])).
% 19.00/8.99  tff(c_18768, plain, (![B_1477]: (r3_lattices('#skF_7', B_1477, '#skF_8') | ~r3_lattice3('#skF_7', B_1477, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1477, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_18529])).
% 19.00/8.99  tff(c_18774, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_16872, c_18768])).
% 19.00/8.99  tff(c_18808, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_18774])).
% 19.00/8.99  tff(c_18839, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_18808, c_48])).
% 19.00/8.99  tff(c_18842, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_18839])).
% 19.00/8.99  tff(c_18844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_18842])).
% 19.00/8.99  tff(c_18845, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_18434])).
% 19.00/8.99  tff(c_18922, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_18845])).
% 19.00/8.99  tff(c_18925, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_18922])).
% 19.00/8.99  tff(c_18926, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_18925])).
% 19.00/8.99  tff(c_18963, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_18926, c_161])).
% 19.00/8.99  tff(c_18996, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_18963])).
% 19.00/8.99  tff(c_19235, plain, (![B_1485]: (r3_lattices('#skF_7', B_1485, '#skF_8') | ~r3_lattice3('#skF_7', B_1485, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1485, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_18996])).
% 19.00/8.99  tff(c_19241, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_16872, c_19235])).
% 19.00/8.99  tff(c_19275, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_19241])).
% 19.00/8.99  tff(c_19354, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_19275, c_48])).
% 19.00/8.99  tff(c_19357, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_19354])).
% 19.00/8.99  tff(c_19359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_19357])).
% 19.00/8.99  tff(c_19361, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_19382, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_19361, c_40])).
% 19.00/8.99  tff(c_19403, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_19382])).
% 19.00/8.99  tff(c_19404, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_19403])).
% 19.00/8.99  tff(c_19447, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_19404, c_1466])).
% 19.00/8.99  tff(c_19498, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_19361, c_66, c_64, c_60, c_19447])).
% 19.00/8.99  tff(c_19499, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_19498])).
% 19.00/8.99  tff(c_19516, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_19499, c_18])).
% 19.00/8.99  tff(c_19519, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_19516])).
% 19.00/8.99  tff(c_19520, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_19519])).
% 19.00/8.99  tff(c_19557, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_19520, c_161])).
% 19.00/8.99  tff(c_19590, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_19557])).
% 19.00/8.99  tff(c_19966, plain, (![B_1499]: (r3_lattices('#skF_7', B_1499, '#skF_8') | ~r3_lattice3('#skF_7', B_1499, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1499, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_19590])).
% 19.00/8.99  tff(c_19972, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_16872, c_19966])).
% 19.00/8.99  tff(c_20006, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_19972])).
% 19.00/8.99  tff(c_20054, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20006, c_48])).
% 19.00/8.99  tff(c_20057, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_20054])).
% 19.00/8.99  tff(c_20059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_20057])).
% 19.00/8.99  tff(c_20060, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_16861])).
% 19.00/8.99  tff(c_21606, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_21609, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_21606])).
% 19.00/8.99  tff(c_21612, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_21609])).
% 19.00/8.99  tff(c_21613, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_21612])).
% 19.00/8.99  tff(c_21614, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_21613])).
% 19.00/8.99  tff(c_21658, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_21614])).
% 19.00/8.99  tff(c_21661, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_21658])).
% 19.00/8.99  tff(c_21662, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_21661])).
% 19.00/8.99  tff(c_21699, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_21662, c_161])).
% 19.00/8.99  tff(c_21732, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_21699])).
% 19.00/8.99  tff(c_22013, plain, (![B_1586]: (r3_lattices('#skF_7', B_1586, '#skF_8') | ~r3_lattice3('#skF_7', B_1586, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1586, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_21732])).
% 19.00/8.99  tff(c_22019, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_20060, c_22013])).
% 19.00/8.99  tff(c_22053, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_22019])).
% 19.00/8.99  tff(c_22084, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22053, c_48])).
% 19.00/8.99  tff(c_22087, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_22084])).
% 19.00/8.99  tff(c_22089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_22087])).
% 19.00/8.99  tff(c_22090, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_21613])).
% 19.00/8.99  tff(c_22150, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_22090])).
% 19.00/8.99  tff(c_22153, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_22150])).
% 19.00/8.99  tff(c_22154, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_22153])).
% 19.00/8.99  tff(c_22191, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_22154, c_161])).
% 19.00/8.99  tff(c_22224, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_22191])).
% 19.00/8.99  tff(c_22505, plain, (![B_1594]: (r3_lattices('#skF_7', B_1594, '#skF_8') | ~r3_lattice3('#skF_7', B_1594, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1594, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_22224])).
% 19.00/8.99  tff(c_22511, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_20060, c_22505])).
% 19.00/8.99  tff(c_22545, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_22511])).
% 19.00/8.99  tff(c_22576, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22545, c_48])).
% 19.00/8.99  tff(c_22579, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_22576])).
% 19.00/8.99  tff(c_22581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_22579])).
% 19.00/8.99  tff(c_22583, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_3147])).
% 19.00/8.99  tff(c_22595, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_22583, c_3156])).
% 19.00/8.99  tff(c_22616, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_22595])).
% 19.00/8.99  tff(c_22627, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(splitLeft, [status(thm)], [c_22616])).
% 19.00/8.99  tff(c_22706, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_22627, c_161])).
% 19.00/8.99  tff(c_22739, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_22706])).
% 19.00/8.99  tff(c_22978, plain, (![B_1602]: (r3_lattices('#skF_7', B_1602, '#skF_8') | ~r3_lattice3('#skF_7', B_1602, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_1602, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_22739])).
% 19.00/8.99  tff(c_22984, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_20060, c_22978])).
% 19.00/8.99  tff(c_23018, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_22984])).
% 19.00/8.99  tff(c_23049, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_23018, c_48])).
% 19.00/8.99  tff(c_23052, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_12986, c_23049])).
% 19.00/8.99  tff(c_23054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_12988, c_23052])).
% 19.00/8.99  tff(c_23056, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))!='#skF_8'), inference(splitRight, [status(thm)], [c_22616])).
% 19.00/8.99  tff(c_22604, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22583, c_40])).
% 19.00/8.99  tff(c_22625, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_22604])).
% 19.00/8.99  tff(c_22626, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_22625])).
% 19.00/8.99  tff(c_23197, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_22626, c_1466])).
% 19.00/8.99  tff(c_23251, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22583, c_66, c_64, c_60, c_23197])).
% 19.00/8.99  tff(c_23252, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_23251])).
% 19.00/8.99  tff(c_23270, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_23252, c_18])).
% 19.00/8.99  tff(c_23273, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_23270])).
% 19.00/8.99  tff(c_23275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_23056, c_23273])).
% 19.00/8.99  tff(c_23277, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_3349])).
% 19.00/8.99  tff(c_23286, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_23277, c_32])).
% 19.00/8.99  tff(c_23295, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23286])).
% 19.00/8.99  tff(c_23296, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_23295])).
% 19.00/8.99  tff(c_23325, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_23296, c_34])).
% 19.00/8.99  tff(c_23354, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23277, c_23325])).
% 19.00/8.99  tff(c_23355, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_23354])).
% 19.00/8.99  tff(c_23328, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_23296, c_30])).
% 19.00/8.99  tff(c_23357, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23277, c_23328])).
% 19.00/8.99  tff(c_23358, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_23357])).
% 19.00/8.99  tff(c_23366, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_23355, c_2192])).
% 19.00/8.99  tff(c_23391, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_23366])).
% 19.00/8.99  tff(c_26837, plain, (![C_1930]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_1930), '#skF_7', C_1930)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_1930) | k16_lattice3('#skF_7', C_1930)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_1930))), inference(negUnitSimplification, [status(thm)], [c_72, c_23391])).
% 19.00/8.99  tff(c_26877, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_26837, c_238])).
% 19.00/8.99  tff(c_26904, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_23358, c_26877])).
% 19.00/8.99  tff(c_26912, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_26904])).
% 19.00/8.99  tff(c_26915, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_26912])).
% 19.00/8.99  tff(c_26918, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26915])).
% 19.00/8.99  tff(c_26919, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_26918])).
% 19.00/8.99  tff(c_26920, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_26919])).
% 19.00/8.99  tff(c_26923, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_26920])).
% 19.00/8.99  tff(c_26926, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_23355, c_23358, c_26923])).
% 19.00/8.99  tff(c_26927, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_26926])).
% 19.00/8.99  tff(c_23770, plain, (![A_1651, B_1652]: (r1_lattices(A_1651, '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_1652) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0(A_1651)) | ~r4_lattice3(A_1651, B_1652, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_1652, u1_struct_0(A_1651)) | ~l3_lattices(A_1651) | v2_struct_0(A_1651))), inference(resolution, [status(thm)], [c_23277, c_10])).
% 19.00/8.99  tff(c_23772, plain, (![B_1652]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_1652) | ~r4_lattice3('#skF_7', B_1652, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_1652, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_23355, c_23770])).
% 19.00/8.99  tff(c_23778, plain, (![B_1652]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_1652) | ~r4_lattice3('#skF_7', B_1652, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_1652, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23772])).
% 19.00/8.99  tff(c_23779, plain, (![B_1652]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_1652) | ~r4_lattice3('#skF_7', B_1652, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_1652, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_23778])).
% 19.00/8.99  tff(c_27549, plain, (![B_1950]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), B_1950) | ~r4_lattice3('#skF_7', B_1950, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_1950, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_26927, c_23779])).
% 19.00/8.99  tff(c_27568, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_27549])).
% 19.00/8.99  tff(c_27586, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_27568])).
% 19.00/8.99  tff(c_28069, plain, (![A_1988]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_1988, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_1988, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_1988, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_27586])).
% 19.00/8.99  tff(c_28097, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3097, c_28069])).
% 19.00/8.99  tff(c_28138, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_28097])).
% 19.00/8.99  tff(c_29042, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_28138])).
% 19.00/8.99  tff(c_29045, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_29042])).
% 19.00/8.99  tff(c_29048, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_29045])).
% 19.00/8.99  tff(c_29049, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_29048])).
% 19.00/8.99  tff(c_29050, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_29049])).
% 19.00/8.99  tff(c_29053, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_29050])).
% 19.00/8.99  tff(c_29056, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_29053])).
% 19.00/8.99  tff(c_29057, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_29056])).
% 19.00/8.99  tff(c_29098, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_29057, c_161])).
% 19.00/8.99  tff(c_29133, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_29098])).
% 19.00/8.99  tff(c_29384, plain, (![B_2082]: (r3_lattices('#skF_7', B_2082, '#skF_8') | ~r3_lattice3('#skF_7', B_2082, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2082, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_29133])).
% 19.00/8.99  tff(c_29393, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_26234, c_29384])).
% 19.00/8.99  tff(c_29430, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_29393])).
% 19.00/8.99  tff(c_29461, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_29430, c_48])).
% 19.00/8.99  tff(c_29464, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_29461])).
% 19.00/8.99  tff(c_29466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_29464])).
% 19.00/8.99  tff(c_29467, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_29049])).
% 19.00/8.99  tff(c_29532, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_29467])).
% 19.00/8.99  tff(c_29535, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_29532])).
% 19.00/8.99  tff(c_29536, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_29535])).
% 19.00/8.99  tff(c_29579, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_29536, c_161])).
% 19.00/8.99  tff(c_29617, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_29579])).
% 19.00/8.99  tff(c_29858, plain, (![B_2087]: (r3_lattices('#skF_7', B_2087, '#skF_8') | ~r3_lattice3('#skF_7', B_2087, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2087, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_29617])).
% 19.00/8.99  tff(c_29867, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_26234, c_29858])).
% 19.00/8.99  tff(c_29904, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_29867])).
% 19.00/8.99  tff(c_29940, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_29904, c_48])).
% 19.00/8.99  tff(c_29943, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_29940])).
% 19.00/8.99  tff(c_29945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_29943])).
% 19.00/8.99  tff(c_29947, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_28138])).
% 19.00/8.99  tff(c_30040, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_29947, c_3156])).
% 19.00/8.99  tff(c_30061, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_30040])).
% 19.00/8.99  tff(c_30072, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(splitLeft, [status(thm)], [c_30061])).
% 19.00/8.99  tff(c_30113, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_30072, c_161])).
% 19.00/8.99  tff(c_30148, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_30113])).
% 19.00/8.99  tff(c_30399, plain, (![B_2099]: (r3_lattices('#skF_7', B_2099, '#skF_8') | ~r3_lattice3('#skF_7', B_2099, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2099, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_30148])).
% 19.00/8.99  tff(c_30408, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_26234, c_30399])).
% 19.00/8.99  tff(c_30445, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_30408])).
% 19.00/8.99  tff(c_30476, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_30445, c_48])).
% 19.00/8.99  tff(c_30479, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_30476])).
% 19.00/8.99  tff(c_30481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_30479])).
% 19.00/8.99  tff(c_30483, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))!='#skF_8'), inference(splitRight, [status(thm)], [c_30061])).
% 19.00/8.99  tff(c_30482, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_30061])).
% 19.00/8.99  tff(c_3141, plain, (![B_474]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_474, '#skF_8'), B_474) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(superposition, [status(thm), theory('equality')], [c_3098, c_38])).
% 19.00/8.99  tff(c_3158, plain, (![B_474]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_474, '#skF_8'), B_474) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3141])).
% 19.00/8.99  tff(c_3159, plain, (![B_474]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_474, '#skF_8'), B_474) | ~r2_hidden('#skF_3'('#skF_7', B_474, '#skF_8'), a_2_2_lattice3('#skF_7', B_474)) | k15_lattice3('#skF_7', B_474)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_474))), inference(negUnitSimplification, [status(thm)], [c_72, c_3158])).
% 19.00/8.99  tff(c_30037, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_29947, c_3159])).
% 19.00/8.99  tff(c_30058, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_30037])).
% 19.00/8.99  tff(c_30545, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_30483, c_30058])).
% 19.00/8.99  tff(c_788, plain, (![B_273, B_270, C_274]: (r1_lattices('#skF_7', '#skF_8', B_273) | ~r4_lattice3('#skF_7', B_273, a_2_1_lattice3(B_270, C_274)) | ~m1_subset_1(B_273, u1_struct_0('#skF_7')) | ~r3_lattice3(B_270, '#skF_8', C_274) | ~m1_subset_1('#skF_8', u1_struct_0(B_270)) | ~l3_lattices(B_270) | v2_struct_0(B_270))), inference(negUnitSimplification, [status(thm)], [c_72, c_787])).
% 19.00/8.99  tff(c_30570, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_30545, c_788])).
% 19.00/8.99  tff(c_30613, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_30482, c_30570])).
% 19.00/8.99  tff(c_30614, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_30613])).
% 19.00/8.99  tff(c_30621, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_30614, c_18])).
% 19.00/8.99  tff(c_30624, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_30621])).
% 19.00/8.99  tff(c_30626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_30483, c_30624])).
% 19.00/8.99  tff(c_30627, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_26226])).
% 19.00/8.99  tff(c_31473, plain, (![C_2194]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_2194), '#skF_7', C_2194)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_2194) | k16_lattice3('#skF_7', C_2194)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_2194))), inference(negUnitSimplification, [status(thm)], [c_72, c_23391])).
% 19.00/8.99  tff(c_31513, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_31473, c_238])).
% 19.00/8.99  tff(c_31540, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_23358, c_31513])).
% 19.00/8.99  tff(c_31548, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_31540])).
% 19.00/8.99  tff(c_31598, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_31548])).
% 19.00/8.99  tff(c_31601, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_31598])).
% 19.00/8.99  tff(c_31602, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_31601])).
% 19.00/8.99  tff(c_31604, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_31602])).
% 19.00/8.99  tff(c_31607, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_31604])).
% 19.00/8.99  tff(c_31610, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_23355, c_23358, c_31607])).
% 19.00/8.99  tff(c_31611, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_31610])).
% 19.00/8.99  tff(c_32204, plain, (![B_2216]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), B_2216) | ~r4_lattice3('#skF_7', B_2216, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_2216, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_31611, c_23779])).
% 19.00/8.99  tff(c_32223, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_32204])).
% 19.00/8.99  tff(c_32241, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_32223])).
% 19.00/8.99  tff(c_32810, plain, (![A_2256]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_2256, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_2256, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_2256, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_32241])).
% 19.00/8.99  tff(c_32842, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3097, c_32810])).
% 19.00/8.99  tff(c_32883, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_32842])).
% 19.00/8.99  tff(c_33621, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_32883])).
% 19.00/8.99  tff(c_33624, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_33621])).
% 19.00/8.99  tff(c_33627, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_33624])).
% 19.00/8.99  tff(c_33628, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_33627])).
% 19.00/8.99  tff(c_33629, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_33628])).
% 19.00/8.99  tff(c_33713, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_33629])).
% 19.00/8.99  tff(c_33716, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_33713])).
% 19.00/8.99  tff(c_33717, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_33716])).
% 19.00/8.99  tff(c_33760, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33717, c_161])).
% 19.00/8.99  tff(c_33798, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_33760])).
% 19.00/8.99  tff(c_34048, plain, (![B_2339]: (r3_lattices('#skF_7', B_2339, '#skF_8') | ~r3_lattice3('#skF_7', B_2339, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2339, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_33798])).
% 19.00/8.99  tff(c_34057, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_30627, c_34048])).
% 19.00/8.99  tff(c_34094, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_34057])).
% 19.00/8.99  tff(c_34125, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_34094, c_48])).
% 19.00/8.99  tff(c_34128, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_34125])).
% 19.00/8.99  tff(c_34130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_34128])).
% 19.00/8.99  tff(c_34131, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_33628])).
% 19.00/8.99  tff(c_34191, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_34131])).
% 19.00/8.99  tff(c_34194, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_34191])).
% 19.00/8.99  tff(c_34195, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_34194])).
% 19.00/8.99  tff(c_34238, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34195, c_161])).
% 19.00/8.99  tff(c_34276, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_34238])).
% 19.00/8.99  tff(c_34522, plain, (![B_2345]: (r3_lattices('#skF_7', B_2345, '#skF_8') | ~r3_lattice3('#skF_7', B_2345, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2345, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_34276])).
% 19.00/8.99  tff(c_34531, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_30627, c_34522])).
% 19.00/8.99  tff(c_34568, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_34531])).
% 19.00/8.99  tff(c_34599, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_34568, c_48])).
% 19.00/8.99  tff(c_34602, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_34599])).
% 19.00/8.99  tff(c_34604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_34602])).
% 19.00/8.99  tff(c_34606, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_32883])).
% 19.00/8.99  tff(c_34623, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_34606, c_3156])).
% 19.00/8.99  tff(c_34644, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_34623])).
% 19.00/8.99  tff(c_34655, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(splitLeft, [status(thm)], [c_34644])).
% 19.00/8.99  tff(c_34698, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34655, c_161])).
% 19.00/8.99  tff(c_34736, plain, (![B_160]: (r3_lattices('#skF_7', B_160, '#skF_8') | ~r3_lattice3('#skF_7', B_160, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_160, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_70, c_68, c_66, c_34698])).
% 19.00/8.99  tff(c_34977, plain, (![B_2351]: (r3_lattices('#skF_7', B_2351, '#skF_8') | ~r3_lattice3('#skF_7', B_2351, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1(B_2351, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_34736])).
% 19.00/8.99  tff(c_34986, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_30627, c_34977])).
% 19.00/8.99  tff(c_35023, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_34986])).
% 19.00/8.99  tff(c_35059, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_35023, c_48])).
% 19.00/8.99  tff(c_35062, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_35059])).
% 19.00/8.99  tff(c_35064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_35062])).
% 19.00/8.99  tff(c_35066, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))!='#skF_8'), inference(splitRight, [status(thm)], [c_34644])).
% 19.00/8.99  tff(c_34632, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_34606, c_40])).
% 19.00/8.99  tff(c_34653, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_34632])).
% 19.00/8.99  tff(c_34654, plain, ('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_34653])).
% 19.00/8.99  tff(c_35100, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_34654, c_1466])).
% 19.00/8.99  tff(c_35143, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34606, c_66, c_64, c_60, c_35100])).
% 19.00/8.99  tff(c_35144, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_35143])).
% 19.00/8.99  tff(c_35217, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_35144, c_18])).
% 19.00/8.99  tff(c_35220, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_915, c_35217])).
% 19.00/8.99  tff(c_35222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_35066, c_35220])).
% 19.00/8.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.00/8.99  
% 19.00/8.99  Inference rules
% 19.00/8.99  ----------------------
% 19.00/8.99  #Ref     : 0
% 19.00/8.99  #Sup     : 6376
% 19.00/8.99  #Fact    : 0
% 19.00/8.99  #Define  : 0
% 19.00/8.99  #Split   : 59
% 19.00/8.99  #Chain   : 0
% 19.00/8.99  #Close   : 0
% 19.00/8.99  
% 19.00/8.99  Ordering : KBO
% 19.00/8.99  
% 19.00/8.99  Simplification rules
% 19.00/8.99  ----------------------
% 19.00/8.99  #Subsume      : 1310
% 19.00/8.99  #Demod        : 14311
% 19.00/8.99  #Tautology    : 1371
% 19.00/8.99  #SimpNegUnit  : 3168
% 19.00/8.99  #BackRed      : 85
% 19.00/8.99  
% 19.00/8.99  #Partial instantiations: 0
% 19.00/8.99  #Strategies tried      : 1
% 19.00/8.99  
% 19.00/8.99  Timing (in seconds)
% 19.00/8.99  ----------------------
% 19.00/8.99  Preprocessing        : 0.36
% 19.00/9.00  Parsing              : 0.20
% 19.00/9.00  CNF conversion       : 0.03
% 19.00/9.00  Main loop            : 7.75
% 19.00/9.00  Inferencing          : 2.43
% 19.00/9.00  Reduction            : 2.65
% 19.00/9.00  Demodulation         : 1.92
% 19.00/9.00  BG Simplification    : 0.20
% 19.00/9.00  Subsumption          : 2.05
% 19.00/9.00  Abstraction          : 0.34
% 19.00/9.00  MUC search           : 0.00
% 19.00/9.00  Cooper               : 0.00
% 19.00/9.00  Total                : 8.29
% 19.00/9.00  Index Insertion      : 0.00
% 19.00/9.00  Index Deletion       : 0.00
% 19.00/9.00  Index Matching       : 0.00
% 19.00/9.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
