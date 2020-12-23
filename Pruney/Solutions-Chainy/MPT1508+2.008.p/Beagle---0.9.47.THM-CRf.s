%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:48 EST 2020

% Result     : Theorem 9.42s
% Output     : CNFRefutation 9.70s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 579 expanded)
%              Number of leaves         :   32 ( 221 expanded)
%              Depth                    :   29
%              Number of atoms          :  504 (2711 expanded)
%              Number of equality atoms :   48 ( 303 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_173,negated_conjecture,(
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

tff(f_134,axiom,(
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

tff(f_110,axiom,(
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

tff(f_153,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    k16_lattice3('#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_60,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    r3_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_44,plain,(
    ! [A_65,B_77,C_83] :
      ( r3_lattice3(A_65,'#skF_5'(A_65,B_77,C_83),C_83)
      | k16_lattice3(A_65,C_83) = B_77
      | ~ r3_lattice3(A_65,B_77,C_83)
      | ~ m1_subset_1(B_77,u1_struct_0(A_65))
      | ~ l3_lattices(A_65)
      | ~ v4_lattice3(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    ! [A_65,B_77,C_83] :
      ( m1_subset_1('#skF_5'(A_65,B_77,C_83),u1_struct_0(A_65))
      | k16_lattice3(A_65,C_83) = B_77
      | ~ r3_lattice3(A_65,B_77,C_83)
      | ~ m1_subset_1(B_77,u1_struct_0(A_65))
      | ~ l3_lattices(A_65)
      | ~ v4_lattice3(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    ! [D_64,B_60,C_61] :
      ( r2_hidden(D_64,a_2_1_lattice3(B_60,C_61))
      | ~ r3_lattice3(B_60,D_64,C_61)
      | ~ m1_subset_1(D_64,u1_struct_0(B_60))
      | ~ l3_lattices(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_300,plain,(
    ! [A_181,B_182,C_183] :
      ( r3_lattice3(A_181,'#skF_5'(A_181,B_182,C_183),C_183)
      | k16_lattice3(A_181,C_183) = B_182
      | ~ r3_lattice3(A_181,B_182,C_183)
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l3_lattices(A_181)
      | ~ v4_lattice3(A_181)
      | ~ v10_lattices(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_71,plain,(
    ! [D_109,B_110,C_111] :
      ( r2_hidden(D_109,a_2_1_lattice3(B_110,C_111))
      | ~ r3_lattice3(B_110,D_109,C_111)
      | ~ m1_subset_1(D_109,u1_struct_0(B_110))
      | ~ l3_lattices(B_110)
      | v2_struct_0(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ! [A_59,B_60,C_61] :
      ( '#skF_4'(A_59,B_60,C_61) = A_59
      | ~ r2_hidden(A_59,a_2_1_lattice3(B_60,C_61))
      | ~ l3_lattices(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_75,plain,(
    ! [D_109,B_110,C_111] :
      ( '#skF_4'(D_109,B_110,C_111) = D_109
      | ~ r3_lattice3(B_110,D_109,C_111)
      | ~ m1_subset_1(D_109,u1_struct_0(B_110))
      | ~ l3_lattices(B_110)
      | v2_struct_0(B_110) ) ),
    inference(resolution,[status(thm)],[c_71,c_34])).

tff(c_1330,plain,(
    ! [A_353,B_354,C_355] :
      ( '#skF_4'('#skF_5'(A_353,B_354,C_355),A_353,C_355) = '#skF_5'(A_353,B_354,C_355)
      | ~ m1_subset_1('#skF_5'(A_353,B_354,C_355),u1_struct_0(A_353))
      | k16_lattice3(A_353,C_355) = B_354
      | ~ r3_lattice3(A_353,B_354,C_355)
      | ~ m1_subset_1(B_354,u1_struct_0(A_353))
      | ~ l3_lattices(A_353)
      | ~ v4_lattice3(A_353)
      | ~ v10_lattices(A_353)
      | v2_struct_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_300,c_75])).

tff(c_1334,plain,(
    ! [A_356,B_357,C_358] :
      ( '#skF_4'('#skF_5'(A_356,B_357,C_358),A_356,C_358) = '#skF_5'(A_356,B_357,C_358)
      | k16_lattice3(A_356,C_358) = B_357
      | ~ r3_lattice3(A_356,B_357,C_358)
      | ~ m1_subset_1(B_357,u1_struct_0(A_356))
      | ~ l3_lattices(A_356)
      | ~ v4_lattice3(A_356)
      | ~ v10_lattices(A_356)
      | v2_struct_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_46,c_1330])).

tff(c_1348,plain,(
    ! [C_358] :
      ( '#skF_4'('#skF_5'('#skF_6','#skF_7',C_358),'#skF_6',C_358) = '#skF_5'('#skF_6','#skF_7',C_358)
      | k16_lattice3('#skF_6',C_358) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_358)
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_1334])).

tff(c_1357,plain,(
    ! [C_358] :
      ( '#skF_4'('#skF_5'('#skF_6','#skF_7',C_358),'#skF_6',C_358) = '#skF_5'('#skF_6','#skF_7',C_358)
      | k16_lattice3('#skF_6',C_358) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_358)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1348])).

tff(c_1359,plain,(
    ! [C_359] :
      ( '#skF_4'('#skF_5'('#skF_6','#skF_7',C_359),'#skF_6',C_359) = '#skF_5'('#skF_6','#skF_7',C_359)
      | k16_lattice3('#skF_6',C_359) = '#skF_7'
      | ~ r3_lattice3('#skF_6','#skF_7',C_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1357])).

tff(c_32,plain,(
    ! [B_60,A_59,C_61] :
      ( r3_lattice3(B_60,'#skF_4'(A_59,B_60,C_61),C_61)
      | ~ r2_hidden(A_59,a_2_1_lattice3(B_60,C_61))
      | ~ l3_lattices(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1('#skF_4'(A_59,B_60,C_61),u1_struct_0(B_60))
      | ~ r2_hidden(A_59,a_2_1_lattice3(B_60,C_61))
      | ~ l3_lattices(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_199,plain,(
    ! [A_157,B_158,D_159,C_160] :
      ( r1_lattices(A_157,B_158,D_159)
      | ~ r2_hidden(D_159,C_160)
      | ~ m1_subset_1(D_159,u1_struct_0(A_157))
      | ~ r3_lattice3(A_157,B_158,C_160)
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l3_lattices(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_212,plain,(
    ! [A_161,B_162] :
      ( r1_lattices(A_161,B_162,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_161))
      | ~ r3_lattice3(A_161,B_162,'#skF_8')
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l3_lattices(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_56,c_199])).

tff(c_214,plain,(
    ! [B_162] :
      ( r1_lattices('#skF_6',B_162,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_162,'#skF_8')
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_212])).

tff(c_217,plain,(
    ! [B_162] :
      ( r1_lattices('#skF_6',B_162,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_162,'#skF_8')
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_214])).

tff(c_219,plain,(
    ! [B_163] :
      ( r1_lattices('#skF_6',B_163,'#skF_7')
      | ~ r3_lattice3('#skF_6',B_163,'#skF_8')
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_217])).

tff(c_231,plain,(
    ! [A_59,C_61] :
      ( r1_lattices('#skF_6','#skF_4'(A_59,'#skF_6',C_61),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_4'(A_59,'#skF_6',C_61),'#skF_8')
      | ~ r2_hidden(A_59,a_2_1_lattice3('#skF_6',C_61))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_249,plain,(
    ! [A_59,C_61] :
      ( r1_lattices('#skF_6','#skF_4'(A_59,'#skF_6',C_61),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_4'(A_59,'#skF_6',C_61),'#skF_8')
      | ~ r2_hidden(A_59,a_2_1_lattice3('#skF_6',C_61))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_231])).

tff(c_259,plain,(
    ! [A_165,C_166] :
      ( r1_lattices('#skF_6','#skF_4'(A_165,'#skF_6',C_166),'#skF_7')
      | ~ r3_lattice3('#skF_6','#skF_4'(A_165,'#skF_6',C_166),'#skF_8')
      | ~ r2_hidden(A_165,a_2_1_lattice3('#skF_6',C_166)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_249])).

tff(c_266,plain,(
    ! [A_59] :
      ( r1_lattices('#skF_6','#skF_4'(A_59,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_59,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_259])).

tff(c_271,plain,(
    ! [A_59] :
      ( r1_lattices('#skF_6','#skF_4'(A_59,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_59,a_2_1_lattice3('#skF_6','#skF_8'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_266])).

tff(c_272,plain,(
    ! [A_59] :
      ( r1_lattices('#skF_6','#skF_4'(A_59,'#skF_6','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_59,a_2_1_lattice3('#skF_6','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_271])).

tff(c_1376,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_272])).

tff(c_1397,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | k16_lattice3('#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1376])).

tff(c_1398,plain,
    ( r1_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1397])).

tff(c_1406,plain,(
    ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1398])).

tff(c_1409,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_1406])).

tff(c_1412,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1409])).

tff(c_1413,plain,
    ( ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1412])).

tff(c_1419,plain,(
    ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1413])).

tff(c_1422,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1419])).

tff(c_1425,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_54,c_1422])).

tff(c_1427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52,c_1425])).

tff(c_1428,plain,(
    ~ r3_lattice3('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1413])).

tff(c_1473,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1428])).

tff(c_1476,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_54,c_1473])).

tff(c_1478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52,c_1476])).

tff(c_1480,plain,(
    r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_1489,plain,
    ( '#skF_4'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1480,c_34])).

tff(c_1498,plain,
    ( '#skF_4'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1489])).

tff(c_1499,plain,(
    '#skF_4'('#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_6','#skF_8') = '#skF_5'('#skF_6','#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1498])).

tff(c_1521,plain,
    ( m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_5'('#skF_6','#skF_7','#skF_8'),a_2_1_lattice3('#skF_6','#skF_8'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1499,c_36])).

tff(c_1546,plain,
    ( m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1480,c_1521])).

tff(c_1547,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1546])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_2'(A_118,B_119,C_120),C_120)
      | r4_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l3_lattices(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_619,plain,(
    ! [A_237,B_238,B_239,C_240] :
      ( '#skF_4'('#skF_2'(A_237,B_238,a_2_1_lattice3(B_239,C_240)),B_239,C_240) = '#skF_2'(A_237,B_238,a_2_1_lattice3(B_239,C_240))
      | ~ l3_lattices(B_239)
      | v2_struct_0(B_239)
      | r4_lattice3(A_237,B_238,a_2_1_lattice3(B_239,C_240))
      | ~ m1_subset_1(B_238,u1_struct_0(A_237))
      | ~ l3_lattices(A_237)
      | v2_struct_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_108,c_34])).

tff(c_626,plain,(
    ! [A_237,B_238] :
      ( r1_lattices('#skF_6','#skF_2'(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | r4_lattice3(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_238,u1_struct_0(A_237))
      | ~ l3_lattices(A_237)
      | v2_struct_0(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_272])).

tff(c_646,plain,(
    ! [A_237,B_238] :
      ( r1_lattices('#skF_6','#skF_2'(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | v2_struct_0('#skF_6')
      | r4_lattice3(A_237,B_238,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_238,u1_struct_0(A_237))
      | ~ l3_lattices(A_237)
      | v2_struct_0(A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_626])).

tff(c_706,plain,(
    ! [A_253,B_254] :
      ( r1_lattices('#skF_6','#skF_2'(A_253,B_254,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_253,B_254,a_2_1_lattice3('#skF_6','#skF_8')),a_2_1_lattice3('#skF_6','#skF_8'))
      | r4_lattice3(A_253,B_254,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_254,u1_struct_0(A_253))
      | ~ l3_lattices(A_253)
      | v2_struct_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_646])).

tff(c_719,plain,(
    ! [A_255,B_256] :
      ( r1_lattices('#skF_6','#skF_2'(A_255,B_256,a_2_1_lattice3('#skF_6','#skF_8')),'#skF_7')
      | r4_lattice3(A_255,B_256,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l3_lattices(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_14,c_706])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_723,plain,
    ( r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_719,c_12])).

tff(c_726,plain,
    ( r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_723])).

tff(c_727,plain,(
    r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_726])).

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

tff(c_126,plain,(
    ! [A_145,D_146,B_147,C_148] :
      ( r1_lattices(A_145,D_146,B_147)
      | ~ r2_hidden(D_146,C_148)
      | ~ m1_subset_1(D_146,u1_struct_0(A_145))
      | ~ r4_lattice3(A_145,B_147,C_148)
      | ~ m1_subset_1(B_147,u1_struct_0(A_145))
      | ~ l3_lattices(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_655,plain,(
    ! [C_241,B_245,A_243,D_244,B_242] :
      ( r1_lattices(A_243,D_244,B_245)
      | ~ m1_subset_1(D_244,u1_struct_0(A_243))
      | ~ r4_lattice3(A_243,B_245,a_2_1_lattice3(B_242,C_241))
      | ~ m1_subset_1(B_245,u1_struct_0(A_243))
      | ~ l3_lattices(A_243)
      | v2_struct_0(A_243)
      | ~ r3_lattice3(B_242,D_244,C_241)
      | ~ m1_subset_1(D_244,u1_struct_0(B_242))
      | ~ l3_lattices(B_242)
      | v2_struct_0(B_242) ) ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_669,plain,(
    ! [B_245,B_242,C_241] :
      ( r1_lattices('#skF_6','#skF_7',B_245)
      | ~ r4_lattice3('#skF_6',B_245,a_2_1_lattice3(B_242,C_241))
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r3_lattice3(B_242,'#skF_7',C_241)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_242))
      | ~ l3_lattices(B_242)
      | v2_struct_0(B_242) ) ),
    inference(resolution,[status(thm)],[c_58,c_655])).

tff(c_678,plain,(
    ! [B_245,B_242,C_241] :
      ( r1_lattices('#skF_6','#skF_7',B_245)
      | ~ r4_lattice3('#skF_6',B_245,a_2_1_lattice3(B_242,C_241))
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r3_lattice3(B_242,'#skF_7',C_241)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_242))
      | ~ l3_lattices(B_242)
      | v2_struct_0(B_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_669])).

tff(c_680,plain,(
    ! [B_246,B_247,C_248] :
      ( r1_lattices('#skF_6','#skF_7',B_246)
      | ~ r4_lattice3('#skF_6',B_246,a_2_1_lattice3(B_247,C_248))
      | ~ m1_subset_1(B_246,u1_struct_0('#skF_6'))
      | ~ r3_lattice3(B_247,'#skF_7',C_248)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_247))
      | ~ l3_lattices(B_247)
      | v2_struct_0(B_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_678])).

tff(c_684,plain,(
    ! [B_247,C_248,C_53] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_247,C_248),C_53))
      | ~ m1_subset_1('#skF_3'('#skF_6',a_2_1_lattice3(B_247,C_248),C_53),u1_struct_0('#skF_6'))
      | ~ r3_lattice3(B_247,'#skF_7',C_248)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_247))
      | ~ l3_lattices(B_247)
      | v2_struct_0(B_247)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_247,C_248)) = C_53
      | ~ r4_lattice3('#skF_6',C_53,a_2_1_lattice3(B_247,C_248))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_6'))
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_680])).

tff(c_691,plain,(
    ! [B_247,C_248,C_53] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_247,C_248),C_53))
      | ~ m1_subset_1('#skF_3'('#skF_6',a_2_1_lattice3(B_247,C_248),C_53),u1_struct_0('#skF_6'))
      | ~ r3_lattice3(B_247,'#skF_7',C_248)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_247))
      | ~ l3_lattices(B_247)
      | v2_struct_0(B_247)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_247,C_248)) = C_53
      | ~ r4_lattice3('#skF_6',C_53,a_2_1_lattice3(B_247,C_248))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_684])).

tff(c_5304,plain,(
    ! [B_683,C_684,C_685] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_683,C_684),C_685))
      | ~ m1_subset_1('#skF_3'('#skF_6',a_2_1_lattice3(B_683,C_684),C_685),u1_struct_0('#skF_6'))
      | ~ r3_lattice3(B_683,'#skF_7',C_684)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_683))
      | ~ l3_lattices(B_683)
      | v2_struct_0(B_683)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_683,C_684)) = C_685
      | ~ r4_lattice3('#skF_6',C_685,a_2_1_lattice3(B_683,C_684))
      | ~ m1_subset_1(C_685,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_691])).

tff(c_5308,plain,(
    ! [B_683,C_684,C_53] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_683,C_684),C_53))
      | ~ r3_lattice3(B_683,'#skF_7',C_684)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_683))
      | ~ l3_lattices(B_683)
      | v2_struct_0(B_683)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_683,C_684)) = C_53
      | ~ r4_lattice3('#skF_6',C_53,a_2_1_lattice3(B_683,C_684))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_6'))
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_5304])).

tff(c_5311,plain,(
    ! [B_683,C_684,C_53] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_683,C_684),C_53))
      | ~ r3_lattice3(B_683,'#skF_7',C_684)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_683))
      | ~ l3_lattices(B_683)
      | v2_struct_0(B_683)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_683,C_684)) = C_53
      | ~ r4_lattice3('#skF_6',C_53,a_2_1_lattice3(B_683,C_684))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_5308])).

tff(c_6667,plain,(
    ! [B_753,C_754,C_755] :
      ( r1_lattices('#skF_6','#skF_7','#skF_3'('#skF_6',a_2_1_lattice3(B_753,C_754),C_755))
      | ~ r3_lattice3(B_753,'#skF_7',C_754)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_753))
      | ~ l3_lattices(B_753)
      | v2_struct_0(B_753)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_753,C_754)) = C_755
      | ~ r4_lattice3('#skF_6',C_755,a_2_1_lattice3(B_753,C_754))
      | ~ m1_subset_1(C_755,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5311])).

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

tff(c_6671,plain,(
    ! [B_753,C_754] :
      ( ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r3_lattice3(B_753,'#skF_7',C_754)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_753))
      | ~ l3_lattices(B_753)
      | v2_struct_0(B_753)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_753,C_754)) = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3(B_753,C_754))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6667,c_18])).

tff(c_6674,plain,(
    ! [B_753,C_754] :
      ( v2_struct_0('#skF_6')
      | ~ r3_lattice3(B_753,'#skF_7',C_754)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_753))
      | ~ l3_lattices(B_753)
      | v2_struct_0(B_753)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_753,C_754)) = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3(B_753,C_754)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_64,c_62,c_6671])).

tff(c_6676,plain,(
    ! [B_756,C_757] :
      ( ~ r3_lattice3(B_756,'#skF_7',C_757)
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_756))
      | ~ l3_lattices(B_756)
      | v2_struct_0(B_756)
      | k15_lattice3('#skF_6',a_2_1_lattice3(B_756,C_757)) = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',a_2_1_lattice3(B_756,C_757)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6674])).

tff(c_6679,plain,
    ( ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_727,c_6676])).

tff(c_6682,plain,
    ( v2_struct_0('#skF_6')
    | k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_6679])).

tff(c_6683,plain,(
    k15_lattice3('#skF_6',a_2_1_lattice3('#skF_6','#skF_8')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6682])).

tff(c_50,plain,(
    ! [A_87,B_91,C_93] :
      ( r3_lattices(A_87,B_91,k15_lattice3(A_87,C_93))
      | ~ r2_hidden(B_91,C_93)
      | ~ m1_subset_1(B_91,u1_struct_0(A_87))
      | ~ l3_lattices(A_87)
      | ~ v4_lattice3(A_87)
      | ~ v10_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6821,plain,(
    ! [B_91] :
      ( r3_lattices('#skF_6',B_91,'#skF_7')
      | ~ r2_hidden(B_91,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6683,c_50])).

tff(c_6918,plain,(
    ! [B_91] :
      ( r3_lattices('#skF_6',B_91,'#skF_7')
      | ~ r2_hidden(B_91,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_6821])).

tff(c_7119,plain,(
    ! [B_764] :
      ( r3_lattices('#skF_6',B_764,'#skF_7')
      | ~ r2_hidden(B_764,a_2_1_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_764,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6918])).

tff(c_7125,plain,
    ( r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1480,c_7119])).

tff(c_7143,plain,(
    r3_lattices('#skF_6','#skF_5'('#skF_6','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_7125])).

tff(c_42,plain,(
    ! [A_65,B_77,C_83] :
      ( ~ r3_lattices(A_65,'#skF_5'(A_65,B_77,C_83),B_77)
      | k16_lattice3(A_65,C_83) = B_77
      | ~ r3_lattice3(A_65,B_77,C_83)
      | ~ m1_subset_1(B_77,u1_struct_0(A_65))
      | ~ l3_lattices(A_65)
      | ~ v4_lattice3(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7152,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7143,c_42])).

tff(c_7155,plain,
    ( k16_lattice3('#skF_6','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_54,c_7152])).

tff(c_7157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52,c_7155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.42/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.18  
% 9.42/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.18  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 9.42/3.18  
% 9.42/3.18  %Foreground sorts:
% 9.42/3.18  
% 9.42/3.18  
% 9.42/3.18  %Background operators:
% 9.42/3.18  
% 9.42/3.18  
% 9.42/3.18  %Foreground operators:
% 9.42/3.18  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.42/3.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.42/3.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.42/3.18  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 9.42/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.42/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.42/3.18  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 9.42/3.18  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 9.42/3.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.42/3.18  tff('#skF_7', type, '#skF_7': $i).
% 9.42/3.18  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.42/3.18  tff('#skF_6', type, '#skF_6': $i).
% 9.42/3.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.42/3.18  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 9.42/3.18  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 9.42/3.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.42/3.18  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 9.42/3.18  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.42/3.18  tff('#skF_8', type, '#skF_8': $i).
% 9.42/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.42/3.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.42/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.42/3.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.42/3.18  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 9.42/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.42/3.18  
% 9.70/3.20  tff(f_173, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 9.70/3.20  tff(f_134, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 9.70/3.20  tff(f_110, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 9.70/3.20  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 9.70/3.20  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 9.70/3.20  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 9.70/3.20  tff(f_153, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 9.70/3.20  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_52, plain, (k16_lattice3('#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_64, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_62, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_60, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_58, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_54, plain, (r3_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_44, plain, (![A_65, B_77, C_83]: (r3_lattice3(A_65, '#skF_5'(A_65, B_77, C_83), C_83) | k16_lattice3(A_65, C_83)=B_77 | ~r3_lattice3(A_65, B_77, C_83) | ~m1_subset_1(B_77, u1_struct_0(A_65)) | ~l3_lattices(A_65) | ~v4_lattice3(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.70/3.20  tff(c_46, plain, (![A_65, B_77, C_83]: (m1_subset_1('#skF_5'(A_65, B_77, C_83), u1_struct_0(A_65)) | k16_lattice3(A_65, C_83)=B_77 | ~r3_lattice3(A_65, B_77, C_83) | ~m1_subset_1(B_77, u1_struct_0(A_65)) | ~l3_lattices(A_65) | ~v4_lattice3(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.70/3.20  tff(c_30, plain, (![D_64, B_60, C_61]: (r2_hidden(D_64, a_2_1_lattice3(B_60, C_61)) | ~r3_lattice3(B_60, D_64, C_61) | ~m1_subset_1(D_64, u1_struct_0(B_60)) | ~l3_lattices(B_60) | v2_struct_0(B_60))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.70/3.20  tff(c_300, plain, (![A_181, B_182, C_183]: (r3_lattice3(A_181, '#skF_5'(A_181, B_182, C_183), C_183) | k16_lattice3(A_181, C_183)=B_182 | ~r3_lattice3(A_181, B_182, C_183) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l3_lattices(A_181) | ~v4_lattice3(A_181) | ~v10_lattices(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.70/3.20  tff(c_71, plain, (![D_109, B_110, C_111]: (r2_hidden(D_109, a_2_1_lattice3(B_110, C_111)) | ~r3_lattice3(B_110, D_109, C_111) | ~m1_subset_1(D_109, u1_struct_0(B_110)) | ~l3_lattices(B_110) | v2_struct_0(B_110))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.70/3.20  tff(c_34, plain, (![A_59, B_60, C_61]: ('#skF_4'(A_59, B_60, C_61)=A_59 | ~r2_hidden(A_59, a_2_1_lattice3(B_60, C_61)) | ~l3_lattices(B_60) | v2_struct_0(B_60))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.70/3.20  tff(c_75, plain, (![D_109, B_110, C_111]: ('#skF_4'(D_109, B_110, C_111)=D_109 | ~r3_lattice3(B_110, D_109, C_111) | ~m1_subset_1(D_109, u1_struct_0(B_110)) | ~l3_lattices(B_110) | v2_struct_0(B_110))), inference(resolution, [status(thm)], [c_71, c_34])).
% 9.70/3.20  tff(c_1330, plain, (![A_353, B_354, C_355]: ('#skF_4'('#skF_5'(A_353, B_354, C_355), A_353, C_355)='#skF_5'(A_353, B_354, C_355) | ~m1_subset_1('#skF_5'(A_353, B_354, C_355), u1_struct_0(A_353)) | k16_lattice3(A_353, C_355)=B_354 | ~r3_lattice3(A_353, B_354, C_355) | ~m1_subset_1(B_354, u1_struct_0(A_353)) | ~l3_lattices(A_353) | ~v4_lattice3(A_353) | ~v10_lattices(A_353) | v2_struct_0(A_353))), inference(resolution, [status(thm)], [c_300, c_75])).
% 9.70/3.20  tff(c_1334, plain, (![A_356, B_357, C_358]: ('#skF_4'('#skF_5'(A_356, B_357, C_358), A_356, C_358)='#skF_5'(A_356, B_357, C_358) | k16_lattice3(A_356, C_358)=B_357 | ~r3_lattice3(A_356, B_357, C_358) | ~m1_subset_1(B_357, u1_struct_0(A_356)) | ~l3_lattices(A_356) | ~v4_lattice3(A_356) | ~v10_lattices(A_356) | v2_struct_0(A_356))), inference(resolution, [status(thm)], [c_46, c_1330])).
% 9.70/3.20  tff(c_1348, plain, (![C_358]: ('#skF_4'('#skF_5'('#skF_6', '#skF_7', C_358), '#skF_6', C_358)='#skF_5'('#skF_6', '#skF_7', C_358) | k16_lattice3('#skF_6', C_358)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_358) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_1334])).
% 9.70/3.20  tff(c_1357, plain, (![C_358]: ('#skF_4'('#skF_5'('#skF_6', '#skF_7', C_358), '#skF_6', C_358)='#skF_5'('#skF_6', '#skF_7', C_358) | k16_lattice3('#skF_6', C_358)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_358) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1348])).
% 9.70/3.20  tff(c_1359, plain, (![C_359]: ('#skF_4'('#skF_5'('#skF_6', '#skF_7', C_359), '#skF_6', C_359)='#skF_5'('#skF_6', '#skF_7', C_359) | k16_lattice3('#skF_6', C_359)='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', C_359))), inference(negUnitSimplification, [status(thm)], [c_66, c_1357])).
% 9.70/3.20  tff(c_32, plain, (![B_60, A_59, C_61]: (r3_lattice3(B_60, '#skF_4'(A_59, B_60, C_61), C_61) | ~r2_hidden(A_59, a_2_1_lattice3(B_60, C_61)) | ~l3_lattices(B_60) | v2_struct_0(B_60))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.70/3.20  tff(c_36, plain, (![A_59, B_60, C_61]: (m1_subset_1('#skF_4'(A_59, B_60, C_61), u1_struct_0(B_60)) | ~r2_hidden(A_59, a_2_1_lattice3(B_60, C_61)) | ~l3_lattices(B_60) | v2_struct_0(B_60))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.70/3.20  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.70/3.20  tff(c_199, plain, (![A_157, B_158, D_159, C_160]: (r1_lattices(A_157, B_158, D_159) | ~r2_hidden(D_159, C_160) | ~m1_subset_1(D_159, u1_struct_0(A_157)) | ~r3_lattice3(A_157, B_158, C_160) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l3_lattices(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.70/3.20  tff(c_212, plain, (![A_161, B_162]: (r1_lattices(A_161, B_162, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0(A_161)) | ~r3_lattice3(A_161, B_162, '#skF_8') | ~m1_subset_1(B_162, u1_struct_0(A_161)) | ~l3_lattices(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_56, c_199])).
% 9.70/3.20  tff(c_214, plain, (![B_162]: (r1_lattices('#skF_6', B_162, '#skF_7') | ~r3_lattice3('#skF_6', B_162, '#skF_8') | ~m1_subset_1(B_162, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_212])).
% 9.70/3.20  tff(c_217, plain, (![B_162]: (r1_lattices('#skF_6', B_162, '#skF_7') | ~r3_lattice3('#skF_6', B_162, '#skF_8') | ~m1_subset_1(B_162, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_214])).
% 9.70/3.20  tff(c_219, plain, (![B_163]: (r1_lattices('#skF_6', B_163, '#skF_7') | ~r3_lattice3('#skF_6', B_163, '#skF_8') | ~m1_subset_1(B_163, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_217])).
% 9.70/3.20  tff(c_231, plain, (![A_59, C_61]: (r1_lattices('#skF_6', '#skF_4'(A_59, '#skF_6', C_61), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_4'(A_59, '#skF_6', C_61), '#skF_8') | ~r2_hidden(A_59, a_2_1_lattice3('#skF_6', C_61)) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_219])).
% 9.70/3.20  tff(c_249, plain, (![A_59, C_61]: (r1_lattices('#skF_6', '#skF_4'(A_59, '#skF_6', C_61), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_4'(A_59, '#skF_6', C_61), '#skF_8') | ~r2_hidden(A_59, a_2_1_lattice3('#skF_6', C_61)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_231])).
% 9.70/3.20  tff(c_259, plain, (![A_165, C_166]: (r1_lattices('#skF_6', '#skF_4'(A_165, '#skF_6', C_166), '#skF_7') | ~r3_lattice3('#skF_6', '#skF_4'(A_165, '#skF_6', C_166), '#skF_8') | ~r2_hidden(A_165, a_2_1_lattice3('#skF_6', C_166)))), inference(negUnitSimplification, [status(thm)], [c_66, c_249])).
% 9.70/3.20  tff(c_266, plain, (![A_59]: (r1_lattices('#skF_6', '#skF_4'(A_59, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_59, a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_259])).
% 9.70/3.20  tff(c_271, plain, (![A_59]: (r1_lattices('#skF_6', '#skF_4'(A_59, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_59, a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_266])).
% 9.70/3.20  tff(c_272, plain, (![A_59]: (r1_lattices('#skF_6', '#skF_4'(A_59, '#skF_6', '#skF_8'), '#skF_7') | ~r2_hidden(A_59, a_2_1_lattice3('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_66, c_271])).
% 9.70/3.20  tff(c_1376, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1359, c_272])).
% 9.70/3.20  tff(c_1397, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | k16_lattice3('#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1376])).
% 9.70/3.20  tff(c_1398, plain, (r1_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1397])).
% 9.70/3.20  tff(c_1406, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1398])).
% 9.70/3.20  tff(c_1409, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_1406])).
% 9.70/3.20  tff(c_1412, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1409])).
% 9.70/3.20  tff(c_1413, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1412])).
% 9.70/3.20  tff(c_1419, plain, (~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1413])).
% 9.70/3.20  tff(c_1422, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_1419])).
% 9.70/3.20  tff(c_1425, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_54, c_1422])).
% 9.70/3.20  tff(c_1427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_52, c_1425])).
% 9.70/3.20  tff(c_1428, plain, (~r3_lattice3('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_1413])).
% 9.70/3.20  tff(c_1473, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_1428])).
% 9.70/3.20  tff(c_1476, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_54, c_1473])).
% 9.70/3.20  tff(c_1478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_52, c_1476])).
% 9.70/3.20  tff(c_1480, plain, (r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1398])).
% 9.70/3.20  tff(c_1489, plain, ('#skF_4'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1480, c_34])).
% 9.70/3.20  tff(c_1498, plain, ('#skF_4'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1489])).
% 9.70/3.20  tff(c_1499, plain, ('#skF_4'('#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_6', '#skF_8')='#skF_5'('#skF_6', '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_66, c_1498])).
% 9.70/3.20  tff(c_1521, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_5'('#skF_6', '#skF_7', '#skF_8'), a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1499, c_36])).
% 9.70/3.20  tff(c_1546, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1480, c_1521])).
% 9.70/3.20  tff(c_1547, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1546])).
% 9.70/3.20  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.70/3.20  tff(c_108, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_2'(A_118, B_119, C_120), C_120) | r4_lattice3(A_118, B_119, C_120) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l3_lattices(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.70/3.20  tff(c_619, plain, (![A_237, B_238, B_239, C_240]: ('#skF_4'('#skF_2'(A_237, B_238, a_2_1_lattice3(B_239, C_240)), B_239, C_240)='#skF_2'(A_237, B_238, a_2_1_lattice3(B_239, C_240)) | ~l3_lattices(B_239) | v2_struct_0(B_239) | r4_lattice3(A_237, B_238, a_2_1_lattice3(B_239, C_240)) | ~m1_subset_1(B_238, u1_struct_0(A_237)) | ~l3_lattices(A_237) | v2_struct_0(A_237))), inference(resolution, [status(thm)], [c_108, c_34])).
% 9.70/3.20  tff(c_626, plain, (![A_237, B_238]: (r1_lattices('#skF_6', '#skF_2'(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | r4_lattice3(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_238, u1_struct_0(A_237)) | ~l3_lattices(A_237) | v2_struct_0(A_237))), inference(superposition, [status(thm), theory('equality')], [c_619, c_272])).
% 9.70/3.20  tff(c_646, plain, (![A_237, B_238]: (r1_lattices('#skF_6', '#skF_2'(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6') | r4_lattice3(A_237, B_238, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_238, u1_struct_0(A_237)) | ~l3_lattices(A_237) | v2_struct_0(A_237))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_626])).
% 9.70/3.20  tff(c_706, plain, (![A_253, B_254]: (r1_lattices('#skF_6', '#skF_2'(A_253, B_254, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | ~r2_hidden('#skF_2'(A_253, B_254, a_2_1_lattice3('#skF_6', '#skF_8')), a_2_1_lattice3('#skF_6', '#skF_8')) | r4_lattice3(A_253, B_254, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_254, u1_struct_0(A_253)) | ~l3_lattices(A_253) | v2_struct_0(A_253))), inference(negUnitSimplification, [status(thm)], [c_66, c_646])).
% 9.70/3.20  tff(c_719, plain, (![A_255, B_256]: (r1_lattices('#skF_6', '#skF_2'(A_255, B_256, a_2_1_lattice3('#skF_6', '#skF_8')), '#skF_7') | r4_lattice3(A_255, B_256, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_256, u1_struct_0(A_255)) | ~l3_lattices(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_14, c_706])).
% 9.70/3.20  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.70/3.20  tff(c_723, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_719, c_12])).
% 9.70/3.20  tff(c_726, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_723])).
% 9.70/3.20  tff(c_727, plain, (r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_726])).
% 9.70/3.20  tff(c_22, plain, (![A_45, B_52, C_53]: (m1_subset_1('#skF_3'(A_45, B_52, C_53), u1_struct_0(A_45)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.70/3.20  tff(c_20, plain, (![A_45, B_52, C_53]: (r4_lattice3(A_45, '#skF_3'(A_45, B_52, C_53), B_52) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.70/3.20  tff(c_126, plain, (![A_145, D_146, B_147, C_148]: (r1_lattices(A_145, D_146, B_147) | ~r2_hidden(D_146, C_148) | ~m1_subset_1(D_146, u1_struct_0(A_145)) | ~r4_lattice3(A_145, B_147, C_148) | ~m1_subset_1(B_147, u1_struct_0(A_145)) | ~l3_lattices(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.70/3.20  tff(c_655, plain, (![C_241, B_245, A_243, D_244, B_242]: (r1_lattices(A_243, D_244, B_245) | ~m1_subset_1(D_244, u1_struct_0(A_243)) | ~r4_lattice3(A_243, B_245, a_2_1_lattice3(B_242, C_241)) | ~m1_subset_1(B_245, u1_struct_0(A_243)) | ~l3_lattices(A_243) | v2_struct_0(A_243) | ~r3_lattice3(B_242, D_244, C_241) | ~m1_subset_1(D_244, u1_struct_0(B_242)) | ~l3_lattices(B_242) | v2_struct_0(B_242))), inference(resolution, [status(thm)], [c_30, c_126])).
% 9.70/3.20  tff(c_669, plain, (![B_245, B_242, C_241]: (r1_lattices('#skF_6', '#skF_7', B_245) | ~r4_lattice3('#skF_6', B_245, a_2_1_lattice3(B_242, C_241)) | ~m1_subset_1(B_245, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r3_lattice3(B_242, '#skF_7', C_241) | ~m1_subset_1('#skF_7', u1_struct_0(B_242)) | ~l3_lattices(B_242) | v2_struct_0(B_242))), inference(resolution, [status(thm)], [c_58, c_655])).
% 9.70/3.20  tff(c_678, plain, (![B_245, B_242, C_241]: (r1_lattices('#skF_6', '#skF_7', B_245) | ~r4_lattice3('#skF_6', B_245, a_2_1_lattice3(B_242, C_241)) | ~m1_subset_1(B_245, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r3_lattice3(B_242, '#skF_7', C_241) | ~m1_subset_1('#skF_7', u1_struct_0(B_242)) | ~l3_lattices(B_242) | v2_struct_0(B_242))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_669])).
% 9.70/3.20  tff(c_680, plain, (![B_246, B_247, C_248]: (r1_lattices('#skF_6', '#skF_7', B_246) | ~r4_lattice3('#skF_6', B_246, a_2_1_lattice3(B_247, C_248)) | ~m1_subset_1(B_246, u1_struct_0('#skF_6')) | ~r3_lattice3(B_247, '#skF_7', C_248) | ~m1_subset_1('#skF_7', u1_struct_0(B_247)) | ~l3_lattices(B_247) | v2_struct_0(B_247))), inference(negUnitSimplification, [status(thm)], [c_66, c_678])).
% 9.70/3.20  tff(c_684, plain, (![B_247, C_248, C_53]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_247, C_248), C_53)) | ~m1_subset_1('#skF_3'('#skF_6', a_2_1_lattice3(B_247, C_248), C_53), u1_struct_0('#skF_6')) | ~r3_lattice3(B_247, '#skF_7', C_248) | ~m1_subset_1('#skF_7', u1_struct_0(B_247)) | ~l3_lattices(B_247) | v2_struct_0(B_247) | k15_lattice3('#skF_6', a_2_1_lattice3(B_247, C_248))=C_53 | ~r4_lattice3('#skF_6', C_53, a_2_1_lattice3(B_247, C_248)) | ~m1_subset_1(C_53, u1_struct_0('#skF_6')) | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_680])).
% 9.70/3.20  tff(c_691, plain, (![B_247, C_248, C_53]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_247, C_248), C_53)) | ~m1_subset_1('#skF_3'('#skF_6', a_2_1_lattice3(B_247, C_248), C_53), u1_struct_0('#skF_6')) | ~r3_lattice3(B_247, '#skF_7', C_248) | ~m1_subset_1('#skF_7', u1_struct_0(B_247)) | ~l3_lattices(B_247) | v2_struct_0(B_247) | k15_lattice3('#skF_6', a_2_1_lattice3(B_247, C_248))=C_53 | ~r4_lattice3('#skF_6', C_53, a_2_1_lattice3(B_247, C_248)) | ~m1_subset_1(C_53, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_684])).
% 9.70/3.20  tff(c_5304, plain, (![B_683, C_684, C_685]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_683, C_684), C_685)) | ~m1_subset_1('#skF_3'('#skF_6', a_2_1_lattice3(B_683, C_684), C_685), u1_struct_0('#skF_6')) | ~r3_lattice3(B_683, '#skF_7', C_684) | ~m1_subset_1('#skF_7', u1_struct_0(B_683)) | ~l3_lattices(B_683) | v2_struct_0(B_683) | k15_lattice3('#skF_6', a_2_1_lattice3(B_683, C_684))=C_685 | ~r4_lattice3('#skF_6', C_685, a_2_1_lattice3(B_683, C_684)) | ~m1_subset_1(C_685, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_691])).
% 9.70/3.20  tff(c_5308, plain, (![B_683, C_684, C_53]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_683, C_684), C_53)) | ~r3_lattice3(B_683, '#skF_7', C_684) | ~m1_subset_1('#skF_7', u1_struct_0(B_683)) | ~l3_lattices(B_683) | v2_struct_0(B_683) | k15_lattice3('#skF_6', a_2_1_lattice3(B_683, C_684))=C_53 | ~r4_lattice3('#skF_6', C_53, a_2_1_lattice3(B_683, C_684)) | ~m1_subset_1(C_53, u1_struct_0('#skF_6')) | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_5304])).
% 9.70/3.20  tff(c_5311, plain, (![B_683, C_684, C_53]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_683, C_684), C_53)) | ~r3_lattice3(B_683, '#skF_7', C_684) | ~m1_subset_1('#skF_7', u1_struct_0(B_683)) | ~l3_lattices(B_683) | v2_struct_0(B_683) | k15_lattice3('#skF_6', a_2_1_lattice3(B_683, C_684))=C_53 | ~r4_lattice3('#skF_6', C_53, a_2_1_lattice3(B_683, C_684)) | ~m1_subset_1(C_53, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_5308])).
% 9.70/3.20  tff(c_6667, plain, (![B_753, C_754, C_755]: (r1_lattices('#skF_6', '#skF_7', '#skF_3'('#skF_6', a_2_1_lattice3(B_753, C_754), C_755)) | ~r3_lattice3(B_753, '#skF_7', C_754) | ~m1_subset_1('#skF_7', u1_struct_0(B_753)) | ~l3_lattices(B_753) | v2_struct_0(B_753) | k15_lattice3('#skF_6', a_2_1_lattice3(B_753, C_754))=C_755 | ~r4_lattice3('#skF_6', C_755, a_2_1_lattice3(B_753, C_754)) | ~m1_subset_1(C_755, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_5311])).
% 9.70/3.20  tff(c_18, plain, (![A_45, C_53, B_52]: (~r1_lattices(A_45, C_53, '#skF_3'(A_45, B_52, C_53)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.70/3.20  tff(c_6671, plain, (![B_753, C_754]: (~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r3_lattice3(B_753, '#skF_7', C_754) | ~m1_subset_1('#skF_7', u1_struct_0(B_753)) | ~l3_lattices(B_753) | v2_struct_0(B_753) | k15_lattice3('#skF_6', a_2_1_lattice3(B_753, C_754))='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3(B_753, C_754)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_6667, c_18])).
% 9.70/3.20  tff(c_6674, plain, (![B_753, C_754]: (v2_struct_0('#skF_6') | ~r3_lattice3(B_753, '#skF_7', C_754) | ~m1_subset_1('#skF_7', u1_struct_0(B_753)) | ~l3_lattices(B_753) | v2_struct_0(B_753) | k15_lattice3('#skF_6', a_2_1_lattice3(B_753, C_754))='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3(B_753, C_754)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_64, c_62, c_6671])).
% 9.70/3.20  tff(c_6676, plain, (![B_756, C_757]: (~r3_lattice3(B_756, '#skF_7', C_757) | ~m1_subset_1('#skF_7', u1_struct_0(B_756)) | ~l3_lattices(B_756) | v2_struct_0(B_756) | k15_lattice3('#skF_6', a_2_1_lattice3(B_756, C_757))='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', a_2_1_lattice3(B_756, C_757)))), inference(negUnitSimplification, [status(thm)], [c_66, c_6674])).
% 9.70/3.20  tff(c_6679, plain, (~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7'), inference(resolution, [status(thm)], [c_727, c_6676])).
% 9.70/3.20  tff(c_6682, plain, (v2_struct_0('#skF_6') | k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_6679])).
% 9.70/3.20  tff(c_6683, plain, (k15_lattice3('#skF_6', a_2_1_lattice3('#skF_6', '#skF_8'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_66, c_6682])).
% 9.70/3.20  tff(c_50, plain, (![A_87, B_91, C_93]: (r3_lattices(A_87, B_91, k15_lattice3(A_87, C_93)) | ~r2_hidden(B_91, C_93) | ~m1_subset_1(B_91, u1_struct_0(A_87)) | ~l3_lattices(A_87) | ~v4_lattice3(A_87) | ~v10_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.70/3.20  tff(c_6821, plain, (![B_91]: (r3_lattices('#skF_6', B_91, '#skF_7') | ~r2_hidden(B_91, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6683, c_50])).
% 9.70/3.20  tff(c_6918, plain, (![B_91]: (r3_lattices('#skF_6', B_91, '#skF_7') | ~r2_hidden(B_91, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_91, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_6821])).
% 9.70/3.20  tff(c_7119, plain, (![B_764]: (r3_lattices('#skF_6', B_764, '#skF_7') | ~r2_hidden(B_764, a_2_1_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_764, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_6918])).
% 9.70/3.20  tff(c_7125, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1480, c_7119])).
% 9.70/3.20  tff(c_7143, plain, (r3_lattices('#skF_6', '#skF_5'('#skF_6', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_7125])).
% 9.70/3.20  tff(c_42, plain, (![A_65, B_77, C_83]: (~r3_lattices(A_65, '#skF_5'(A_65, B_77, C_83), B_77) | k16_lattice3(A_65, C_83)=B_77 | ~r3_lattice3(A_65, B_77, C_83) | ~m1_subset_1(B_77, u1_struct_0(A_65)) | ~l3_lattices(A_65) | ~v4_lattice3(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.70/3.20  tff(c_7152, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_7143, c_42])).
% 9.70/3.20  tff(c_7155, plain, (k16_lattice3('#skF_6', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_54, c_7152])).
% 9.70/3.20  tff(c_7157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_52, c_7155])).
% 9.70/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.70/3.20  
% 9.70/3.20  Inference rules
% 9.70/3.20  ----------------------
% 9.70/3.20  #Ref     : 0
% 9.70/3.20  #Sup     : 1249
% 9.70/3.20  #Fact    : 0
% 9.70/3.20  #Define  : 0
% 9.70/3.20  #Split   : 22
% 9.70/3.20  #Chain   : 0
% 9.70/3.20  #Close   : 0
% 9.70/3.20  
% 9.70/3.20  Ordering : KBO
% 9.70/3.20  
% 9.70/3.20  Simplification rules
% 9.70/3.20  ----------------------
% 9.70/3.20  #Subsume      : 247
% 9.70/3.20  #Demod        : 2055
% 9.70/3.20  #Tautology    : 315
% 9.70/3.20  #SimpNegUnit  : 648
% 9.70/3.20  #BackRed      : 55
% 9.70/3.20  
% 9.70/3.20  #Partial instantiations: 0
% 9.70/3.20  #Strategies tried      : 1
% 9.70/3.20  
% 9.70/3.20  Timing (in seconds)
% 9.70/3.20  ----------------------
% 9.70/3.21  Preprocessing        : 0.35
% 9.70/3.21  Parsing              : 0.19
% 9.70/3.21  CNF conversion       : 0.03
% 9.70/3.21  Main loop            : 2.07
% 9.70/3.21  Inferencing          : 0.74
% 9.70/3.21  Reduction            : 0.68
% 9.70/3.21  Demodulation         : 0.46
% 9.70/3.21  BG Simplification    : 0.07
% 9.70/3.21  Subsumption          : 0.45
% 9.70/3.21  Abstraction          : 0.09
% 9.70/3.21  MUC search           : 0.00
% 9.70/3.21  Cooper               : 0.00
% 9.70/3.21  Total                : 2.46
% 9.70/3.21  Index Insertion      : 0.00
% 9.70/3.21  Index Deletion       : 0.00
% 9.70/3.21  Index Matching       : 0.00
% 9.70/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
