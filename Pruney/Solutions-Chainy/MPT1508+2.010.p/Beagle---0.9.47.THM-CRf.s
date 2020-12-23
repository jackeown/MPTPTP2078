%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:48 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :  251 (34587 expanded)
%              Number of leaves         :   35 (11826 expanded)
%              Depth                    :   68
%              Number of atoms          :  897 (164531 expanded)
%              Number of equality atoms :  114 (20145 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_184,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_164,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_58,plain,(
    k16_lattice3('#skF_7','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_70,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_68,plain,(
    v4_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_66,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    r3_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

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

tff(c_361,plain,(
    ! [A_209,B_210,C_211] :
      ( r3_lattice3(A_209,'#skF_6'(A_209,B_210,C_211),C_211)
      | k16_lattice3(A_209,C_211) = B_210
      | ~ r3_lattice3(A_209,B_210,C_211)
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l3_lattices(A_209)
      | ~ v4_lattice3(A_209)
      | ~ v10_lattices(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    ! [D_111,B_112,C_113] :
      ( r2_hidden(D_111,a_2_1_lattice3(B_112,C_113))
      | ~ r3_lattice3(B_112,D_111,C_113)
      | ~ m1_subset_1(D_111,u1_struct_0(B_112))
      | ~ l3_lattices(B_112)
      | v2_struct_0(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_57,B_58,C_59] :
      ( '#skF_4'(A_57,B_58,C_59) = A_57
      | ~ r2_hidden(A_57,a_2_1_lattice3(B_58,C_59))
      | ~ l3_lattices(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_80,plain,(
    ! [D_111,B_112,C_113] :
      ( '#skF_4'(D_111,B_112,C_113) = D_111
      | ~ r3_lattice3(B_112,D_111,C_113)
      | ~ m1_subset_1(D_111,u1_struct_0(B_112))
      | ~ l3_lattices(B_112)
      | v2_struct_0(B_112) ) ),
    inference(resolution,[status(thm)],[c_76,c_32])).

tff(c_2114,plain,(
    ! [A_406,B_407,C_408] :
      ( '#skF_4'('#skF_6'(A_406,B_407,C_408),A_406,C_408) = '#skF_6'(A_406,B_407,C_408)
      | ~ m1_subset_1('#skF_6'(A_406,B_407,C_408),u1_struct_0(A_406))
      | k16_lattice3(A_406,C_408) = B_407
      | ~ r3_lattice3(A_406,B_407,C_408)
      | ~ m1_subset_1(B_407,u1_struct_0(A_406))
      | ~ l3_lattices(A_406)
      | ~ v4_lattice3(A_406)
      | ~ v10_lattices(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_361,c_80])).

tff(c_2118,plain,(
    ! [A_409,B_410,C_411] :
      ( '#skF_4'('#skF_6'(A_409,B_410,C_411),A_409,C_411) = '#skF_6'(A_409,B_410,C_411)
      | k16_lattice3(A_409,C_411) = B_410
      | ~ r3_lattice3(A_409,B_410,C_411)
      | ~ m1_subset_1(B_410,u1_struct_0(A_409))
      | ~ l3_lattices(A_409)
      | ~ v4_lattice3(A_409)
      | ~ v10_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_52,c_2114])).

tff(c_2132,plain,(
    ! [C_411] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_411),'#skF_7',C_411) = '#skF_6'('#skF_7','#skF_8',C_411)
      | k16_lattice3('#skF_7',C_411) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_411)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_2118])).

tff(c_2141,plain,(
    ! [C_411] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_411),'#skF_7',C_411) = '#skF_6'('#skF_7','#skF_8',C_411)
      | k16_lattice3('#skF_7',C_411) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_411)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2132])).

tff(c_2143,plain,(
    ! [C_412] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_8',C_412),'#skF_7',C_412) = '#skF_6'('#skF_7','#skF_8',C_412)
      | k16_lattice3('#skF_7',C_412) = '#skF_8'
      | ~ r3_lattice3('#skF_7','#skF_8',C_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2141])).

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
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_215,plain,(
    ! [A_169,B_170,D_171,C_172] :
      ( r1_lattices(A_169,B_170,D_171)
      | ~ r2_hidden(D_171,C_172)
      | ~ m1_subset_1(D_171,u1_struct_0(A_169))
      | ~ r3_lattice3(A_169,B_170,C_172)
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_241,plain,(
    ! [A_176,B_177] :
      ( r1_lattices(A_176,B_177,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_176))
      | ~ r3_lattice3(A_176,B_177,'#skF_9')
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l3_lattices(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_62,c_215])).

tff(c_243,plain,(
    ! [B_177] :
      ( r1_lattices('#skF_7',B_177,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_177,'#skF_9')
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_241])).

tff(c_246,plain,(
    ! [B_177] :
      ( r1_lattices('#skF_7',B_177,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_177,'#skF_9')
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_243])).

tff(c_248,plain,(
    ! [B_178] :
      ( r1_lattices('#skF_7',B_178,'#skF_8')
      | ~ r3_lattice3('#skF_7',B_178,'#skF_9')
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_246])).

tff(c_264,plain,(
    ! [A_57,C_59] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_9')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7',C_59))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_248])).

tff(c_282,plain,(
    ! [A_57,C_59] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_57,'#skF_7',C_59),'#skF_9')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7',C_59))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_264])).

tff(c_288,plain,(
    ! [A_181,C_182] :
      ( r1_lattices('#skF_7','#skF_4'(A_181,'#skF_7',C_182),'#skF_8')
      | ~ r3_lattice3('#skF_7','#skF_4'(A_181,'#skF_7',C_182),'#skF_9')
      | ~ r2_hidden(A_181,a_2_1_lattice3('#skF_7',C_182)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_282])).

tff(c_295,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_288])).

tff(c_300,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_295])).

tff(c_301,plain,(
    ! [A_57] :
      ( r1_lattices('#skF_7','#skF_4'(A_57,'#skF_7','#skF_9'),'#skF_8')
      | ~ r2_hidden(A_57,a_2_1_lattice3('#skF_7','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_300])).

tff(c_2166,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2143,c_301])).

tff(c_2190,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2166])).

tff(c_2191,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2190])).

tff(c_2199,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2191])).

tff(c_2202,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_2199])).

tff(c_2205,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2202])).

tff(c_2206,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2205])).

tff(c_2216,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2206])).

tff(c_2219,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_2216])).

tff(c_2222,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_2219])).

tff(c_2224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_2222])).

tff(c_2225,plain,(
    ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2206])).

tff(c_2288,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_2225])).

tff(c_2291,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_2288])).

tff(c_2293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_2291])).

tff(c_2295,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2191])).

tff(c_2304,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2295,c_32])).

tff(c_2313,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2304])).

tff(c_2314,plain,(
    '#skF_4'('#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2313])).

tff(c_2345,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_34])).

tff(c_2375,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2295,c_2345])).

tff(c_2376,plain,(
    m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2375])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden('#skF_2'(A_120,B_121,C_122),C_122)
      | r4_lattice3(A_120,B_121,C_122)
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l3_lattices(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_591,plain,(
    ! [A_251,B_252,B_253,C_254] :
      ( '#skF_4'('#skF_2'(A_251,B_252,a_2_1_lattice3(B_253,C_254)),B_253,C_254) = '#skF_2'(A_251,B_252,a_2_1_lattice3(B_253,C_254))
      | ~ l3_lattices(B_253)
      | v2_struct_0(B_253)
      | r4_lattice3(A_251,B_252,a_2_1_lattice3(B_253,C_254))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_108,c_32])).

tff(c_598,plain,(
    ! [A_251,B_252] :
      ( r1_lattices('#skF_7','#skF_2'(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | r4_lattice3(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_301])).

tff(c_618,plain,(
    ! [A_251,B_252] :
      ( r1_lattices('#skF_7','#skF_2'(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | v2_struct_0('#skF_7')
      | r4_lattice3(A_251,B_252,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_598])).

tff(c_676,plain,(
    ! [A_258,B_259] :
      ( r1_lattices('#skF_7','#skF_2'(A_258,B_259,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_258,B_259,a_2_1_lattice3('#skF_7','#skF_9')),a_2_1_lattice3('#skF_7','#skF_9'))
      | r4_lattice3(A_258,B_259,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_259,u1_struct_0(A_258))
      | ~ l3_lattices(A_258)
      | v2_struct_0(A_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_618])).

tff(c_689,plain,(
    ! [A_260,B_261] :
      ( r1_lattices('#skF_7','#skF_2'(A_260,B_261,a_2_1_lattice3('#skF_7','#skF_9')),'#skF_8')
      | r4_lattice3(A_260,B_261,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_261,u1_struct_0(A_260))
      | ~ l3_lattices(A_260)
      | v2_struct_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_14,c_676])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_693,plain,
    ( r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_689,c_12])).

tff(c_696,plain,
    ( r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_693])).

tff(c_697,plain,(
    r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_696])).

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

tff(c_308,plain,(
    ! [A_186,B_187,C_188] :
      ( r4_lattice3(A_186,'#skF_3'(A_186,B_187,C_188),B_187)
      | k15_lattice3(A_186,B_187) = C_188
      | ~ r4_lattice3(A_186,C_188,B_187)
      | ~ m1_subset_1(C_188,u1_struct_0(A_186))
      | ~ v4_lattice3(A_186)
      | ~ v10_lattices(A_186)
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_138,plain,(
    ! [D_148,B_149,C_150] :
      ( r2_hidden(D_148,a_2_2_lattice3(B_149,C_150))
      | ~ r4_lattice3(B_149,D_148,C_150)
      | ~ m1_subset_1(D_148,u1_struct_0(B_149))
      | ~ l3_lattices(B_149)
      | ~ v4_lattice3(B_149)
      | ~ v10_lattices(B_149)
      | v2_struct_0(B_149) ) ),
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

tff(c_142,plain,(
    ! [D_148,B_149,C_150] :
      ( '#skF_5'(D_148,B_149,C_150) = D_148
      | ~ r4_lattice3(B_149,D_148,C_150)
      | ~ m1_subset_1(D_148,u1_struct_0(B_149))
      | ~ l3_lattices(B_149)
      | ~ v4_lattice3(B_149)
      | ~ v10_lattices(B_149)
      | v2_struct_0(B_149) ) ),
    inference(resolution,[status(thm)],[c_138,c_40])).

tff(c_2634,plain,(
    ! [A_424,B_425,C_426] :
      ( '#skF_5'('#skF_3'(A_424,B_425,C_426),A_424,B_425) = '#skF_3'(A_424,B_425,C_426)
      | ~ m1_subset_1('#skF_3'(A_424,B_425,C_426),u1_struct_0(A_424))
      | k15_lattice3(A_424,B_425) = C_426
      | ~ r4_lattice3(A_424,C_426,B_425)
      | ~ m1_subset_1(C_426,u1_struct_0(A_424))
      | ~ v4_lattice3(A_424)
      | ~ v10_lattices(A_424)
      | ~ l3_lattices(A_424)
      | v2_struct_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_308,c_142])).

tff(c_2920,plain,(
    ! [A_447,B_448,C_449] :
      ( '#skF_5'('#skF_3'(A_447,B_448,C_449),A_447,B_448) = '#skF_3'(A_447,B_448,C_449)
      | k15_lattice3(A_447,B_448) = C_449
      | ~ r4_lattice3(A_447,C_449,B_448)
      | ~ m1_subset_1(C_449,u1_struct_0(A_447))
      | ~ v4_lattice3(A_447)
      | ~ v10_lattices(A_447)
      | ~ l3_lattices(A_447)
      | v2_struct_0(A_447) ) ),
    inference(resolution,[status(thm)],[c_22,c_2634])).

tff(c_2938,plain,(
    ! [B_448] :
      ( '#skF_5'('#skF_3'('#skF_7',B_448,'#skF_8'),'#skF_7',B_448) = '#skF_3'('#skF_7',B_448,'#skF_8')
      | k15_lattice3('#skF_7',B_448) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_448)
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_2920])).

tff(c_2952,plain,(
    ! [B_448] :
      ( '#skF_5'('#skF_3'('#skF_7',B_448,'#skF_8'),'#skF_7',B_448) = '#skF_3'('#skF_7',B_448,'#skF_8')
      | k15_lattice3('#skF_7',B_448) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_448)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_2938])).

tff(c_2953,plain,(
    ! [B_448] :
      ( '#skF_5'('#skF_3'('#skF_7',B_448,'#skF_8'),'#skF_7',B_448) = '#skF_3'('#skF_7',B_448,'#skF_8')
      | k15_lattice3('#skF_7',B_448) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2952])).

tff(c_38,plain,(
    ! [B_64,A_63,C_65] :
      ( r4_lattice3(B_64,'#skF_5'(A_63,B_64,C_65),C_65)
      | ~ r2_hidden(A_63,a_2_2_lattice3(B_64,C_65))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2342,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2314,c_30])).

tff(c_2372,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2295,c_2342])).

tff(c_2373,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2372])).

tff(c_2117,plain,(
    ! [A_69,B_81,C_87] :
      ( '#skF_4'('#skF_6'(A_69,B_81,C_87),A_69,C_87) = '#skF_6'(A_69,B_81,C_87)
      | k16_lattice3(A_69,C_87) = B_81
      | ~ r3_lattice3(A_69,B_81,C_87)
      | ~ m1_subset_1(B_81,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | ~ v4_lattice3(A_69)
      | ~ v10_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_52,c_2114])).

tff(c_2405,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2376,c_2117])).

tff(c_2426,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_87)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2405])).

tff(c_3146,plain,(
    ! [C_462] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_462),'#skF_7',C_462) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_462)
      | k16_lattice3('#skF_7',C_462) = '#skF_6'('#skF_7','#skF_8','#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),C_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2426])).

tff(c_3173,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_301])).

tff(c_3197,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_3173])).

tff(c_3205,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3197])).

tff(c_3208,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_3205])).

tff(c_3211,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3208])).

tff(c_3212,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3211])).

tff(c_3213,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3212])).

tff(c_3216,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_3213])).

tff(c_3219,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2376,c_2373,c_3216])).

tff(c_3220,plain,(
    k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3219])).

tff(c_3233,plain,(
    '#skF_6'('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3220,c_58])).

tff(c_54,plain,(
    ! [A_91,C_97,B_95] :
      ( r3_lattices(A_91,k16_lattice3(A_91,C_97),B_95)
      | ~ r2_hidden(B_95,C_97)
      | ~ m1_subset_1(B_95,u1_struct_0(A_91))
      | ~ l3_lattices(A_91)
      | ~ v4_lattice3(A_91)
      | ~ v10_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3239,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_95)
      | ~ r2_hidden(B_95,'#skF_9')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3220,c_54])).

tff(c_3248,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_95)
      | ~ r2_hidden(B_95,'#skF_9')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3239])).

tff(c_3254,plain,(
    ! [B_467] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_467)
      | ~ r2_hidden(B_467,'#skF_9')
      | ~ m1_subset_1(B_467,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3248])).

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

tff(c_3258,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3254,c_48])).

tff(c_3261,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_70,c_68,c_66,c_60,c_3220,c_3258])).

tff(c_3263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3233,c_3261])).

tff(c_3264,plain,(
    ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3212])).

tff(c_3325,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_3264])).

tff(c_3328,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2376,c_2373,c_3325])).

tff(c_3329,plain,(
    k16_lattice3('#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3328])).

tff(c_3331,plain,(
    '#skF_6'('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_58])).

tff(c_3337,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_95)
      | ~ r2_hidden(B_95,'#skF_9')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3329,c_54])).

tff(c_3346,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_95)
      | ~ r2_hidden(B_95,'#skF_9')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3337])).

tff(c_3352,plain,(
    ! [B_471] :
      ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),B_471)
      | ~ r2_hidden(B_471,'#skF_9')
      | ~ m1_subset_1(B_471,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3346])).

tff(c_3356,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3352,c_48])).

tff(c_3359,plain,
    ( '#skF_6'('#skF_7','#skF_8','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_70,c_68,c_66,c_60,c_3329,c_3356])).

tff(c_3361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3331,c_3359])).

tff(c_3363,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3197])).

tff(c_3383,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3363,c_32])).

tff(c_3392,plain,
    ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3383])).

tff(c_3393,plain,(
    '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_7','#skF_9') = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3392])).

tff(c_3425,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_34])).

tff(c_3454,plain,
    ( m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3363,c_3425])).

tff(c_3455,plain,(
    m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3454])).

tff(c_3422,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_30])).

tff(c_3451,plain,
    ( r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3363,c_3422])).

tff(c_3452,plain,(
    r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3451])).

tff(c_3475,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3455,c_2117])).

tff(c_3500,plain,(
    ! [C_87] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87),'#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | k16_lattice3('#skF_7',C_87) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_87)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3475])).

tff(c_6231,plain,(
    ! [C_717] :
      ( '#skF_4'('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_717),'#skF_7',C_717) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_717)
      | k16_lattice3('#skF_7',C_717) = '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9')
      | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),C_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3500])).

tff(c_6268,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6231,c_301])).

tff(c_6298,plain,
    ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9'))
    | '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3452,c_6268])).

tff(c_6306,plain,(
    ~ r2_hidden('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_6298])).

tff(c_6309,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_6306])).

tff(c_6312,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6309])).

tff(c_6313,plain,
    ( ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6312])).

tff(c_6314,plain,(
    ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6313])).

tff(c_6317,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | ~ r3_lattice3('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),'#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_6314])).

tff(c_6320,plain,
    ( '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3455,c_3452,c_6317])).

tff(c_6321,plain,(
    '#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9') = k16_lattice3('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6320])).

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

tff(c_3839,plain,(
    ! [A_514,B_515] :
      ( r1_lattices(A_514,'#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_515)
      | ~ m1_subset_1('#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),u1_struct_0(A_514))
      | ~ r4_lattice3(A_514,B_515,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_515,u1_struct_0(A_514))
      | ~ l3_lattices(A_514)
      | v2_struct_0(A_514) ) ),
    inference(resolution,[status(thm)],[c_3363,c_10])).

tff(c_3841,plain,(
    ! [B_515] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_515)
      | ~ r4_lattice3('#skF_7',B_515,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_515,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3455,c_3839])).

tff(c_3847,plain,(
    ! [B_515] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_515)
      | ~ r4_lattice3('#skF_7',B_515,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_515,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3841])).

tff(c_3848,plain,(
    ! [B_515] :
      ( r1_lattices('#skF_7','#skF_6'('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_9'),B_515)
      | ~ r4_lattice3('#skF_7',B_515,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_515,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3847])).

tff(c_6770,plain,(
    ! [B_732] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),B_732)
      | ~ r4_lattice3('#skF_7',B_732,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_732,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6321,c_3848])).

tff(c_6785,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_6770])).

tff(c_6799,plain,(
    ! [A_63] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_63,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_63,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_6785])).

tff(c_7300,plain,(
    ! [A_771] :
      ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_5'(A_771,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
      | ~ m1_subset_1('#skF_5'(A_771,'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_771,a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6799])).

tff(c_7332,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2953,c_7300])).

tff(c_7373,plain,
    ( r1_lattices('#skF_7',k16_lattice3('#skF_7','#skF_9'),'#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_5'('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),'#skF_7',a_2_1_lattice3('#skF_7','#skF_9')),u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_7332])).

tff(c_8609,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_7373])).

tff(c_8612,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_8609])).

tff(c_8615,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_8612])).

tff(c_8616,plain,
    ( ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8615])).

tff(c_8617,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8616])).

tff(c_8620,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_8617])).

tff(c_8623,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_697,c_8620])).

tff(c_8624,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8623])).

tff(c_56,plain,(
    ! [A_91,B_95,C_97] :
      ( r3_lattices(A_91,B_95,k15_lattice3(A_91,C_97))
      | ~ r2_hidden(B_95,C_97)
      | ~ m1_subset_1(B_95,u1_struct_0(A_91))
      | ~ l3_lattices(A_91)
      | ~ v4_lattice3(A_91)
      | ~ v10_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_8634,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8624,c_56])).

tff(c_8646,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_8634])).

tff(c_8694,plain,(
    ! [B_910] :
      ( r3_lattices('#skF_7',B_910,'#skF_8')
      | ~ r2_hidden(B_910,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_910,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8646])).

tff(c_8700,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2295,c_8694])).

tff(c_8718,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_8700])).

tff(c_8727,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8718,c_48])).

tff(c_8730,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_8727])).

tff(c_8732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_8730])).

tff(c_8733,plain,(
    ~ r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_8616])).

tff(c_8874,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_8733])).

tff(c_8877,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_697,c_8874])).

tff(c_8878,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8877])).

tff(c_8888,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8878,c_56])).

tff(c_8900,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_8888])).

tff(c_8906,plain,(
    ! [B_914] :
      ( r3_lattices('#skF_7',B_914,'#skF_8')
      | ~ r2_hidden(B_914,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_914,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8900])).

tff(c_8912,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2295,c_8906])).

tff(c_8930,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_8912])).

tff(c_8981,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8930,c_48])).

tff(c_8984,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_8981])).

tff(c_8986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_8984])).

tff(c_8988,plain,(
    r2_hidden('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_2_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_7373])).

tff(c_2954,plain,(
    ! [B_450] :
      ( '#skF_5'('#skF_3'('#skF_7',B_450,'#skF_8'),'#skF_7',B_450) = '#skF_3'('#skF_7',B_450,'#skF_8')
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2952])).

tff(c_42,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1('#skF_5'(A_63,B_64,C_65),u1_struct_0(B_64))
      | ~ r2_hidden(A_63,a_2_2_lattice3(B_64,C_65))
      | ~ l3_lattices(B_64)
      | ~ v4_lattice3(B_64)
      | ~ v10_lattices(B_64)
      | v2_struct_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2990,plain,(
    ! [B_450] :
      ( m1_subset_1('#skF_3'('#skF_7',B_450,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_42])).

tff(c_3007,plain,(
    ! [B_450] :
      ( m1_subset_1('#skF_3'('#skF_7',B_450,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2990])).

tff(c_3008,plain,(
    ! [B_450] :
      ( m1_subset_1('#skF_3'('#skF_7',B_450,'#skF_8'),u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3007])).

tff(c_9000,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_8988,c_3008])).

tff(c_9021,plain,
    ( m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_9000])).

tff(c_9032,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_9021])).

tff(c_9128,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9032,c_56])).

tff(c_9140,plain,(
    ! [B_95] :
      ( r3_lattices('#skF_7',B_95,'#skF_8')
      | ~ r2_hidden(B_95,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_9128])).

tff(c_9327,plain,(
    ! [B_927] :
      ( r3_lattices('#skF_7',B_927,'#skF_8')
      | ~ r2_hidden(B_927,a_2_1_lattice3('#skF_7','#skF_9'))
      | ~ m1_subset_1(B_927,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9140])).

tff(c_9333,plain,
    ( r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8')
    | ~ m1_subset_1('#skF_6'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2295,c_9327])).

tff(c_9351,plain,(
    r3_lattices('#skF_7','#skF_6'('#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_9333])).

tff(c_9360,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9351,c_48])).

tff(c_9363,plain,
    ( k16_lattice3('#skF_7','#skF_9') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_9360])).

tff(c_9365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_9363])).

tff(c_9367,plain,(
    k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9021])).

tff(c_9366,plain,(
    m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9021])).

tff(c_2993,plain,(
    ! [B_450] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_450,'#skF_8'),B_450)
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | ~ l3_lattices('#skF_7')
      | ~ v4_lattice3('#skF_7')
      | ~ v10_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_38])).

tff(c_3010,plain,(
    ! [B_450] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_450,'#skF_8'),B_450)
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | v2_struct_0('#skF_7')
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2993])).

tff(c_3011,plain,(
    ! [B_450] :
      ( r4_lattice3('#skF_7','#skF_3'('#skF_7',B_450,'#skF_8'),B_450)
      | ~ r2_hidden('#skF_3'('#skF_7',B_450,'#skF_8'),a_2_2_lattice3('#skF_7',B_450))
      | k15_lattice3('#skF_7',B_450) = '#skF_8'
      | ~ r4_lattice3('#skF_7','#skF_8',B_450) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3010])).

tff(c_8997,plain,
    ( r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_8988,c_3011])).

tff(c_9018,plain,
    ( r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9'))
    | k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_8997])).

tff(c_9424,plain,(
    r4_lattice3('#skF_7','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),a_2_1_lattice3('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_9367,c_9018])).

tff(c_149,plain,(
    ! [A_160,D_161,B_162,C_163] :
      ( r1_lattices(A_160,D_161,B_162)
      | ~ r2_hidden(D_161,C_163)
      | ~ m1_subset_1(D_161,u1_struct_0(A_160))
      | ~ r4_lattice3(A_160,B_162,C_163)
      | ~ m1_subset_1(B_162,u1_struct_0(A_160))
      | ~ l3_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1007,plain,(
    ! [B_289,A_291,D_290,C_292,B_288] :
      ( r1_lattices(A_291,D_290,B_288)
      | ~ m1_subset_1(D_290,u1_struct_0(A_291))
      | ~ r4_lattice3(A_291,B_288,a_2_1_lattice3(B_289,C_292))
      | ~ m1_subset_1(B_288,u1_struct_0(A_291))
      | ~ l3_lattices(A_291)
      | v2_struct_0(A_291)
      | ~ r3_lattice3(B_289,D_290,C_292)
      | ~ m1_subset_1(D_290,u1_struct_0(B_289))
      | ~ l3_lattices(B_289)
      | v2_struct_0(B_289) ) ),
    inference(resolution,[status(thm)],[c_28,c_149])).

tff(c_1021,plain,(
    ! [B_288,B_289,C_292] :
      ( r1_lattices('#skF_7','#skF_8',B_288)
      | ~ r4_lattice3('#skF_7',B_288,a_2_1_lattice3(B_289,C_292))
      | ~ m1_subset_1(B_288,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r3_lattice3(B_289,'#skF_8',C_292)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_289))
      | ~ l3_lattices(B_289)
      | v2_struct_0(B_289) ) ),
    inference(resolution,[status(thm)],[c_64,c_1007])).

tff(c_1030,plain,(
    ! [B_288,B_289,C_292] :
      ( r1_lattices('#skF_7','#skF_8',B_288)
      | ~ r4_lattice3('#skF_7',B_288,a_2_1_lattice3(B_289,C_292))
      | ~ m1_subset_1(B_288,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ r3_lattice3(B_289,'#skF_8',C_292)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_289))
      | ~ l3_lattices(B_289)
      | v2_struct_0(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1021])).

tff(c_1031,plain,(
    ! [B_288,B_289,C_292] :
      ( r1_lattices('#skF_7','#skF_8',B_288)
      | ~ r4_lattice3('#skF_7',B_288,a_2_1_lattice3(B_289,C_292))
      | ~ m1_subset_1(B_288,u1_struct_0('#skF_7'))
      | ~ r3_lattice3(B_289,'#skF_8',C_292)
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_289))
      | ~ l3_lattices(B_289)
      | v2_struct_0(B_289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1030])).

tff(c_9449,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ r3_lattice3('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9424,c_1031])).

tff(c_9492,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_9366,c_9449])).

tff(c_9493,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_3'('#skF_7',a_2_1_lattice3('#skF_7','#skF_9'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9492])).

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

tff(c_9542,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | ~ r4_lattice3('#skF_7','#skF_8',a_2_1_lattice3('#skF_7','#skF_9'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ v4_lattice3('#skF_7')
    | ~ v10_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9493,c_18])).

tff(c_9545,plain,
    ( k15_lattice3('#skF_7',a_2_1_lattice3('#skF_7','#skF_9')) = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_64,c_697,c_9542])).

tff(c_9547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9367,c_9545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:48:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/3.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/3.80  
% 10.97/3.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.17/3.80  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 11.17/3.80  
% 11.17/3.80  %Foreground sorts:
% 11.17/3.80  
% 11.17/3.80  
% 11.17/3.80  %Background operators:
% 11.17/3.80  
% 11.17/3.80  
% 11.17/3.80  %Foreground operators:
% 11.17/3.80  tff(l3_lattices, type, l3_lattices: $i > $o).
% 11.17/3.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.17/3.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.17/3.80  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 11.17/3.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.17/3.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.17/3.80  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.17/3.80  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 11.17/3.80  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 11.17/3.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.17/3.80  tff('#skF_7', type, '#skF_7': $i).
% 11.17/3.80  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 11.17/3.80  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.17/3.80  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 11.17/3.80  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 11.17/3.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.17/3.80  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 11.17/3.80  tff(v10_lattices, type, v10_lattices: $i > $o).
% 11.17/3.80  tff('#skF_9', type, '#skF_9': $i).
% 11.17/3.80  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 11.17/3.80  tff('#skF_8', type, '#skF_8': $i).
% 11.17/3.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.17/3.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.17/3.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.17/3.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.17/3.80  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 11.17/3.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.17/3.80  
% 11.17/3.83  tff(f_184, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 11.17/3.83  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 11.17/3.83  tff(f_103, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 11.17/3.83  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 11.17/3.83  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 11.17/3.83  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 11.17/3.83  tff(f_121, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 11.17/3.83  tff(f_164, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 11.17/3.83  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_58, plain, (k16_lattice3('#skF_7', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_70, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_68, plain, (v4_lattice3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_66, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_60, plain, (r3_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_50, plain, (![A_69, B_81, C_87]: (r3_lattice3(A_69, '#skF_6'(A_69, B_81, C_87), C_87) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.17/3.83  tff(c_52, plain, (![A_69, B_81, C_87]: (m1_subset_1('#skF_6'(A_69, B_81, C_87), u1_struct_0(A_69)) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.17/3.83  tff(c_28, plain, (![D_62, B_58, C_59]: (r2_hidden(D_62, a_2_1_lattice3(B_58, C_59)) | ~r3_lattice3(B_58, D_62, C_59) | ~m1_subset_1(D_62, u1_struct_0(B_58)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.17/3.83  tff(c_361, plain, (![A_209, B_210, C_211]: (r3_lattice3(A_209, '#skF_6'(A_209, B_210, C_211), C_211) | k16_lattice3(A_209, C_211)=B_210 | ~r3_lattice3(A_209, B_210, C_211) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l3_lattices(A_209) | ~v4_lattice3(A_209) | ~v10_lattices(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.17/3.83  tff(c_76, plain, (![D_111, B_112, C_113]: (r2_hidden(D_111, a_2_1_lattice3(B_112, C_113)) | ~r3_lattice3(B_112, D_111, C_113) | ~m1_subset_1(D_111, u1_struct_0(B_112)) | ~l3_lattices(B_112) | v2_struct_0(B_112))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.17/3.83  tff(c_32, plain, (![A_57, B_58, C_59]: ('#skF_4'(A_57, B_58, C_59)=A_57 | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.17/3.83  tff(c_80, plain, (![D_111, B_112, C_113]: ('#skF_4'(D_111, B_112, C_113)=D_111 | ~r3_lattice3(B_112, D_111, C_113) | ~m1_subset_1(D_111, u1_struct_0(B_112)) | ~l3_lattices(B_112) | v2_struct_0(B_112))), inference(resolution, [status(thm)], [c_76, c_32])).
% 11.17/3.83  tff(c_2114, plain, (![A_406, B_407, C_408]: ('#skF_4'('#skF_6'(A_406, B_407, C_408), A_406, C_408)='#skF_6'(A_406, B_407, C_408) | ~m1_subset_1('#skF_6'(A_406, B_407, C_408), u1_struct_0(A_406)) | k16_lattice3(A_406, C_408)=B_407 | ~r3_lattice3(A_406, B_407, C_408) | ~m1_subset_1(B_407, u1_struct_0(A_406)) | ~l3_lattices(A_406) | ~v4_lattice3(A_406) | ~v10_lattices(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_361, c_80])).
% 11.17/3.83  tff(c_2118, plain, (![A_409, B_410, C_411]: ('#skF_4'('#skF_6'(A_409, B_410, C_411), A_409, C_411)='#skF_6'(A_409, B_410, C_411) | k16_lattice3(A_409, C_411)=B_410 | ~r3_lattice3(A_409, B_410, C_411) | ~m1_subset_1(B_410, u1_struct_0(A_409)) | ~l3_lattices(A_409) | ~v4_lattice3(A_409) | ~v10_lattices(A_409) | v2_struct_0(A_409))), inference(resolution, [status(thm)], [c_52, c_2114])).
% 11.17/3.83  tff(c_2132, plain, (![C_411]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_411), '#skF_7', C_411)='#skF_6'('#skF_7', '#skF_8', C_411) | k16_lattice3('#skF_7', C_411)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_411) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_2118])).
% 11.17/3.83  tff(c_2141, plain, (![C_411]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_411), '#skF_7', C_411)='#skF_6'('#skF_7', '#skF_8', C_411) | k16_lattice3('#skF_7', C_411)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_411) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2132])).
% 11.17/3.83  tff(c_2143, plain, (![C_412]: ('#skF_4'('#skF_6'('#skF_7', '#skF_8', C_412), '#skF_7', C_412)='#skF_6'('#skF_7', '#skF_8', C_412) | k16_lattice3('#skF_7', C_412)='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', C_412))), inference(negUnitSimplification, [status(thm)], [c_72, c_2141])).
% 11.17/3.83  tff(c_30, plain, (![B_58, A_57, C_59]: (r3_lattice3(B_58, '#skF_4'(A_57, B_58, C_59), C_59) | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.17/3.83  tff(c_34, plain, (![A_57, B_58, C_59]: (m1_subset_1('#skF_4'(A_57, B_58, C_59), u1_struct_0(B_58)) | ~r2_hidden(A_57, a_2_1_lattice3(B_58, C_59)) | ~l3_lattices(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.17/3.83  tff(c_62, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.17/3.83  tff(c_215, plain, (![A_169, B_170, D_171, C_172]: (r1_lattices(A_169, B_170, D_171) | ~r2_hidden(D_171, C_172) | ~m1_subset_1(D_171, u1_struct_0(A_169)) | ~r3_lattice3(A_169, B_170, C_172) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.17/3.83  tff(c_241, plain, (![A_176, B_177]: (r1_lattices(A_176, B_177, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0(A_176)) | ~r3_lattice3(A_176, B_177, '#skF_9') | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~l3_lattices(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_62, c_215])).
% 11.17/3.83  tff(c_243, plain, (![B_177]: (r1_lattices('#skF_7', B_177, '#skF_8') | ~r3_lattice3('#skF_7', B_177, '#skF_9') | ~m1_subset_1(B_177, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_241])).
% 11.17/3.83  tff(c_246, plain, (![B_177]: (r1_lattices('#skF_7', B_177, '#skF_8') | ~r3_lattice3('#skF_7', B_177, '#skF_9') | ~m1_subset_1(B_177, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_243])).
% 11.17/3.83  tff(c_248, plain, (![B_178]: (r1_lattices('#skF_7', B_178, '#skF_8') | ~r3_lattice3('#skF_7', B_178, '#skF_9') | ~m1_subset_1(B_178, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_246])).
% 11.17/3.83  tff(c_264, plain, (![A_57, C_59]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_9') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', C_59)) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_248])).
% 11.17/3.83  tff(c_282, plain, (![A_57, C_59]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_57, '#skF_7', C_59), '#skF_9') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', C_59)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_264])).
% 11.17/3.83  tff(c_288, plain, (![A_181, C_182]: (r1_lattices('#skF_7', '#skF_4'(A_181, '#skF_7', C_182), '#skF_8') | ~r3_lattice3('#skF_7', '#skF_4'(A_181, '#skF_7', C_182), '#skF_9') | ~r2_hidden(A_181, a_2_1_lattice3('#skF_7', C_182)))), inference(negUnitSimplification, [status(thm)], [c_72, c_282])).
% 11.17/3.83  tff(c_295, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_288])).
% 11.17/3.83  tff(c_300, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_295])).
% 11.17/3.83  tff(c_301, plain, (![A_57]: (r1_lattices('#skF_7', '#skF_4'(A_57, '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden(A_57, a_2_1_lattice3('#skF_7', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_72, c_300])).
% 11.17/3.83  tff(c_2166, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2143, c_301])).
% 11.17/3.83  tff(c_2190, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2166])).
% 11.17/3.83  tff(c_2191, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2190])).
% 11.17/3.83  tff(c_2199, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_2191])).
% 11.17/3.83  tff(c_2202, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_2199])).
% 11.17/3.83  tff(c_2205, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2202])).
% 11.17/3.83  tff(c_2206, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2205])).
% 11.17/3.83  tff(c_2216, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2206])).
% 11.17/3.83  tff(c_2219, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_2216])).
% 11.17/3.83  tff(c_2222, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_2219])).
% 11.17/3.83  tff(c_2224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_2222])).
% 11.17/3.83  tff(c_2225, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_2206])).
% 11.17/3.83  tff(c_2288, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_2225])).
% 11.17/3.83  tff(c_2291, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_2288])).
% 11.17/3.83  tff(c_2293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_2291])).
% 11.17/3.83  tff(c_2295, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_2191])).
% 11.17/3.83  tff(c_2304, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2295, c_32])).
% 11.17/3.83  tff(c_2313, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2304])).
% 11.17/3.83  tff(c_2314, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_2313])).
% 11.17/3.83  tff(c_2345, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2314, c_34])).
% 11.17/3.83  tff(c_2375, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2295, c_2345])).
% 11.17/3.83  tff(c_2376, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2375])).
% 11.17/3.83  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.17/3.83  tff(c_108, plain, (![A_120, B_121, C_122]: (r2_hidden('#skF_2'(A_120, B_121, C_122), C_122) | r4_lattice3(A_120, B_121, C_122) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l3_lattices(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.17/3.83  tff(c_591, plain, (![A_251, B_252, B_253, C_254]: ('#skF_4'('#skF_2'(A_251, B_252, a_2_1_lattice3(B_253, C_254)), B_253, C_254)='#skF_2'(A_251, B_252, a_2_1_lattice3(B_253, C_254)) | ~l3_lattices(B_253) | v2_struct_0(B_253) | r4_lattice3(A_251, B_252, a_2_1_lattice3(B_253, C_254)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_108, c_32])).
% 11.17/3.83  tff(c_598, plain, (![A_251, B_252]: (r1_lattices('#skF_7', '#skF_2'(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | r4_lattice3(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(superposition, [status(thm), theory('equality')], [c_591, c_301])).
% 11.17/3.83  tff(c_618, plain, (![A_251, B_252]: (r1_lattices('#skF_7', '#skF_2'(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7') | r4_lattice3(A_251, B_252, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_598])).
% 11.17/3.83  tff(c_676, plain, (![A_258, B_259]: (r1_lattices('#skF_7', '#skF_2'(A_258, B_259, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | ~r2_hidden('#skF_2'(A_258, B_259, a_2_1_lattice3('#skF_7', '#skF_9')), a_2_1_lattice3('#skF_7', '#skF_9')) | r4_lattice3(A_258, B_259, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_259, u1_struct_0(A_258)) | ~l3_lattices(A_258) | v2_struct_0(A_258))), inference(negUnitSimplification, [status(thm)], [c_72, c_618])).
% 11.17/3.83  tff(c_689, plain, (![A_260, B_261]: (r1_lattices('#skF_7', '#skF_2'(A_260, B_261, a_2_1_lattice3('#skF_7', '#skF_9')), '#skF_8') | r4_lattice3(A_260, B_261, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_261, u1_struct_0(A_260)) | ~l3_lattices(A_260) | v2_struct_0(A_260))), inference(resolution, [status(thm)], [c_14, c_676])).
% 11.17/3.83  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.17/3.83  tff(c_693, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_689, c_12])).
% 11.17/3.83  tff(c_696, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_693])).
% 11.17/3.83  tff(c_697, plain, (r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_696])).
% 11.17/3.83  tff(c_20, plain, (![A_45, B_52, C_53]: (r4_lattice3(A_45, '#skF_3'(A_45, B_52, C_53), B_52) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.17/3.83  tff(c_22, plain, (![A_45, B_52, C_53]: (m1_subset_1('#skF_3'(A_45, B_52, C_53), u1_struct_0(A_45)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.17/3.83  tff(c_36, plain, (![D_68, B_64, C_65]: (r2_hidden(D_68, a_2_2_lattice3(B_64, C_65)) | ~r4_lattice3(B_64, D_68, C_65) | ~m1_subset_1(D_68, u1_struct_0(B_64)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.17/3.83  tff(c_308, plain, (![A_186, B_187, C_188]: (r4_lattice3(A_186, '#skF_3'(A_186, B_187, C_188), B_187) | k15_lattice3(A_186, B_187)=C_188 | ~r4_lattice3(A_186, C_188, B_187) | ~m1_subset_1(C_188, u1_struct_0(A_186)) | ~v4_lattice3(A_186) | ~v10_lattices(A_186) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.17/3.83  tff(c_138, plain, (![D_148, B_149, C_150]: (r2_hidden(D_148, a_2_2_lattice3(B_149, C_150)) | ~r4_lattice3(B_149, D_148, C_150) | ~m1_subset_1(D_148, u1_struct_0(B_149)) | ~l3_lattices(B_149) | ~v4_lattice3(B_149) | ~v10_lattices(B_149) | v2_struct_0(B_149))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.17/3.83  tff(c_40, plain, (![A_63, B_64, C_65]: ('#skF_5'(A_63, B_64, C_65)=A_63 | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.17/3.83  tff(c_142, plain, (![D_148, B_149, C_150]: ('#skF_5'(D_148, B_149, C_150)=D_148 | ~r4_lattice3(B_149, D_148, C_150) | ~m1_subset_1(D_148, u1_struct_0(B_149)) | ~l3_lattices(B_149) | ~v4_lattice3(B_149) | ~v10_lattices(B_149) | v2_struct_0(B_149))), inference(resolution, [status(thm)], [c_138, c_40])).
% 11.17/3.83  tff(c_2634, plain, (![A_424, B_425, C_426]: ('#skF_5'('#skF_3'(A_424, B_425, C_426), A_424, B_425)='#skF_3'(A_424, B_425, C_426) | ~m1_subset_1('#skF_3'(A_424, B_425, C_426), u1_struct_0(A_424)) | k15_lattice3(A_424, B_425)=C_426 | ~r4_lattice3(A_424, C_426, B_425) | ~m1_subset_1(C_426, u1_struct_0(A_424)) | ~v4_lattice3(A_424) | ~v10_lattices(A_424) | ~l3_lattices(A_424) | v2_struct_0(A_424))), inference(resolution, [status(thm)], [c_308, c_142])).
% 11.17/3.83  tff(c_2920, plain, (![A_447, B_448, C_449]: ('#skF_5'('#skF_3'(A_447, B_448, C_449), A_447, B_448)='#skF_3'(A_447, B_448, C_449) | k15_lattice3(A_447, B_448)=C_449 | ~r4_lattice3(A_447, C_449, B_448) | ~m1_subset_1(C_449, u1_struct_0(A_447)) | ~v4_lattice3(A_447) | ~v10_lattices(A_447) | ~l3_lattices(A_447) | v2_struct_0(A_447))), inference(resolution, [status(thm)], [c_22, c_2634])).
% 11.17/3.83  tff(c_2938, plain, (![B_448]: ('#skF_5'('#skF_3'('#skF_7', B_448, '#skF_8'), '#skF_7', B_448)='#skF_3'('#skF_7', B_448, '#skF_8') | k15_lattice3('#skF_7', B_448)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_448) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_2920])).
% 11.17/3.83  tff(c_2952, plain, (![B_448]: ('#skF_5'('#skF_3'('#skF_7', B_448, '#skF_8'), '#skF_7', B_448)='#skF_3'('#skF_7', B_448, '#skF_8') | k15_lattice3('#skF_7', B_448)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_448) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_2938])).
% 11.17/3.83  tff(c_2953, plain, (![B_448]: ('#skF_5'('#skF_3'('#skF_7', B_448, '#skF_8'), '#skF_7', B_448)='#skF_3'('#skF_7', B_448, '#skF_8') | k15_lattice3('#skF_7', B_448)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_448))), inference(negUnitSimplification, [status(thm)], [c_72, c_2952])).
% 11.17/3.83  tff(c_38, plain, (![B_64, A_63, C_65]: (r4_lattice3(B_64, '#skF_5'(A_63, B_64, C_65), C_65) | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.17/3.83  tff(c_2342, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2314, c_30])).
% 11.17/3.83  tff(c_2372, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2295, c_2342])).
% 11.17/3.83  tff(c_2373, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_2372])).
% 11.17/3.83  tff(c_2117, plain, (![A_69, B_81, C_87]: ('#skF_4'('#skF_6'(A_69, B_81, C_87), A_69, C_87)='#skF_6'(A_69, B_81, C_87) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_52, c_2114])).
% 11.17/3.83  tff(c_2405, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2376, c_2117])).
% 11.17/3.83  tff(c_2426, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_87) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2405])).
% 11.17/3.83  tff(c_3146, plain, (![C_462]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_462), '#skF_7', C_462)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_462) | k16_lattice3('#skF_7', C_462)='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), C_462))), inference(negUnitSimplification, [status(thm)], [c_72, c_2426])).
% 11.17/3.83  tff(c_3173, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3146, c_301])).
% 11.17/3.83  tff(c_3197, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_3173])).
% 11.17/3.83  tff(c_3205, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_3197])).
% 11.17/3.83  tff(c_3208, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_3205])).
% 11.17/3.83  tff(c_3211, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3208])).
% 11.17/3.83  tff(c_3212, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3211])).
% 11.17/3.83  tff(c_3213, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_3212])).
% 11.17/3.83  tff(c_3216, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_3213])).
% 11.17/3.83  tff(c_3219, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2376, c_2373, c_3216])).
% 11.17/3.83  tff(c_3220, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_3219])).
% 11.17/3.83  tff(c_3233, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3220, c_58])).
% 11.17/3.83  tff(c_54, plain, (![A_91, C_97, B_95]: (r3_lattices(A_91, k16_lattice3(A_91, C_97), B_95) | ~r2_hidden(B_95, C_97) | ~m1_subset_1(B_95, u1_struct_0(A_91)) | ~l3_lattices(A_91) | ~v4_lattice3(A_91) | ~v10_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.17/3.83  tff(c_3239, plain, (![B_95]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_95) | ~r2_hidden(B_95, '#skF_9') | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3220, c_54])).
% 11.17/3.83  tff(c_3248, plain, (![B_95]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_95) | ~r2_hidden(B_95, '#skF_9') | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3239])).
% 11.17/3.83  tff(c_3254, plain, (![B_467]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_467) | ~r2_hidden(B_467, '#skF_9') | ~m1_subset_1(B_467, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_3248])).
% 11.17/3.83  tff(c_48, plain, (![A_69, B_81, C_87]: (~r3_lattices(A_69, '#skF_6'(A_69, B_81, C_87), B_81) | k16_lattice3(A_69, C_87)=B_81 | ~r3_lattice3(A_69, B_81, C_87) | ~m1_subset_1(B_81, u1_struct_0(A_69)) | ~l3_lattices(A_69) | ~v4_lattice3(A_69) | ~v10_lattices(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.17/3.83  tff(c_3258, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3254, c_48])).
% 11.17/3.83  tff(c_3261, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_70, c_68, c_66, c_60, c_3220, c_3258])).
% 11.17/3.83  tff(c_3263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3233, c_3261])).
% 11.17/3.83  tff(c_3264, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_3212])).
% 11.17/3.83  tff(c_3325, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_3264])).
% 11.17/3.83  tff(c_3328, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2376, c_2373, c_3325])).
% 11.17/3.83  tff(c_3329, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_3328])).
% 11.17/3.83  tff(c_3331, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_58])).
% 11.17/3.83  tff(c_3337, plain, (![B_95]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_95) | ~r2_hidden(B_95, '#skF_9') | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3329, c_54])).
% 11.17/3.83  tff(c_3346, plain, (![B_95]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_95) | ~r2_hidden(B_95, '#skF_9') | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3337])).
% 11.17/3.83  tff(c_3352, plain, (![B_471]: (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), B_471) | ~r2_hidden(B_471, '#skF_9') | ~m1_subset_1(B_471, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_3346])).
% 11.17/3.83  tff(c_3356, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r2_hidden('#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3352, c_48])).
% 11.17/3.83  tff(c_3359, plain, ('#skF_6'('#skF_7', '#skF_8', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_70, c_68, c_66, c_60, c_3329, c_3356])).
% 11.17/3.83  tff(c_3361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3331, c_3359])).
% 11.17/3.83  tff(c_3363, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_3197])).
% 11.17/3.83  tff(c_3383, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3363, c_32])).
% 11.17/3.83  tff(c_3392, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3383])).
% 11.17/3.83  tff(c_3393, plain, ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_7', '#skF_9')='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_3392])).
% 11.17/3.83  tff(c_3425, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3393, c_34])).
% 11.17/3.83  tff(c_3454, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3363, c_3425])).
% 11.17/3.83  tff(c_3455, plain, (m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3454])).
% 11.17/3.83  tff(c_3422, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3393, c_30])).
% 11.17/3.83  tff(c_3451, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3363, c_3422])).
% 11.17/3.83  tff(c_3452, plain, (r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_3451])).
% 11.17/3.83  tff(c_3475, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3455, c_2117])).
% 11.17/3.83  tff(c_3500, plain, (![C_87]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87), '#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | k16_lattice3('#skF_7', C_87)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_87) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3475])).
% 11.17/3.83  tff(c_6231, plain, (![C_717]: ('#skF_4'('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_717), '#skF_7', C_717)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_717) | k16_lattice3('#skF_7', C_717)='#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), C_717))), inference(negUnitSimplification, [status(thm)], [c_72, c_3500])).
% 11.17/3.83  tff(c_6268, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6231, c_301])).
% 11.17/3.83  tff(c_6298, plain, (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9')) | '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3452, c_6268])).
% 11.17/3.83  tff(c_6306, plain, (~r2_hidden('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_6298])).
% 11.17/3.83  tff(c_6309, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_6306])).
% 11.17/3.83  tff(c_6312, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6309])).
% 11.17/3.83  tff(c_6313, plain, (~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_6312])).
% 11.17/3.83  tff(c_6314, plain, (~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_6313])).
% 11.17/3.83  tff(c_6317, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | ~r3_lattice3('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), '#skF_9') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_6314])).
% 11.17/3.83  tff(c_6320, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3455, c_3452, c_6317])).
% 11.17/3.83  tff(c_6321, plain, ('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9')=k16_lattice3('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_72, c_6320])).
% 11.17/3.83  tff(c_10, plain, (![A_23, D_44, B_35, C_41]: (r1_lattices(A_23, D_44, B_35) | ~r2_hidden(D_44, C_41) | ~m1_subset_1(D_44, u1_struct_0(A_23)) | ~r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.17/3.83  tff(c_3839, plain, (![A_514, B_515]: (r1_lattices(A_514, '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_515) | ~m1_subset_1('#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), u1_struct_0(A_514)) | ~r4_lattice3(A_514, B_515, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_515, u1_struct_0(A_514)) | ~l3_lattices(A_514) | v2_struct_0(A_514))), inference(resolution, [status(thm)], [c_3363, c_10])).
% 11.17/3.83  tff(c_3841, plain, (![B_515]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_515) | ~r4_lattice3('#skF_7', B_515, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_515, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3455, c_3839])).
% 11.17/3.83  tff(c_3847, plain, (![B_515]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_515) | ~r4_lattice3('#skF_7', B_515, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_515, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3841])).
% 11.17/3.83  tff(c_3848, plain, (![B_515]: (r1_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_9'), B_515) | ~r4_lattice3('#skF_7', B_515, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_515, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_3847])).
% 11.17/3.83  tff(c_6770, plain, (![B_732]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), B_732) | ~r4_lattice3('#skF_7', B_732, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_732, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_6321, c_3848])).
% 11.17/3.83  tff(c_6785, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_6770])).
% 11.17/3.83  tff(c_6799, plain, (![A_63]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_63, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_63, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_6785])).
% 11.17/3.83  tff(c_7300, plain, (![A_771]: (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_5'(A_771, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | ~m1_subset_1('#skF_5'(A_771, '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden(A_771, a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_6799])).
% 11.17/3.83  tff(c_7332, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2953, c_7300])).
% 11.17/3.83  tff(c_7373, plain, (r1_lattices('#skF_7', k16_lattice3('#skF_7', '#skF_9'), '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_5'('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), '#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_697, c_7332])).
% 11.17/3.83  tff(c_8609, plain, (~r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_7373])).
% 11.17/3.83  tff(c_8612, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_8609])).
% 11.17/3.83  tff(c_8615, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_8612])).
% 11.17/3.83  tff(c_8616, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_8615])).
% 11.17/3.83  tff(c_8617, plain, (~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_8616])).
% 11.17/3.83  tff(c_8620, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_8617])).
% 11.17/3.83  tff(c_8623, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_697, c_8620])).
% 11.17/3.83  tff(c_8624, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_8623])).
% 11.17/3.83  tff(c_56, plain, (![A_91, B_95, C_97]: (r3_lattices(A_91, B_95, k15_lattice3(A_91, C_97)) | ~r2_hidden(B_95, C_97) | ~m1_subset_1(B_95, u1_struct_0(A_91)) | ~l3_lattices(A_91) | ~v4_lattice3(A_91) | ~v10_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.17/3.83  tff(c_8634, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8624, c_56])).
% 11.17/3.83  tff(c_8646, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_8634])).
% 11.17/3.83  tff(c_8694, plain, (![B_910]: (r3_lattices('#skF_7', B_910, '#skF_8') | ~r2_hidden(B_910, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_910, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_8646])).
% 11.17/3.83  tff(c_8700, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2295, c_8694])).
% 11.17/3.83  tff(c_8718, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_8700])).
% 11.17/3.83  tff(c_8727, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8718, c_48])).
% 11.17/3.83  tff(c_8730, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_8727])).
% 11.17/3.83  tff(c_8732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_8730])).
% 11.17/3.83  tff(c_8733, plain, (~r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_8616])).
% 11.17/3.83  tff(c_8874, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_8733])).
% 11.17/3.83  tff(c_8877, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_697, c_8874])).
% 11.17/3.83  tff(c_8878, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_8877])).
% 11.17/3.83  tff(c_8888, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8878, c_56])).
% 11.17/3.83  tff(c_8900, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_8888])).
% 11.17/3.83  tff(c_8906, plain, (![B_914]: (r3_lattices('#skF_7', B_914, '#skF_8') | ~r2_hidden(B_914, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_914, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_8900])).
% 11.17/3.83  tff(c_8912, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2295, c_8906])).
% 11.17/3.83  tff(c_8930, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_8912])).
% 11.17/3.83  tff(c_8981, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8930, c_48])).
% 11.17/3.83  tff(c_8984, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_8981])).
% 11.17/3.83  tff(c_8986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_8984])).
% 11.17/3.83  tff(c_8988, plain, (r2_hidden('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_2_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_7373])).
% 11.17/3.83  tff(c_2954, plain, (![B_450]: ('#skF_5'('#skF_3'('#skF_7', B_450, '#skF_8'), '#skF_7', B_450)='#skF_3'('#skF_7', B_450, '#skF_8') | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(negUnitSimplification, [status(thm)], [c_72, c_2952])).
% 11.17/3.83  tff(c_42, plain, (![A_63, B_64, C_65]: (m1_subset_1('#skF_5'(A_63, B_64, C_65), u1_struct_0(B_64)) | ~r2_hidden(A_63, a_2_2_lattice3(B_64, C_65)) | ~l3_lattices(B_64) | ~v4_lattice3(B_64) | ~v10_lattices(B_64) | v2_struct_0(B_64))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.17/3.83  tff(c_2990, plain, (![B_450]: (m1_subset_1('#skF_3'('#skF_7', B_450, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_42])).
% 11.17/3.83  tff(c_3007, plain, (![B_450]: (m1_subset_1('#skF_3'('#skF_7', B_450, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2990])).
% 11.17/3.83  tff(c_3008, plain, (![B_450]: (m1_subset_1('#skF_3'('#skF_7', B_450, '#skF_8'), u1_struct_0('#skF_7')) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(negUnitSimplification, [status(thm)], [c_72, c_3007])).
% 11.17/3.83  tff(c_9000, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_8988, c_3008])).
% 11.17/3.83  tff(c_9021, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_697, c_9000])).
% 11.17/3.83  tff(c_9032, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(splitLeft, [status(thm)], [c_9021])).
% 11.17/3.83  tff(c_9128, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9032, c_56])).
% 11.17/3.83  tff(c_9140, plain, (![B_95]: (r3_lattices('#skF_7', B_95, '#skF_8') | ~r2_hidden(B_95, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_95, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_9128])).
% 11.17/3.83  tff(c_9327, plain, (![B_927]: (r3_lattices('#skF_7', B_927, '#skF_8') | ~r2_hidden(B_927, a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1(B_927, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_9140])).
% 11.17/3.83  tff(c_9333, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2295, c_9327])).
% 11.17/3.83  tff(c_9351, plain, (r3_lattices('#skF_7', '#skF_6'('#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_9333])).
% 11.17/3.83  tff(c_9360, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9351, c_48])).
% 11.17/3.83  tff(c_9363, plain, (k16_lattice3('#skF_7', '#skF_9')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_60, c_9360])).
% 11.17/3.83  tff(c_9365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_9363])).
% 11.17/3.83  tff(c_9367, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))!='#skF_8'), inference(splitRight, [status(thm)], [c_9021])).
% 11.17/3.83  tff(c_9366, plain, (m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_9021])).
% 11.17/3.83  tff(c_2993, plain, (![B_450]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_450, '#skF_8'), B_450) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | ~l3_lattices('#skF_7') | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_38])).
% 11.17/3.83  tff(c_3010, plain, (![B_450]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_450, '#skF_8'), B_450) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | v2_struct_0('#skF_7') | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2993])).
% 11.17/3.83  tff(c_3011, plain, (![B_450]: (r4_lattice3('#skF_7', '#skF_3'('#skF_7', B_450, '#skF_8'), B_450) | ~r2_hidden('#skF_3'('#skF_7', B_450, '#skF_8'), a_2_2_lattice3('#skF_7', B_450)) | k15_lattice3('#skF_7', B_450)='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', B_450))), inference(negUnitSimplification, [status(thm)], [c_72, c_3010])).
% 11.17/3.83  tff(c_8997, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_8988, c_3011])).
% 11.17/3.83  tff(c_9018, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9')) | k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_697, c_8997])).
% 11.17/3.83  tff(c_9424, plain, (r4_lattice3('#skF_7', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), a_2_1_lattice3('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_9367, c_9018])).
% 11.17/3.83  tff(c_149, plain, (![A_160, D_161, B_162, C_163]: (r1_lattices(A_160, D_161, B_162) | ~r2_hidden(D_161, C_163) | ~m1_subset_1(D_161, u1_struct_0(A_160)) | ~r4_lattice3(A_160, B_162, C_163) | ~m1_subset_1(B_162, u1_struct_0(A_160)) | ~l3_lattices(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.17/3.83  tff(c_1007, plain, (![B_289, A_291, D_290, C_292, B_288]: (r1_lattices(A_291, D_290, B_288) | ~m1_subset_1(D_290, u1_struct_0(A_291)) | ~r4_lattice3(A_291, B_288, a_2_1_lattice3(B_289, C_292)) | ~m1_subset_1(B_288, u1_struct_0(A_291)) | ~l3_lattices(A_291) | v2_struct_0(A_291) | ~r3_lattice3(B_289, D_290, C_292) | ~m1_subset_1(D_290, u1_struct_0(B_289)) | ~l3_lattices(B_289) | v2_struct_0(B_289))), inference(resolution, [status(thm)], [c_28, c_149])).
% 11.17/3.83  tff(c_1021, plain, (![B_288, B_289, C_292]: (r1_lattices('#skF_7', '#skF_8', B_288) | ~r4_lattice3('#skF_7', B_288, a_2_1_lattice3(B_289, C_292)) | ~m1_subset_1(B_288, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7') | ~r3_lattice3(B_289, '#skF_8', C_292) | ~m1_subset_1('#skF_8', u1_struct_0(B_289)) | ~l3_lattices(B_289) | v2_struct_0(B_289))), inference(resolution, [status(thm)], [c_64, c_1007])).
% 11.17/3.83  tff(c_1030, plain, (![B_288, B_289, C_292]: (r1_lattices('#skF_7', '#skF_8', B_288) | ~r4_lattice3('#skF_7', B_288, a_2_1_lattice3(B_289, C_292)) | ~m1_subset_1(B_288, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~r3_lattice3(B_289, '#skF_8', C_292) | ~m1_subset_1('#skF_8', u1_struct_0(B_289)) | ~l3_lattices(B_289) | v2_struct_0(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1021])).
% 11.17/3.83  tff(c_1031, plain, (![B_288, B_289, C_292]: (r1_lattices('#skF_7', '#skF_8', B_288) | ~r4_lattice3('#skF_7', B_288, a_2_1_lattice3(B_289, C_292)) | ~m1_subset_1(B_288, u1_struct_0('#skF_7')) | ~r3_lattice3(B_289, '#skF_8', C_292) | ~m1_subset_1('#skF_8', u1_struct_0(B_289)) | ~l3_lattices(B_289) | v2_struct_0(B_289))), inference(negUnitSimplification, [status(thm)], [c_72, c_1030])).
% 11.17/3.83  tff(c_9449, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | ~m1_subset_1('#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'), u1_struct_0('#skF_7')) | ~r3_lattice3('#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9424, c_1031])).
% 11.17/3.83  tff(c_9492, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_9366, c_9449])).
% 11.17/3.83  tff(c_9493, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_3'('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_9492])).
% 11.17/3.83  tff(c_18, plain, (![A_45, C_53, B_52]: (~r1_lattices(A_45, C_53, '#skF_3'(A_45, B_52, C_53)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.17/3.83  tff(c_9542, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | ~r4_lattice3('#skF_7', '#skF_8', a_2_1_lattice3('#skF_7', '#skF_9')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~v4_lattice3('#skF_7') | ~v10_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9493, c_18])).
% 11.17/3.83  tff(c_9545, plain, (k15_lattice3('#skF_7', a_2_1_lattice3('#skF_7', '#skF_9'))='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_64, c_697, c_9542])).
% 11.17/3.83  tff(c_9547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_9367, c_9545])).
% 11.17/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.17/3.83  
% 11.17/3.83  Inference rules
% 11.17/3.83  ----------------------
% 11.17/3.83  #Ref     : 0
% 11.17/3.83  #Sup     : 1723
% 11.17/3.83  #Fact    : 0
% 11.17/3.83  #Define  : 0
% 11.17/3.83  #Split   : 23
% 11.17/3.83  #Chain   : 0
% 11.17/3.83  #Close   : 0
% 11.17/3.83  
% 11.17/3.83  Ordering : KBO
% 11.17/3.83  
% 11.17/3.83  Simplification rules
% 11.17/3.83  ----------------------
% 11.17/3.83  #Subsume      : 294
% 11.17/3.83  #Demod        : 2922
% 11.17/3.83  #Tautology    : 368
% 11.17/3.83  #SimpNegUnit  : 831
% 11.17/3.83  #BackRed      : 34
% 11.17/3.83  
% 11.17/3.83  #Partial instantiations: 0
% 11.17/3.83  #Strategies tried      : 1
% 11.17/3.83  
% 11.17/3.83  Timing (in seconds)
% 11.17/3.83  ----------------------
% 11.17/3.83  Preprocessing        : 0.36
% 11.17/3.83  Parsing              : 0.20
% 11.17/3.84  CNF conversion       : 0.03
% 11.17/3.84  Main loop            : 2.61
% 11.17/3.84  Inferencing          : 0.90
% 11.17/3.84  Reduction            : 0.83
% 11.17/3.84  Demodulation         : 0.58
% 11.17/3.84  BG Simplification    : 0.09
% 11.17/3.84  Subsumption          : 0.63
% 11.17/3.84  Abstraction          : 0.12
% 11.17/3.84  MUC search           : 0.00
% 11.17/3.84  Cooper               : 0.00
% 11.17/3.84  Total                : 3.04
% 11.17/3.84  Index Insertion      : 0.00
% 11.17/3.84  Index Deletion       : 0.00
% 11.17/3.84  Index Matching       : 0.00
% 11.17/3.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
