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
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 431 expanded)
%              Number of leaves         :   43 ( 167 expanded)
%              Depth                    :   21
%              Number of atoms          :  360 (1661 expanded)
%              Number of equality atoms :   44 ( 209 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r4_lattice3(A,B,C) )
               => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

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

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_83,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

tff(f_102,axiom,(
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

tff(f_152,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_171,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_68,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    k15_lattice3('#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_62,plain,(
    r4_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_24,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_2'(A_9),u1_struct_0(A_9))
      | v9_lattices(A_9)
      | ~ l3_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_61] :
      ( l1_lattices(A_61)
      | ~ l3_lattices(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_185,plain,(
    ! [A_94,C_95,B_96] :
      ( k2_lattices(A_94,C_95,B_96) = k2_lattices(A_94,B_96,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(A_94))
      | ~ m1_subset_1(B_96,u1_struct_0(A_94))
      | ~ v6_lattices(A_94)
      | ~ l1_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_197,plain,(
    ! [B_96] :
      ( k2_lattices('#skF_6',B_96,'#skF_7') = k2_lattices('#skF_6','#skF_7',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_185])).

tff(c_205,plain,(
    ! [B_96] :
      ( k2_lattices('#skF_6',B_96,'#skF_7') = k2_lattices('#skF_6','#skF_7',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_197])).

tff(c_206,plain,(
    ! [B_96] :
      ( k2_lattices('#skF_6',B_96,'#skF_7') = k2_lattices('#skF_6','#skF_7',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_205])).

tff(c_207,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_232,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_235,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_232])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_235])).

tff(c_240,plain,(
    ! [B_100] :
      ( k2_lattices('#skF_6',B_100,'#skF_7') = k2_lattices('#skF_6','#skF_7',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_244,plain,
    ( k2_lattices('#skF_6','#skF_2'('#skF_6'),'#skF_7') = k2_lattices('#skF_6','#skF_7','#skF_2'('#skF_6'))
    | v9_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_266,plain,
    ( k2_lattices('#skF_6','#skF_2'('#skF_6'),'#skF_7') = k2_lattices('#skF_6','#skF_7','#skF_2'('#skF_6'))
    | v9_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_244])).

tff(c_267,plain,
    ( k2_lattices('#skF_6','#skF_2'('#skF_6'),'#skF_7') = k2_lattices('#skF_6','#skF_7','#skF_2'('#skF_6'))
    | v9_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_266])).

tff(c_286,plain,(
    v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_70,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_239,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_387,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_399,plain,(
    ! [B_114] :
      ( r3_lattices('#skF_6',B_114,'#skF_7')
      | ~ r1_lattices('#skF_6',B_114,'#skF_7')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_387])).

tff(c_407,plain,(
    ! [B_114] :
      ( r3_lattices('#skF_6',B_114,'#skF_7')
      | ~ r1_lattices('#skF_6',B_114,'#skF_7')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_286,c_68,c_399])).

tff(c_408,plain,(
    ! [B_114] :
      ( r3_lattices('#skF_6',B_114,'#skF_7')
      | ~ r1_lattices('#skF_6',B_114,'#skF_7')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_6'))
      | ~ v8_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_407])).

tff(c_409,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_412,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_409])).

tff(c_415,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_415])).

tff(c_419,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_75,plain,(
    ! [A_60] :
      ( l2_lattices(A_60)
      | ~ l3_lattices(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    l2_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_54,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k15_lattice3(A_47,B_48),u1_struct_0(A_47))
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    ! [A_49,B_53,C_55] :
      ( r3_lattices(A_49,B_53,k15_lattice3(A_49,C_55))
      | ~ r2_hidden(B_53,C_55)
      | ~ m1_subset_1(B_53,u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_358,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_lattices(A_106,B_107,C_108)
      | ~ r3_lattices(A_106,B_107,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l3_lattices(A_106)
      | ~ v9_lattices(A_106)
      | ~ v8_lattices(A_106)
      | ~ v6_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_798,plain,(
    ! [A_177,B_178,C_179] :
      ( r1_lattices(A_177,B_178,k15_lattice3(A_177,C_179))
      | ~ m1_subset_1(k15_lattice3(A_177,C_179),u1_struct_0(A_177))
      | ~ v9_lattices(A_177)
      | ~ v8_lattices(A_177)
      | ~ v6_lattices(A_177)
      | ~ r2_hidden(B_178,C_179)
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l3_lattices(A_177)
      | ~ v4_lattice3(A_177)
      | ~ v10_lattices(A_177)
      | v2_struct_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_58,c_358])).

tff(c_802,plain,(
    ! [A_180,B_181,B_182] :
      ( r1_lattices(A_180,B_181,k15_lattice3(A_180,B_182))
      | ~ v9_lattices(A_180)
      | ~ v8_lattices(A_180)
      | ~ v6_lattices(A_180)
      | ~ r2_hidden(B_181,B_182)
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ v4_lattice3(A_180)
      | ~ v10_lattices(A_180)
      | ~ l3_lattices(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_54,c_798])).

tff(c_18,plain,(
    ! [A_2,B_6,C_8] :
      ( k1_lattices(A_2,B_6,C_8) = C_8
      | ~ r1_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_881,plain,(
    ! [A_201,B_202,B_203] :
      ( k1_lattices(A_201,B_202,k15_lattice3(A_201,B_203)) = k15_lattice3(A_201,B_203)
      | ~ m1_subset_1(k15_lattice3(A_201,B_203),u1_struct_0(A_201))
      | ~ l2_lattices(A_201)
      | ~ v9_lattices(A_201)
      | ~ v8_lattices(A_201)
      | ~ v6_lattices(A_201)
      | ~ r2_hidden(B_202,B_203)
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ v4_lattice3(A_201)
      | ~ v10_lattices(A_201)
      | ~ l3_lattices(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_802,c_18])).

tff(c_910,plain,(
    ! [A_208,B_209,B_210] :
      ( k1_lattices(A_208,B_209,k15_lattice3(A_208,B_210)) = k15_lattice3(A_208,B_210)
      | ~ l2_lattices(A_208)
      | ~ v9_lattices(A_208)
      | ~ v8_lattices(A_208)
      | ~ v6_lattices(A_208)
      | ~ r2_hidden(B_209,B_210)
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ v4_lattice3(A_208)
      | ~ v10_lattices(A_208)
      | ~ l3_lattices(A_208)
      | v2_struct_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_54,c_881])).

tff(c_924,plain,(
    ! [B_210] :
      ( k1_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_210)) = k15_lattice3('#skF_6',B_210)
      | ~ l2_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | ~ r2_hidden('#skF_7',B_210)
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_910])).

tff(c_933,plain,(
    ! [B_210] :
      ( k1_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_210)) = k15_lattice3('#skF_6',B_210)
      | ~ r2_hidden('#skF_7',B_210)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_70,c_239,c_419,c_286,c_79,c_924])).

tff(c_935,plain,(
    ! [B_211] :
      ( k1_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_211)) = k15_lattice3('#skF_6',B_211)
      | ~ r2_hidden('#skF_7',B_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_933])).

tff(c_297,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_lattices(A_102,B_103,k1_lattices(A_102,B_103,C_104)) = B_103
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ v9_lattices(A_102)
      | ~ l3_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_314,plain,(
    ! [A_47,B_103,B_48] :
      ( k2_lattices(A_47,B_103,k1_lattices(A_47,B_103,k15_lattice3(A_47,B_48))) = B_103
      | ~ m1_subset_1(B_103,u1_struct_0(A_47))
      | ~ v9_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_54,c_297])).

tff(c_941,plain,(
    ! [B_211] :
      ( k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_211)) = '#skF_7'
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_7',B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_314])).

tff(c_947,plain,(
    ! [B_211] :
      ( k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_211)) = '#skF_7'
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_7',B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_286,c_66,c_941])).

tff(c_950,plain,(
    ! [B_212] :
      ( k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_212)) = '#skF_7'
      | ~ r2_hidden('#skF_7',B_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_947])).

tff(c_260,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7') = k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_48))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_240])).

tff(c_282,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7') = k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_48))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_260])).

tff(c_283,plain,(
    ! [B_48] : k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7') = k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_48)) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_282])).

tff(c_745,plain,(
    ! [A_157,B_158,D_159] :
      ( r1_lattices(A_157,k15_lattice3(A_157,B_158),D_159)
      | ~ r4_lattice3(A_157,D_159,B_158)
      | ~ m1_subset_1(D_159,u1_struct_0(A_157))
      | ~ m1_subset_1(k15_lattice3(A_157,B_158),u1_struct_0(A_157))
      | ~ v4_lattice3(A_157)
      | ~ v10_lattices(A_157)
      | ~ l3_lattices(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_749,plain,(
    ! [A_160,B_161,D_162] :
      ( r1_lattices(A_160,k15_lattice3(A_160,B_161),D_162)
      | ~ r4_lattice3(A_160,D_162,B_161)
      | ~ m1_subset_1(D_162,u1_struct_0(A_160))
      | ~ v4_lattice3(A_160)
      | ~ v10_lattices(A_160)
      | ~ l3_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_54,c_745])).

tff(c_806,plain,(
    ! [A_183,B_184,D_185] :
      ( k1_lattices(A_183,k15_lattice3(A_183,B_184),D_185) = D_185
      | ~ m1_subset_1(k15_lattice3(A_183,B_184),u1_struct_0(A_183))
      | ~ l2_lattices(A_183)
      | ~ r4_lattice3(A_183,D_185,B_184)
      | ~ m1_subset_1(D_185,u1_struct_0(A_183))
      | ~ v4_lattice3(A_183)
      | ~ v10_lattices(A_183)
      | ~ l3_lattices(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_749,c_18])).

tff(c_810,plain,(
    ! [A_186,B_187,D_188] :
      ( k1_lattices(A_186,k15_lattice3(A_186,B_187),D_188) = D_188
      | ~ l2_lattices(A_186)
      | ~ r4_lattice3(A_186,D_188,B_187)
      | ~ m1_subset_1(D_188,u1_struct_0(A_186))
      | ~ v4_lattice3(A_186)
      | ~ v10_lattices(A_186)
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_54,c_806])).

tff(c_824,plain,(
    ! [B_187] :
      ( k1_lattices('#skF_6',k15_lattice3('#skF_6',B_187),'#skF_7') = '#skF_7'
      | ~ l2_lattices('#skF_6')
      | ~ r4_lattice3('#skF_6','#skF_7',B_187)
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_810])).

tff(c_833,plain,(
    ! [B_187] :
      ( k1_lattices('#skF_6',k15_lattice3('#skF_6',B_187),'#skF_7') = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',B_187)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_70,c_79,c_824])).

tff(c_835,plain,(
    ! [B_189] :
      ( k1_lattices('#skF_6',k15_lattice3('#skF_6',B_189),'#skF_7') = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',B_189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_833])).

tff(c_309,plain,(
    ! [B_103] :
      ( k2_lattices('#skF_6',B_103,k1_lattices('#skF_6',B_103,'#skF_7')) = B_103
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_297])).

tff(c_317,plain,(
    ! [B_103] :
      ( k2_lattices('#skF_6',B_103,k1_lattices('#skF_6',B_103,'#skF_7')) = B_103
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_286,c_309])).

tff(c_319,plain,(
    ! [B_105] :
      ( k2_lattices('#skF_6',B_105,k1_lattices('#skF_6',B_105,'#skF_7')) = B_105
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_317])).

tff(c_334,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),k1_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7')) = k15_lattice3('#skF_6',B_48)
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_319])).

tff(c_355,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),k1_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7')) = k15_lattice3('#skF_6',B_48)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334])).

tff(c_356,plain,(
    ! [B_48] : k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),k1_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_7')) = k15_lattice3('#skF_6',B_48) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_355])).

tff(c_841,plain,(
    ! [B_189] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_189),'#skF_7') = k15_lattice3('#skF_6',B_189)
      | ~ r4_lattice3('#skF_6','#skF_7',B_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_356])).

tff(c_846,plain,(
    ! [B_189] :
      ( k2_lattices('#skF_6','#skF_7',k15_lattice3('#skF_6',B_189)) = k15_lattice3('#skF_6',B_189)
      | ~ r4_lattice3('#skF_6','#skF_7',B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_841])).

tff(c_974,plain,(
    ! [B_216] :
      ( k15_lattice3('#skF_6',B_216) = '#skF_7'
      | ~ r4_lattice3('#skF_6','#skF_7',B_216)
      | ~ r2_hidden('#skF_7',B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_846])).

tff(c_977,plain,
    ( k15_lattice3('#skF_6','#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_974])).

tff(c_980,plain,(
    k15_lattice3('#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_977])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_980])).

tff(c_984,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_987,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_984])).

tff(c_990,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_987])).

tff(c_992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:36:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.60  
% 3.59/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.60  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 3.59/1.60  
% 3.59/1.60  %Foreground sorts:
% 3.59/1.60  
% 3.59/1.60  
% 3.59/1.60  %Background operators:
% 3.59/1.60  
% 3.59/1.60  
% 3.59/1.60  %Foreground operators:
% 3.59/1.60  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.59/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.60  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.59/1.60  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.59/1.60  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.59/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.59/1.60  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.59/1.60  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.59/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.59/1.60  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.59/1.60  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.59/1.60  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.59/1.60  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.59/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.59/1.60  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.59/1.60  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.59/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.59/1.60  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.59/1.60  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.59/1.60  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.59/1.60  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.59/1.60  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.59/1.60  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.59/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.59/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.59/1.60  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.59/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.60  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.59/1.60  
% 3.59/1.62  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattice3)).
% 3.59/1.62  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.59/1.62  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 3.59/1.62  tff(f_83, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.59/1.62  tff(f_145, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 3.59/1.62  tff(f_102, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.59/1.62  tff(f_152, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 3.59/1.62  tff(f_171, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.59/1.62  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 3.59/1.62  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 3.59/1.62  tff(c_74, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_68, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_72, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.62  tff(c_60, plain, (k15_lattice3('#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_62, plain, (r4_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_24, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9), u1_struct_0(A_9)) | v9_lattices(A_9) | ~l3_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/1.62  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.62  tff(c_80, plain, (![A_61]: (l1_lattices(A_61) | ~l3_lattices(A_61))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.59/1.62  tff(c_84, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_68, c_80])).
% 3.59/1.62  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_185, plain, (![A_94, C_95, B_96]: (k2_lattices(A_94, C_95, B_96)=k2_lattices(A_94, B_96, C_95) | ~m1_subset_1(C_95, u1_struct_0(A_94)) | ~m1_subset_1(B_96, u1_struct_0(A_94)) | ~v6_lattices(A_94) | ~l1_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.59/1.62  tff(c_197, plain, (![B_96]: (k2_lattices('#skF_6', B_96, '#skF_7')=k2_lattices('#skF_6', '#skF_7', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_185])).
% 3.59/1.62  tff(c_205, plain, (![B_96]: (k2_lattices('#skF_6', B_96, '#skF_7')=k2_lattices('#skF_6', '#skF_7', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_197])).
% 3.59/1.62  tff(c_206, plain, (![B_96]: (k2_lattices('#skF_6', B_96, '#skF_7')=k2_lattices('#skF_6', '#skF_7', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_205])).
% 3.59/1.62  tff(c_207, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_206])).
% 3.59/1.62  tff(c_232, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_207])).
% 3.59/1.62  tff(c_235, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_232])).
% 3.59/1.62  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_235])).
% 3.59/1.62  tff(c_240, plain, (![B_100]: (k2_lattices('#skF_6', B_100, '#skF_7')=k2_lattices('#skF_6', '#skF_7', B_100) | ~m1_subset_1(B_100, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_206])).
% 3.59/1.62  tff(c_244, plain, (k2_lattices('#skF_6', '#skF_2'('#skF_6'), '#skF_7')=k2_lattices('#skF_6', '#skF_7', '#skF_2'('#skF_6')) | v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_240])).
% 3.59/1.62  tff(c_266, plain, (k2_lattices('#skF_6', '#skF_2'('#skF_6'), '#skF_7')=k2_lattices('#skF_6', '#skF_7', '#skF_2'('#skF_6')) | v9_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_244])).
% 3.59/1.62  tff(c_267, plain, (k2_lattices('#skF_6', '#skF_2'('#skF_6'), '#skF_7')=k2_lattices('#skF_6', '#skF_7', '#skF_2'('#skF_6')) | v9_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_266])).
% 3.59/1.62  tff(c_286, plain, (v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_267])).
% 3.59/1.62  tff(c_70, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.59/1.62  tff(c_239, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_206])).
% 3.59/1.62  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.62  tff(c_387, plain, (![A_113, B_114, C_115]: (r3_lattices(A_113, B_114, C_115) | ~r1_lattices(A_113, B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l3_lattices(A_113) | ~v9_lattices(A_113) | ~v8_lattices(A_113) | ~v6_lattices(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.59/1.62  tff(c_399, plain, (![B_114]: (r3_lattices('#skF_6', B_114, '#skF_7') | ~r1_lattices('#skF_6', B_114, '#skF_7') | ~m1_subset_1(B_114, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_387])).
% 3.59/1.62  tff(c_407, plain, (![B_114]: (r3_lattices('#skF_6', B_114, '#skF_7') | ~r1_lattices('#skF_6', B_114, '#skF_7') | ~m1_subset_1(B_114, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_286, c_68, c_399])).
% 3.59/1.62  tff(c_408, plain, (![B_114]: (r3_lattices('#skF_6', B_114, '#skF_7') | ~r1_lattices('#skF_6', B_114, '#skF_7') | ~m1_subset_1(B_114, u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_407])).
% 3.59/1.62  tff(c_409, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_408])).
% 3.59/1.62  tff(c_412, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_4, c_409])).
% 3.59/1.62  tff(c_415, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_412])).
% 3.59/1.62  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_415])).
% 3.59/1.62  tff(c_419, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_408])).
% 3.59/1.62  tff(c_75, plain, (![A_60]: (l2_lattices(A_60) | ~l3_lattices(A_60))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.59/1.62  tff(c_79, plain, (l2_lattices('#skF_6')), inference(resolution, [status(thm)], [c_68, c_75])).
% 3.59/1.62  tff(c_54, plain, (![A_47, B_48]: (m1_subset_1(k15_lattice3(A_47, B_48), u1_struct_0(A_47)) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.59/1.62  tff(c_58, plain, (![A_49, B_53, C_55]: (r3_lattices(A_49, B_53, k15_lattice3(A_49, C_55)) | ~r2_hidden(B_53, C_55) | ~m1_subset_1(B_53, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.59/1.62  tff(c_358, plain, (![A_106, B_107, C_108]: (r1_lattices(A_106, B_107, C_108) | ~r3_lattices(A_106, B_107, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l3_lattices(A_106) | ~v9_lattices(A_106) | ~v8_lattices(A_106) | ~v6_lattices(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.59/1.62  tff(c_798, plain, (![A_177, B_178, C_179]: (r1_lattices(A_177, B_178, k15_lattice3(A_177, C_179)) | ~m1_subset_1(k15_lattice3(A_177, C_179), u1_struct_0(A_177)) | ~v9_lattices(A_177) | ~v8_lattices(A_177) | ~v6_lattices(A_177) | ~r2_hidden(B_178, C_179) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~l3_lattices(A_177) | ~v4_lattice3(A_177) | ~v10_lattices(A_177) | v2_struct_0(A_177))), inference(resolution, [status(thm)], [c_58, c_358])).
% 3.59/1.62  tff(c_802, plain, (![A_180, B_181, B_182]: (r1_lattices(A_180, B_181, k15_lattice3(A_180, B_182)) | ~v9_lattices(A_180) | ~v8_lattices(A_180) | ~v6_lattices(A_180) | ~r2_hidden(B_181, B_182) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~v4_lattice3(A_180) | ~v10_lattices(A_180) | ~l3_lattices(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_54, c_798])).
% 3.59/1.62  tff(c_18, plain, (![A_2, B_6, C_8]: (k1_lattices(A_2, B_6, C_8)=C_8 | ~r1_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l2_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.59/1.62  tff(c_881, plain, (![A_201, B_202, B_203]: (k1_lattices(A_201, B_202, k15_lattice3(A_201, B_203))=k15_lattice3(A_201, B_203) | ~m1_subset_1(k15_lattice3(A_201, B_203), u1_struct_0(A_201)) | ~l2_lattices(A_201) | ~v9_lattices(A_201) | ~v8_lattices(A_201) | ~v6_lattices(A_201) | ~r2_hidden(B_202, B_203) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~v4_lattice3(A_201) | ~v10_lattices(A_201) | ~l3_lattices(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_802, c_18])).
% 3.59/1.62  tff(c_910, plain, (![A_208, B_209, B_210]: (k1_lattices(A_208, B_209, k15_lattice3(A_208, B_210))=k15_lattice3(A_208, B_210) | ~l2_lattices(A_208) | ~v9_lattices(A_208) | ~v8_lattices(A_208) | ~v6_lattices(A_208) | ~r2_hidden(B_209, B_210) | ~m1_subset_1(B_209, u1_struct_0(A_208)) | ~v4_lattice3(A_208) | ~v10_lattices(A_208) | ~l3_lattices(A_208) | v2_struct_0(A_208))), inference(resolution, [status(thm)], [c_54, c_881])).
% 3.59/1.62  tff(c_924, plain, (![B_210]: (k1_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_210))=k15_lattice3('#skF_6', B_210) | ~l2_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | ~r2_hidden('#skF_7', B_210) | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_910])).
% 3.59/1.62  tff(c_933, plain, (![B_210]: (k1_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_210))=k15_lattice3('#skF_6', B_210) | ~r2_hidden('#skF_7', B_210) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_70, c_239, c_419, c_286, c_79, c_924])).
% 3.59/1.62  tff(c_935, plain, (![B_211]: (k1_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_211))=k15_lattice3('#skF_6', B_211) | ~r2_hidden('#skF_7', B_211))), inference(negUnitSimplification, [status(thm)], [c_74, c_933])).
% 3.59/1.62  tff(c_297, plain, (![A_102, B_103, C_104]: (k2_lattices(A_102, B_103, k1_lattices(A_102, B_103, C_104))=B_103 | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~v9_lattices(A_102) | ~l3_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/1.62  tff(c_314, plain, (![A_47, B_103, B_48]: (k2_lattices(A_47, B_103, k1_lattices(A_47, B_103, k15_lattice3(A_47, B_48)))=B_103 | ~m1_subset_1(B_103, u1_struct_0(A_47)) | ~v9_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_54, c_297])).
% 3.59/1.62  tff(c_941, plain, (![B_211]: (k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_211))='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden('#skF_7', B_211))), inference(superposition, [status(thm), theory('equality')], [c_935, c_314])).
% 3.59/1.62  tff(c_947, plain, (![B_211]: (k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_211))='#skF_7' | v2_struct_0('#skF_6') | ~r2_hidden('#skF_7', B_211))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_286, c_66, c_941])).
% 3.59/1.62  tff(c_950, plain, (![B_212]: (k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_212))='#skF_7' | ~r2_hidden('#skF_7', B_212))), inference(negUnitSimplification, [status(thm)], [c_74, c_947])).
% 3.59/1.62  tff(c_260, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7')=k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_48)) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_240])).
% 3.59/1.62  tff(c_282, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7')=k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_48)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_260])).
% 3.59/1.62  tff(c_283, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7')=k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_48)))), inference(negUnitSimplification, [status(thm)], [c_74, c_282])).
% 3.59/1.62  tff(c_745, plain, (![A_157, B_158, D_159]: (r1_lattices(A_157, k15_lattice3(A_157, B_158), D_159) | ~r4_lattice3(A_157, D_159, B_158) | ~m1_subset_1(D_159, u1_struct_0(A_157)) | ~m1_subset_1(k15_lattice3(A_157, B_158), u1_struct_0(A_157)) | ~v4_lattice3(A_157) | ~v10_lattices(A_157) | ~l3_lattices(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.59/1.62  tff(c_749, plain, (![A_160, B_161, D_162]: (r1_lattices(A_160, k15_lattice3(A_160, B_161), D_162) | ~r4_lattice3(A_160, D_162, B_161) | ~m1_subset_1(D_162, u1_struct_0(A_160)) | ~v4_lattice3(A_160) | ~v10_lattices(A_160) | ~l3_lattices(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_54, c_745])).
% 3.59/1.62  tff(c_806, plain, (![A_183, B_184, D_185]: (k1_lattices(A_183, k15_lattice3(A_183, B_184), D_185)=D_185 | ~m1_subset_1(k15_lattice3(A_183, B_184), u1_struct_0(A_183)) | ~l2_lattices(A_183) | ~r4_lattice3(A_183, D_185, B_184) | ~m1_subset_1(D_185, u1_struct_0(A_183)) | ~v4_lattice3(A_183) | ~v10_lattices(A_183) | ~l3_lattices(A_183) | v2_struct_0(A_183))), inference(resolution, [status(thm)], [c_749, c_18])).
% 3.59/1.62  tff(c_810, plain, (![A_186, B_187, D_188]: (k1_lattices(A_186, k15_lattice3(A_186, B_187), D_188)=D_188 | ~l2_lattices(A_186) | ~r4_lattice3(A_186, D_188, B_187) | ~m1_subset_1(D_188, u1_struct_0(A_186)) | ~v4_lattice3(A_186) | ~v10_lattices(A_186) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_54, c_806])).
% 3.59/1.62  tff(c_824, plain, (![B_187]: (k1_lattices('#skF_6', k15_lattice3('#skF_6', B_187), '#skF_7')='#skF_7' | ~l2_lattices('#skF_6') | ~r4_lattice3('#skF_6', '#skF_7', B_187) | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_810])).
% 3.59/1.62  tff(c_833, plain, (![B_187]: (k1_lattices('#skF_6', k15_lattice3('#skF_6', B_187), '#skF_7')='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', B_187) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_70, c_79, c_824])).
% 3.59/1.62  tff(c_835, plain, (![B_189]: (k1_lattices('#skF_6', k15_lattice3('#skF_6', B_189), '#skF_7')='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', B_189))), inference(negUnitSimplification, [status(thm)], [c_74, c_833])).
% 3.59/1.62  tff(c_309, plain, (![B_103]: (k2_lattices('#skF_6', B_103, k1_lattices('#skF_6', B_103, '#skF_7'))=B_103 | ~m1_subset_1(B_103, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_297])).
% 3.59/1.62  tff(c_317, plain, (![B_103]: (k2_lattices('#skF_6', B_103, k1_lattices('#skF_6', B_103, '#skF_7'))=B_103 | ~m1_subset_1(B_103, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_286, c_309])).
% 3.59/1.62  tff(c_319, plain, (![B_105]: (k2_lattices('#skF_6', B_105, k1_lattices('#skF_6', B_105, '#skF_7'))=B_105 | ~m1_subset_1(B_105, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_74, c_317])).
% 3.59/1.62  tff(c_334, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), k1_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7'))=k15_lattice3('#skF_6', B_48) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_319])).
% 3.59/1.62  tff(c_355, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), k1_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7'))=k15_lattice3('#skF_6', B_48) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_334])).
% 3.59/1.62  tff(c_356, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), k1_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_7'))=k15_lattice3('#skF_6', B_48))), inference(negUnitSimplification, [status(thm)], [c_74, c_355])).
% 3.59/1.62  tff(c_841, plain, (![B_189]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_189), '#skF_7')=k15_lattice3('#skF_6', B_189) | ~r4_lattice3('#skF_6', '#skF_7', B_189))), inference(superposition, [status(thm), theory('equality')], [c_835, c_356])).
% 3.59/1.62  tff(c_846, plain, (![B_189]: (k2_lattices('#skF_6', '#skF_7', k15_lattice3('#skF_6', B_189))=k15_lattice3('#skF_6', B_189) | ~r4_lattice3('#skF_6', '#skF_7', B_189))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_841])).
% 3.59/1.62  tff(c_974, plain, (![B_216]: (k15_lattice3('#skF_6', B_216)='#skF_7' | ~r4_lattice3('#skF_6', '#skF_7', B_216) | ~r2_hidden('#skF_7', B_216))), inference(superposition, [status(thm), theory('equality')], [c_950, c_846])).
% 3.59/1.62  tff(c_977, plain, (k15_lattice3('#skF_6', '#skF_8')='#skF_7' | ~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_62, c_974])).
% 3.59/1.62  tff(c_980, plain, (k15_lattice3('#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_977])).
% 3.59/1.62  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_980])).
% 3.59/1.62  tff(c_984, plain, (~v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_267])).
% 3.59/1.62  tff(c_987, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_2, c_984])).
% 3.59/1.62  tff(c_990, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_987])).
% 3.59/1.62  tff(c_992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_990])).
% 3.59/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  Inference rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Ref     : 0
% 3.59/1.62  #Sup     : 188
% 3.59/1.62  #Fact    : 0
% 3.59/1.62  #Define  : 0
% 3.59/1.62  #Split   : 9
% 3.59/1.62  #Chain   : 0
% 3.59/1.62  #Close   : 0
% 3.59/1.62  
% 3.59/1.62  Ordering : KBO
% 3.59/1.62  
% 3.59/1.62  Simplification rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Subsume      : 23
% 3.59/1.62  #Demod        : 116
% 3.59/1.62  #Tautology    : 94
% 3.59/1.62  #SimpNegUnit  : 50
% 3.59/1.62  #BackRed      : 0
% 3.59/1.62  
% 3.59/1.62  #Partial instantiations: 0
% 3.59/1.62  #Strategies tried      : 1
% 3.59/1.62  
% 3.59/1.62  Timing (in seconds)
% 3.59/1.62  ----------------------
% 3.59/1.62  Preprocessing        : 0.37
% 3.59/1.62  Parsing              : 0.19
% 3.59/1.62  CNF conversion       : 0.03
% 3.59/1.62  Main loop            : 0.47
% 3.59/1.62  Inferencing          : 0.19
% 3.59/1.62  Reduction            : 0.12
% 3.59/1.62  Demodulation         : 0.08
% 3.59/1.62  BG Simplification    : 0.03
% 3.59/1.62  Subsumption          : 0.09
% 3.59/1.62  Abstraction          : 0.03
% 3.59/1.62  MUC search           : 0.00
% 3.59/1.62  Cooper               : 0.00
% 3.59/1.62  Total                : 0.87
% 3.59/1.63  Index Insertion      : 0.00
% 3.59/1.63  Index Deletion       : 0.00
% 3.59/1.63  Index Matching       : 0.00
% 3.59/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
