%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 12.37s
% Output     : CNFRefutation 12.62s
% Verified   : 
% Statistics : Number of formulae       :  198 (1759 expanded)
%              Number of leaves         :   43 ( 584 expanded)
%              Depth                    :   27
%              Number of atoms          :  657 (8354 expanded)
%              Number of equality atoms :   18 ( 268 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_orders_2 > v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k8_funcop_1 > k3_yellow_6 > k3_waybel_2 > k11_lattice3 > u1_waybel_0 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_6,type,(
    k3_yellow_6: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_waybel_2,type,(
    k3_waybel_2: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k8_funcop_1,type,(
    k8_funcop_1: ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_247,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & l1_waybel_0(C,A) )
               => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
                  & v4_orders_2(k3_waybel_2(A,B,C))
                  & v7_waybel_0(k3_waybel_2(A,B,C))
                  & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_9)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_202,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( v6_waybel_0(k3_waybel_2(A,B,C),A)
        & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_2)).

tff(f_219,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
        & v6_waybel_0(k3_waybel_2(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_waybel_2)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v4_orders_2(A)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(A),u1_orders_2(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l16_yellow_6)).

tff(f_186,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_waybel_0(C,A) )
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k3_waybel_2(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(D))
                         => ? [F] :
                              ( m1_subset_1(F,u1_struct_0(A))
                              & F = k1_funct_1(u1_waybel_0(A,C),E)
                              & k1_funct_1(u1_waybel_0(A,D),E) = k11_lattice3(A,B,F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k3_yellow_6(A,B,C),B)
        & l1_waybel_0(k3_yellow_6(A,B,C),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_6)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k3_yellow_6(A,B,C)) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_6)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,B)
                    & l1_waybel_0(D,B) )
                 => ( D = k3_yellow_6(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A))
                      & r2_funct_2(u1_struct_0(D),u1_struct_0(B),u1_waybel_0(B,D),k8_funcop_1(u1_struct_0(B),u1_struct_0(D),C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_6)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v7_waybel_0(A)
      <=> v7_waybel_0(g1_orders_2(u1_struct_0(A),u1_orders_2(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l15_yellow_6)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( ~ v2_struct_0(k3_yellow_6(A,B,C))
        & v6_waybel_0(k3_yellow_6(A,B,C),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_yellow_6)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_78,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_68,plain,(
    l1_waybel_0('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2373,plain,(
    ! [B_512,A_513] :
      ( l1_orders_2(B_512)
      | ~ l1_waybel_0(B_512,A_513)
      | ~ l1_struct_0(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2377,plain,
    ( l1_orders_2('#skF_8')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_2373])).

tff(c_2378,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2377])).

tff(c_2382,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_2378])).

tff(c_2386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2382])).

tff(c_2388,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2377])).

tff(c_2596,plain,(
    ! [A_558,B_559,C_560] :
      ( l1_waybel_0(k3_waybel_2(A_558,B_559,C_560),A_558)
      | ~ l1_waybel_0(C_560,A_558)
      | v2_struct_0(C_560)
      | ~ m1_subset_1(B_559,u1_struct_0(A_558))
      | ~ l1_orders_2(A_558)
      | v2_struct_0(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2608,plain,(
    ! [C_560] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_560),'#skF_6')
      | ~ l1_waybel_0(C_560,'#skF_6')
      | v2_struct_0(C_560)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_2596])).

tff(c_2613,plain,(
    ! [C_560] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_560),'#skF_6')
      | ~ l1_waybel_0(C_560,'#skF_6')
      | v2_struct_0(C_560)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2608])).

tff(c_2615,plain,(
    ! [C_561] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_561),'#skF_6')
      | ~ l1_waybel_0(C_561,'#skF_6')
      | v2_struct_0(C_561) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2613])).

tff(c_89,plain,(
    ! [B_185,A_186] :
      ( l1_orders_2(B_185)
      | ~ l1_waybel_0(B_185,A_186)
      | ~ l1_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,
    ( l1_orders_2('#skF_8')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_89])).

tff(c_94,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_97,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_97])).

tff(c_103,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_309,plain,(
    ! [A_227,B_228,C_229] :
      ( l1_waybel_0(k3_waybel_2(A_227,B_228,C_229),A_227)
      | ~ l1_waybel_0(C_229,A_227)
      | v2_struct_0(C_229)
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_321,plain,(
    ! [C_229] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_229),'#skF_6')
      | ~ l1_waybel_0(C_229,'#skF_6')
      | v2_struct_0(C_229)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_309])).

tff(c_326,plain,(
    ! [C_229] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_229),'#skF_6')
      | ~ l1_waybel_0(C_229,'#skF_6')
      | v2_struct_0(C_229)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_321])).

tff(c_328,plain,(
    ! [C_230] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_230),'#skF_6')
      | ~ l1_waybel_0(C_230,'#skF_6')
      | v2_struct_0(C_230) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_326])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_orders_2(B_6)
      | ~ l1_waybel_0(B_6,A_4)
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_331,plain,(
    ! [C_230] :
      ( l1_orders_2(k3_waybel_2('#skF_6','#skF_7',C_230))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_waybel_0(C_230,'#skF_6')
      | v2_struct_0(C_230) ) ),
    inference(resolution,[status(thm)],[c_328,c_8])).

tff(c_334,plain,(
    ! [C_230] :
      ( l1_orders_2(k3_waybel_2('#skF_6','#skF_7',C_230))
      | ~ l1_waybel_0(C_230,'#skF_6')
      | v2_struct_0(C_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_331])).

tff(c_102,plain,(
    l1_orders_2('#skF_8') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_72,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_327,plain,(
    ! [C_229] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_229),'#skF_6')
      | ~ l1_waybel_0(C_229,'#skF_6')
      | v2_struct_0(C_229) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_326])).

tff(c_62,plain,(
    ! [A_175,B_176,C_177] :
      ( v6_waybel_0(k3_waybel_2(A_175,B_176,C_177),A_175)
      | ~ l1_waybel_0(C_177,A_175)
      | v2_struct_0(C_177)
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_42,plain,(
    ! [A_55] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(A_55),u1_orders_2(A_55)))
      | ~ v4_orders_2(A_55)
      | ~ l1_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_531,plain,(
    ! [A_272,B_273,C_274] :
      ( g1_orders_2(u1_struct_0(k3_waybel_2(A_272,B_273,C_274)),u1_orders_2(k3_waybel_2(A_272,B_273,C_274))) = g1_orders_2(u1_struct_0(C_274),u1_orders_2(C_274))
      | ~ l1_waybel_0(k3_waybel_2(A_272,B_273,C_274),A_272)
      | ~ v6_waybel_0(k3_waybel_2(A_272,B_273,C_274),A_272)
      | ~ l1_waybel_0(C_274,A_272)
      | v2_struct_0(C_274)
      | ~ m1_subset_1(B_273,u1_struct_0(A_272))
      | ~ l1_orders_2(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40,plain,(
    ! [A_55] :
      ( v4_orders_2(A_55)
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(A_55),u1_orders_2(A_55)))
      | ~ l1_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2218,plain,(
    ! [A_495,B_496,C_497] :
      ( v4_orders_2(k3_waybel_2(A_495,B_496,C_497))
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(C_497),u1_orders_2(C_497)))
      | ~ l1_orders_2(k3_waybel_2(A_495,B_496,C_497))
      | v2_struct_0(k3_waybel_2(A_495,B_496,C_497))
      | ~ l1_waybel_0(k3_waybel_2(A_495,B_496,C_497),A_495)
      | ~ v6_waybel_0(k3_waybel_2(A_495,B_496,C_497),A_495)
      | ~ l1_waybel_0(C_497,A_495)
      | v2_struct_0(C_497)
      | ~ m1_subset_1(B_496,u1_struct_0(A_495))
      | ~ l1_orders_2(A_495)
      | v2_struct_0(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_40])).

tff(c_2242,plain,(
    ! [A_498,B_499,A_500] :
      ( v4_orders_2(k3_waybel_2(A_498,B_499,A_500))
      | ~ l1_orders_2(k3_waybel_2(A_498,B_499,A_500))
      | v2_struct_0(k3_waybel_2(A_498,B_499,A_500))
      | ~ l1_waybel_0(k3_waybel_2(A_498,B_499,A_500),A_498)
      | ~ v6_waybel_0(k3_waybel_2(A_498,B_499,A_500),A_498)
      | ~ l1_waybel_0(A_500,A_498)
      | ~ m1_subset_1(B_499,u1_struct_0(A_498))
      | ~ l1_orders_2(A_498)
      | v2_struct_0(A_498)
      | ~ v4_orders_2(A_500)
      | ~ l1_orders_2(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_42,c_2218])).

tff(c_2247,plain,(
    ! [A_501,B_502,C_503] :
      ( v4_orders_2(k3_waybel_2(A_501,B_502,C_503))
      | ~ l1_orders_2(k3_waybel_2(A_501,B_502,C_503))
      | v2_struct_0(k3_waybel_2(A_501,B_502,C_503))
      | ~ l1_waybel_0(k3_waybel_2(A_501,B_502,C_503),A_501)
      | ~ v4_orders_2(C_503)
      | ~ l1_orders_2(C_503)
      | ~ l1_waybel_0(C_503,A_501)
      | v2_struct_0(C_503)
      | ~ m1_subset_1(B_502,u1_struct_0(A_501))
      | ~ l1_orders_2(A_501)
      | v2_struct_0(A_501) ) ),
    inference(resolution,[status(thm)],[c_62,c_2242])).

tff(c_2255,plain,(
    ! [C_229] :
      ( v4_orders_2(k3_waybel_2('#skF_6','#skF_7',C_229))
      | ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7',C_229))
      | v2_struct_0(k3_waybel_2('#skF_6','#skF_7',C_229))
      | ~ v4_orders_2(C_229)
      | ~ l1_orders_2(C_229)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(C_229,'#skF_6')
      | v2_struct_0(C_229) ) ),
    inference(resolution,[status(thm)],[c_327,c_2247])).

tff(c_2261,plain,(
    ! [C_229] :
      ( v4_orders_2(k3_waybel_2('#skF_6','#skF_7',C_229))
      | ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7',C_229))
      | v2_struct_0(k3_waybel_2('#skF_6','#skF_7',C_229))
      | ~ v4_orders_2(C_229)
      | ~ l1_orders_2(C_229)
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(C_229,'#skF_6')
      | v2_struct_0(C_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2255])).

tff(c_2263,plain,(
    ! [C_504] :
      ( v4_orders_2(k3_waybel_2('#skF_6','#skF_7',C_504))
      | ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7',C_504))
      | v2_struct_0(k3_waybel_2('#skF_6','#skF_7',C_504))
      | ~ v4_orders_2(C_504)
      | ~ l1_orders_2(C_504)
      | ~ l1_waybel_0(C_504,'#skF_6')
      | v2_struct_0(C_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2261])).

tff(c_66,plain,
    ( ~ l1_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'),'#skF_6')
    | ~ v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ v4_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_83,plain,(
    ~ v4_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2269,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ v4_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2263,c_83])).

tff(c_2273,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_72,c_2269])).

tff(c_2274,plain,
    ( ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2273])).

tff(c_2311,plain,(
    ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2274])).

tff(c_2314,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_334,c_2311])).

tff(c_2317,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2314])).

tff(c_2319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2317])).

tff(c_2320,plain,(
    v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2274])).

tff(c_64,plain,(
    ! [A_175,B_176,C_177] :
      ( ~ v2_struct_0(k3_waybel_2(A_175,B_176,C_177))
      | ~ l1_waybel_0(C_177,A_175)
      | v2_struct_0(C_177)
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_2360,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2320,c_64])).

tff(c_2363,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_2360])).

tff(c_2365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_2363])).

tff(c_2366,plain,
    ( ~ v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ l1_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'),'#skF_6')
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2389,plain,(
    ~ l1_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2366])).

tff(c_2618,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2615,c_2389])).

tff(c_2624,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2618])).

tff(c_2626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2624])).

tff(c_2628,plain,(
    l1_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2366])).

tff(c_2631,plain,
    ( l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2628,c_8])).

tff(c_2634,plain,(
    l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2631])).

tff(c_2367,plain,(
    v4_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3125,plain,(
    ! [A_654,B_655,C_656] :
      ( g1_orders_2(u1_struct_0(k3_waybel_2(A_654,B_655,C_656)),u1_orders_2(k3_waybel_2(A_654,B_655,C_656))) = g1_orders_2(u1_struct_0(C_656),u1_orders_2(C_656))
      | ~ l1_waybel_0(k3_waybel_2(A_654,B_655,C_656),A_654)
      | ~ v6_waybel_0(k3_waybel_2(A_654,B_655,C_656),A_654)
      | ~ l1_waybel_0(C_656,A_654)
      | v2_struct_0(C_656)
      | ~ m1_subset_1(B_655,u1_struct_0(A_654))
      | ~ l1_orders_2(A_654)
      | v2_struct_0(A_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6365,plain,(
    ! [C_957,A_958,B_959] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(C_957),u1_orders_2(C_957)))
      | ~ v4_orders_2(k3_waybel_2(A_958,B_959,C_957))
      | ~ l1_orders_2(k3_waybel_2(A_958,B_959,C_957))
      | v2_struct_0(k3_waybel_2(A_958,B_959,C_957))
      | ~ l1_waybel_0(k3_waybel_2(A_958,B_959,C_957),A_958)
      | ~ v6_waybel_0(k3_waybel_2(A_958,B_959,C_957),A_958)
      | ~ l1_waybel_0(C_957,A_958)
      | v2_struct_0(C_957)
      | ~ m1_subset_1(B_959,u1_struct_0(A_958))
      | ~ l1_orders_2(A_958)
      | v2_struct_0(A_958) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3125,c_42])).

tff(c_6370,plain,(
    ! [C_962,A_963,B_964] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(C_962),u1_orders_2(C_962)))
      | ~ v4_orders_2(k3_waybel_2(A_963,B_964,C_962))
      | ~ l1_orders_2(k3_waybel_2(A_963,B_964,C_962))
      | v2_struct_0(k3_waybel_2(A_963,B_964,C_962))
      | ~ l1_waybel_0(k3_waybel_2(A_963,B_964,C_962),A_963)
      | ~ l1_waybel_0(C_962,A_963)
      | v2_struct_0(C_962)
      | ~ m1_subset_1(B_964,u1_struct_0(A_963))
      | ~ l1_orders_2(A_963)
      | v2_struct_0(A_963) ) ),
    inference(resolution,[status(thm)],[c_62,c_6365])).

tff(c_6388,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | ~ v4_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2628,c_6370])).

tff(c_6402,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_2634,c_2367,c_6388])).

tff(c_6403,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_6402])).

tff(c_6404,plain,(
    v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6403])).

tff(c_6457,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6404,c_64])).

tff(c_6460,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_6457])).

tff(c_6462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_6460])).

tff(c_6464,plain,(
    ~ v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6403])).

tff(c_2627,plain,
    ( ~ v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2366])).

tff(c_2635,plain,(
    ~ v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2627])).

tff(c_2801,plain,(
    ! [A_600,B_601,C_602] :
      ( l1_waybel_0(k3_waybel_2(A_600,B_601,C_602),A_600)
      | ~ l1_waybel_0(C_602,A_600)
      | v2_struct_0(C_602)
      | ~ m1_subset_1(B_601,u1_struct_0(A_600))
      | ~ l1_orders_2(A_600)
      | v2_struct_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2811,plain,(
    ! [C_602] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_602),'#skF_6')
      | ~ l1_waybel_0(C_602,'#skF_6')
      | v2_struct_0(C_602)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_2801])).

tff(c_2816,plain,(
    ! [C_602] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_602),'#skF_6')
      | ~ l1_waybel_0(C_602,'#skF_6')
      | v2_struct_0(C_602)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2811])).

tff(c_2817,plain,(
    ! [C_602] :
      ( l1_waybel_0(k3_waybel_2('#skF_6','#skF_7',C_602),'#skF_6')
      | ~ l1_waybel_0(C_602,'#skF_6')
      | v2_struct_0(C_602) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2816])).

tff(c_2387,plain,(
    l1_orders_2('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2377])).

tff(c_70,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_2650,plain,(
    ! [A_568,B_569,C_570] :
      ( l1_waybel_0(k3_yellow_6(A_568,B_569,C_570),B_569)
      | ~ m1_subset_1(C_570,u1_struct_0(B_569))
      | ~ l1_struct_0(B_569)
      | v2_struct_0(B_569)
      | ~ l1_orders_2(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2656,plain,(
    ! [A_568] :
      ( l1_waybel_0(k3_yellow_6(A_568,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_568) ) ),
    inference(resolution,[status(thm)],[c_76,c_2650])).

tff(c_2661,plain,(
    ! [A_568] :
      ( l1_waybel_0(k3_yellow_6(A_568,'#skF_6','#skF_7'),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2656])).

tff(c_2663,plain,(
    ! [A_571] :
      ( l1_waybel_0(k3_yellow_6(A_571,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2(A_571) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2661])).

tff(c_2666,plain,(
    ! [A_571] :
      ( l1_orders_2(k3_yellow_6(A_571,'#skF_6','#skF_7'))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_orders_2(A_571) ) ),
    inference(resolution,[status(thm)],[c_2663,c_8])).

tff(c_2669,plain,(
    ! [A_571] :
      ( l1_orders_2(k3_yellow_6(A_571,'#skF_6','#skF_7'))
      | ~ l1_orders_2(A_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2666])).

tff(c_30,plain,(
    ! [A_48,B_49,C_50] :
      ( v6_waybel_0(k3_yellow_6(A_48,B_49,C_50),B_49)
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l1_struct_0(B_49)
      | v2_struct_0(B_49)
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6463,plain,(
    v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_6403])).

tff(c_2673,plain,(
    ! [A_579,B_580,C_581] :
      ( u1_struct_0(k3_yellow_6(A_579,B_580,C_581)) = u1_struct_0(A_579)
      | ~ m1_subset_1(C_581,u1_struct_0(B_580))
      | ~ l1_struct_0(B_580)
      | v2_struct_0(B_580)
      | ~ l1_orders_2(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2679,plain,(
    ! [A_579] :
      ( u1_struct_0(k3_yellow_6(A_579,'#skF_6','#skF_7')) = u1_struct_0(A_579)
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_579) ) ),
    inference(resolution,[status(thm)],[c_76,c_2673])).

tff(c_2684,plain,(
    ! [A_579] :
      ( u1_struct_0(k3_yellow_6(A_579,'#skF_6','#skF_7')) = u1_struct_0(A_579)
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2679])).

tff(c_2685,plain,(
    ! [A_579] :
      ( u1_struct_0(k3_yellow_6(A_579,'#skF_6','#skF_7')) = u1_struct_0(A_579)
      | ~ l1_orders_2(A_579) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2684])).

tff(c_2990,plain,(
    ! [A_638,B_639,C_640] :
      ( g1_orders_2(u1_struct_0(k3_yellow_6(A_638,B_639,C_640)),u1_orders_2(k3_yellow_6(A_638,B_639,C_640))) = g1_orders_2(u1_struct_0(A_638),u1_orders_2(A_638))
      | ~ l1_waybel_0(k3_yellow_6(A_638,B_639,C_640),B_639)
      | ~ v6_waybel_0(k3_yellow_6(A_638,B_639,C_640),B_639)
      | ~ m1_subset_1(C_640,u1_struct_0(B_639))
      | ~ l1_struct_0(B_639)
      | v2_struct_0(B_639)
      | ~ l1_orders_2(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3017,plain,(
    ! [A_579] :
      ( g1_orders_2(u1_struct_0(A_579),u1_orders_2(k3_yellow_6(A_579,'#skF_6','#skF_7'))) = g1_orders_2(u1_struct_0(A_579),u1_orders_2(A_579))
      | ~ l1_waybel_0(k3_yellow_6(A_579,'#skF_6','#skF_7'),'#skF_6')
      | ~ v6_waybel_0(k3_yellow_6(A_579,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_579)
      | ~ l1_orders_2(A_579) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_2990])).

tff(c_3021,plain,(
    ! [A_579] :
      ( g1_orders_2(u1_struct_0(A_579),u1_orders_2(k3_yellow_6(A_579,'#skF_6','#skF_7'))) = g1_orders_2(u1_struct_0(A_579),u1_orders_2(A_579))
      | ~ l1_waybel_0(k3_yellow_6(A_579,'#skF_6','#skF_7'),'#skF_6')
      | ~ v6_waybel_0(k3_yellow_6(A_579,'#skF_6','#skF_7'),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_76,c_3017])).

tff(c_3042,plain,(
    ! [A_646] :
      ( g1_orders_2(u1_struct_0(A_646),u1_orders_2(k3_yellow_6(A_646,'#skF_6','#skF_7'))) = g1_orders_2(u1_struct_0(A_646),u1_orders_2(A_646))
      | ~ l1_waybel_0(k3_yellow_6(A_646,'#skF_6','#skF_7'),'#skF_6')
      | ~ v6_waybel_0(k3_yellow_6(A_646,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2(A_646) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3021])).

tff(c_2686,plain,(
    ! [A_582] :
      ( u1_struct_0(k3_yellow_6(A_582,'#skF_6','#skF_7')) = u1_struct_0(A_582)
      | ~ l1_orders_2(A_582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2684])).

tff(c_2696,plain,(
    ! [A_582] :
      ( v4_orders_2(k3_yellow_6(A_582,'#skF_6','#skF_7'))
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(A_582),u1_orders_2(k3_yellow_6(A_582,'#skF_6','#skF_7'))))
      | ~ l1_orders_2(k3_yellow_6(A_582,'#skF_6','#skF_7'))
      | v2_struct_0(k3_yellow_6(A_582,'#skF_6','#skF_7'))
      | ~ l1_orders_2(A_582) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2686,c_40])).

tff(c_3048,plain,(
    ! [A_646] :
      ( v4_orders_2(k3_yellow_6(A_646,'#skF_6','#skF_7'))
      | ~ v4_orders_2(g1_orders_2(u1_struct_0(A_646),u1_orders_2(A_646)))
      | ~ l1_orders_2(k3_yellow_6(A_646,'#skF_6','#skF_7'))
      | v2_struct_0(k3_yellow_6(A_646,'#skF_6','#skF_7'))
      | ~ l1_orders_2(A_646)
      | ~ l1_waybel_0(k3_yellow_6(A_646,'#skF_6','#skF_7'),'#skF_6')
      | ~ v6_waybel_0(k3_yellow_6(A_646,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2(A_646) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3042,c_2696])).

tff(c_6471,plain,
    ( v4_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6')
    | ~ v6_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_6463,c_3048])).

tff(c_6483,plain,
    ( v4_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6')
    | ~ v6_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_6471])).

tff(c_6585,plain,(
    ~ v6_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6483])).

tff(c_6588,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_6585])).

tff(c_6591,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2388,c_76,c_6588])).

tff(c_6593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6591])).

tff(c_6594,plain,
    ( ~ l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v4_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6483])).

tff(c_6604,plain,(
    ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6594])).

tff(c_6607,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_2669,c_6604])).

tff(c_6611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_6607])).

tff(c_6613,plain,(
    l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6594])).

tff(c_2662,plain,(
    ! [A_568] :
      ( l1_waybel_0(k3_yellow_6(A_568,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2(A_568) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2661])).

tff(c_6612,plain,
    ( ~ l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6')
    | v4_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6594])).

tff(c_6614,plain,(
    ~ l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6612])).

tff(c_6617,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_2662,c_6614])).

tff(c_6621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_6617])).

tff(c_6623,plain,(
    l1_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_6612])).

tff(c_38,plain,(
    ! [A_54] :
      ( v7_waybel_0(g1_orders_2(u1_struct_0(A_54),u1_orders_2(A_54)))
      | ~ v7_waybel_0(A_54)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    ! [A_54] :
      ( v7_waybel_0(A_54)
      | ~ v7_waybel_0(g1_orders_2(u1_struct_0(A_54),u1_orders_2(A_54)))
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4764,plain,(
    ! [A_820,B_821,C_822] :
      ( v7_waybel_0(k3_yellow_6(A_820,B_821,C_822))
      | ~ v7_waybel_0(g1_orders_2(u1_struct_0(A_820),u1_orders_2(A_820)))
      | ~ l1_orders_2(k3_yellow_6(A_820,B_821,C_822))
      | v2_struct_0(k3_yellow_6(A_820,B_821,C_822))
      | ~ l1_waybel_0(k3_yellow_6(A_820,B_821,C_822),B_821)
      | ~ v6_waybel_0(k3_yellow_6(A_820,B_821,C_822),B_821)
      | ~ m1_subset_1(C_822,u1_struct_0(B_821))
      | ~ l1_struct_0(B_821)
      | v2_struct_0(B_821)
      | ~ l1_orders_2(A_820) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_36])).

tff(c_5573,plain,(
    ! [A_864,B_865,C_866] :
      ( v7_waybel_0(k3_yellow_6(A_864,B_865,C_866))
      | ~ l1_orders_2(k3_yellow_6(A_864,B_865,C_866))
      | v2_struct_0(k3_yellow_6(A_864,B_865,C_866))
      | ~ l1_waybel_0(k3_yellow_6(A_864,B_865,C_866),B_865)
      | ~ v6_waybel_0(k3_yellow_6(A_864,B_865,C_866),B_865)
      | ~ m1_subset_1(C_866,u1_struct_0(B_865))
      | ~ l1_struct_0(B_865)
      | v2_struct_0(B_865)
      | ~ v7_waybel_0(A_864)
      | ~ l1_orders_2(A_864)
      | v2_struct_0(A_864) ) ),
    inference(resolution,[status(thm)],[c_38,c_4764])).

tff(c_5577,plain,(
    ! [A_48,B_49,C_50] :
      ( v7_waybel_0(k3_yellow_6(A_48,B_49,C_50))
      | ~ l1_orders_2(k3_yellow_6(A_48,B_49,C_50))
      | v2_struct_0(k3_yellow_6(A_48,B_49,C_50))
      | ~ l1_waybel_0(k3_yellow_6(A_48,B_49,C_50),B_49)
      | ~ v7_waybel_0(A_48)
      | v2_struct_0(A_48)
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l1_struct_0(B_49)
      | v2_struct_0(B_49)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_30,c_5573])).

tff(c_6682,plain,
    ( v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ v7_waybel_0('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_6623,c_5577])).

tff(c_6698,plain,
    ( v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2388,c_76,c_70,c_6613,c_6682])).

tff(c_6699,plain,
    ( v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_6698])).

tff(c_6716,plain,(
    v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6699])).

tff(c_34,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ v2_struct_0(k3_yellow_6(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,u1_struct_0(B_52))
      | ~ l1_struct_0(B_52)
      | v2_struct_0(B_52)
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6721,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_6716,c_34])).

tff(c_6727,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2388,c_76,c_6721])).

tff(c_6729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_80,c_6727])).

tff(c_6731,plain,(
    ~ v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6699])).

tff(c_6730,plain,(
    v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6699])).

tff(c_5796,plain,(
    ! [A_892,B_893,C_894] :
      ( v7_waybel_0(g1_orders_2(u1_struct_0(A_892),u1_orders_2(A_892)))
      | ~ v7_waybel_0(k3_yellow_6(A_892,B_893,C_894))
      | ~ l1_orders_2(k3_yellow_6(A_892,B_893,C_894))
      | v2_struct_0(k3_yellow_6(A_892,B_893,C_894))
      | ~ l1_waybel_0(k3_yellow_6(A_892,B_893,C_894),B_893)
      | ~ v6_waybel_0(k3_yellow_6(A_892,B_893,C_894),B_893)
      | ~ m1_subset_1(C_894,u1_struct_0(B_893))
      | ~ l1_struct_0(B_893)
      | v2_struct_0(B_893)
      | ~ l1_orders_2(A_892) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_38])).

tff(c_5799,plain,(
    ! [A_48,B_49,C_50] :
      ( v7_waybel_0(g1_orders_2(u1_struct_0(A_48),u1_orders_2(A_48)))
      | ~ v7_waybel_0(k3_yellow_6(A_48,B_49,C_50))
      | ~ l1_orders_2(k3_yellow_6(A_48,B_49,C_50))
      | v2_struct_0(k3_yellow_6(A_48,B_49,C_50))
      | ~ l1_waybel_0(k3_yellow_6(A_48,B_49,C_50),B_49)
      | ~ m1_subset_1(C_50,u1_struct_0(B_49))
      | ~ l1_struct_0(B_49)
      | v2_struct_0(B_49)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_30,c_5796])).

tff(c_6678,plain,
    ( v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | ~ v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ l1_orders_2(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_6623,c_5799])).

tff(c_6690,plain,
    ( v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | ~ v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2388,c_76,c_6613,c_6678])).

tff(c_6691,plain,
    ( v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | ~ v7_waybel_0(k3_yellow_6('#skF_8','#skF_6','#skF_7'))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6690])).

tff(c_6773,plain,
    ( v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')))
    | v2_struct_0(k3_yellow_6('#skF_8','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6730,c_6691])).

tff(c_6774,plain,(
    v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6731,c_6773])).

tff(c_3140,plain,(
    ! [A_654,B_655,C_656] :
      ( v7_waybel_0(k3_waybel_2(A_654,B_655,C_656))
      | ~ v7_waybel_0(g1_orders_2(u1_struct_0(C_656),u1_orders_2(C_656)))
      | ~ l1_orders_2(k3_waybel_2(A_654,B_655,C_656))
      | v2_struct_0(k3_waybel_2(A_654,B_655,C_656))
      | ~ l1_waybel_0(k3_waybel_2(A_654,B_655,C_656),A_654)
      | ~ v6_waybel_0(k3_waybel_2(A_654,B_655,C_656),A_654)
      | ~ l1_waybel_0(C_656,A_654)
      | v2_struct_0(C_656)
      | ~ m1_subset_1(B_655,u1_struct_0(A_654))
      | ~ l1_orders_2(A_654)
      | v2_struct_0(A_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3125,c_36])).

tff(c_6776,plain,(
    ! [A_654,B_655] :
      ( v7_waybel_0(k3_waybel_2(A_654,B_655,'#skF_8'))
      | ~ l1_orders_2(k3_waybel_2(A_654,B_655,'#skF_8'))
      | v2_struct_0(k3_waybel_2(A_654,B_655,'#skF_8'))
      | ~ l1_waybel_0(k3_waybel_2(A_654,B_655,'#skF_8'),A_654)
      | ~ v6_waybel_0(k3_waybel_2(A_654,B_655,'#skF_8'),A_654)
      | ~ l1_waybel_0('#skF_8',A_654)
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(B_655,u1_struct_0(A_654))
      | ~ l1_orders_2(A_654)
      | v2_struct_0(A_654) ) ),
    inference(resolution,[status(thm)],[c_6774,c_3140])).

tff(c_10629,plain,(
    ! [A_1113,B_1114] :
      ( v7_waybel_0(k3_waybel_2(A_1113,B_1114,'#skF_8'))
      | ~ l1_orders_2(k3_waybel_2(A_1113,B_1114,'#skF_8'))
      | v2_struct_0(k3_waybel_2(A_1113,B_1114,'#skF_8'))
      | ~ l1_waybel_0(k3_waybel_2(A_1113,B_1114,'#skF_8'),A_1113)
      | ~ v6_waybel_0(k3_waybel_2(A_1113,B_1114,'#skF_8'),A_1113)
      | ~ l1_waybel_0('#skF_8',A_1113)
      | ~ m1_subset_1(B_1114,u1_struct_0(A_1113))
      | ~ l1_orders_2(A_1113)
      | v2_struct_0(A_1113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6776])).

tff(c_10633,plain,(
    ! [A_175,B_176] :
      ( v7_waybel_0(k3_waybel_2(A_175,B_176,'#skF_8'))
      | ~ l1_orders_2(k3_waybel_2(A_175,B_176,'#skF_8'))
      | v2_struct_0(k3_waybel_2(A_175,B_176,'#skF_8'))
      | ~ l1_waybel_0(k3_waybel_2(A_175,B_176,'#skF_8'),A_175)
      | ~ l1_waybel_0('#skF_8',A_175)
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_62,c_10629])).

tff(c_11084,plain,(
    ! [A_1128,B_1129] :
      ( v7_waybel_0(k3_waybel_2(A_1128,B_1129,'#skF_8'))
      | ~ l1_orders_2(k3_waybel_2(A_1128,B_1129,'#skF_8'))
      | v2_struct_0(k3_waybel_2(A_1128,B_1129,'#skF_8'))
      | ~ l1_waybel_0(k3_waybel_2(A_1128,B_1129,'#skF_8'),A_1128)
      | ~ l1_waybel_0('#skF_8',A_1128)
      | ~ m1_subset_1(B_1129,u1_struct_0(A_1128))
      | ~ l1_orders_2(A_1128)
      | v2_struct_0(A_1128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10633])).

tff(c_11117,plain,
    ( v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ l1_orders_2(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2817,c_11084])).

tff(c_11154,plain,
    ( v7_waybel_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8'))
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_78,c_76,c_2634,c_11117])).

tff(c_11156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_80,c_6464,c_2635,c_11154])).

tff(c_11157,plain,(
    v2_struct_0(k3_waybel_2('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2627])).

tff(c_11253,plain,(
    ! [A_1152,B_1153,C_1154] :
      ( ~ v2_struct_0(k3_waybel_2(A_1152,B_1153,C_1154))
      | ~ l1_waybel_0(C_1154,A_1152)
      | v2_struct_0(C_1154)
      | ~ m1_subset_1(B_1153,u1_struct_0(A_1152))
      | ~ l1_orders_2(A_1152)
      | v2_struct_0(A_1152) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_11255,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | v2_struct_0('#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_11157,c_11253])).

tff(c_11258,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_11255])).

tff(c_11260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_11258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:08:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.37/4.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/4.64  
% 12.55/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/4.64  %$ r2_funct_2 > r1_orders_2 > v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k8_funcop_1 > k3_yellow_6 > k3_waybel_2 > k11_lattice3 > u1_waybel_0 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3
% 12.55/4.64  
% 12.55/4.64  %Foreground sorts:
% 12.55/4.64  
% 12.55/4.64  
% 12.55/4.64  %Background operators:
% 12.55/4.64  
% 12.55/4.64  
% 12.55/4.64  %Foreground operators:
% 12.55/4.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.55/4.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.55/4.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.55/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.55/4.64  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 12.55/4.64  tff(k3_yellow_6, type, k3_yellow_6: ($i * $i * $i) > $i).
% 12.55/4.64  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.55/4.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 12.55/4.64  tff(k3_waybel_2, type, k3_waybel_2: ($i * $i * $i) > $i).
% 12.55/4.64  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 12.55/4.64  tff('#skF_7', type, '#skF_7': $i).
% 12.55/4.64  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 12.55/4.64  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 12.55/4.64  tff('#skF_6', type, '#skF_6': $i).
% 12.55/4.64  tff(k8_funcop_1, type, k8_funcop_1: ($i * $i * $i) > $i).
% 12.55/4.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.55/4.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.55/4.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.55/4.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.55/4.64  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 12.55/4.64  tff('#skF_8', type, '#skF_8': $i).
% 12.55/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.55/4.64  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 12.55/4.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 12.55/4.64  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.55/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.55/4.64  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 12.55/4.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.55/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.55/4.64  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 12.55/4.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.55/4.64  
% 12.62/4.67  tff(f_247, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (((~v2_struct_0(k3_waybel_2(A, B, C)) & v4_orders_2(k3_waybel_2(A, B, C))) & v7_waybel_0(k3_waybel_2(A, B, C))) & l1_waybel_0(k3_waybel_2(A, B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_9)).
% 12.62/4.67  tff(f_43, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 12.62/4.67  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 12.62/4.67  tff(f_202, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & ~v2_struct_0(C)) & l1_waybel_0(C, A)) => (v6_waybel_0(k3_waybel_2(A, B, C), A) & l1_waybel_0(k3_waybel_2(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_waybel_2)).
% 12.62/4.67  tff(f_219, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & ~v2_struct_0(C)) & l1_waybel_0(C, A)) => (~v2_struct_0(k3_waybel_2(A, B, C)) & v6_waybel_0(k3_waybel_2(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_waybel_2)).
% 12.62/4.67  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (v4_orders_2(A) <=> v4_orders_2(g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l16_yellow_6)).
% 12.62/4.67  tff(f_186, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((~v2_struct_0(C) & l1_waybel_0(C, A)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k3_waybel_2(A, B, C)) <=> ((g1_orders_2(u1_struct_0(D), u1_orders_2(D)) = g1_orders_2(u1_struct_0(C), u1_orders_2(C))) & (![E]: (m1_subset_1(E, u1_struct_0(D)) => (?[F]: ((m1_subset_1(F, u1_struct_0(A)) & (F = k1_funct_1(u1_waybel_0(A, C), E))) & (k1_funct_1(u1_waybel_0(A, D), E) = k11_lattice3(A, B, F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_waybel_2)).
% 12.62/4.67  tff(f_105, axiom, (![A, B, C]: ((((l1_orders_2(A) & ~v2_struct_0(B)) & l1_struct_0(B)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k3_yellow_6(A, B, C), B) & l1_waybel_0(k3_yellow_6(A, B, C), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_6)).
% 12.62/4.67  tff(f_153, axiom, (![A]: (l1_orders_2(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k3_yellow_6(A, B, C)) = u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_6)).
% 12.62/4.67  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, B) & l1_waybel_0(D, B)) => ((D = k3_yellow_6(A, B, C)) <=> ((g1_orders_2(u1_struct_0(D), u1_orders_2(D)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), u1_waybel_0(B, D), k8_funcop_1(u1_struct_0(B), u1_struct_0(D), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_yellow_6)).
% 12.62/4.67  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (v7_waybel_0(A) <=> v7_waybel_0(g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l15_yellow_6)).
% 12.62/4.67  tff(f_122, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_orders_2(A)) & ~v2_struct_0(B)) & l1_struct_0(B)) & m1_subset_1(C, u1_struct_0(B))) => (~v2_struct_0(k3_yellow_6(A, B, C)) & v6_waybel_0(k3_yellow_6(A, B, C), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_yellow_6)).
% 12.62/4.67  tff(c_80, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_74, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_78, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_76, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_68, plain, (l1_waybel_0('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.62/4.67  tff(c_2373, plain, (![B_512, A_513]: (l1_orders_2(B_512) | ~l1_waybel_0(B_512, A_513) | ~l1_struct_0(A_513))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.62/4.67  tff(c_2377, plain, (l1_orders_2('#skF_8') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_2373])).
% 12.62/4.67  tff(c_2378, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2377])).
% 12.62/4.67  tff(c_2382, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_6, c_2378])).
% 12.62/4.67  tff(c_2386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_2382])).
% 12.62/4.67  tff(c_2388, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_2377])).
% 12.62/4.67  tff(c_2596, plain, (![A_558, B_559, C_560]: (l1_waybel_0(k3_waybel_2(A_558, B_559, C_560), A_558) | ~l1_waybel_0(C_560, A_558) | v2_struct_0(C_560) | ~m1_subset_1(B_559, u1_struct_0(A_558)) | ~l1_orders_2(A_558) | v2_struct_0(A_558))), inference(cnfTransformation, [status(thm)], [f_202])).
% 12.62/4.67  tff(c_2608, plain, (![C_560]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_560), '#skF_6') | ~l1_waybel_0(C_560, '#skF_6') | v2_struct_0(C_560) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_2596])).
% 12.62/4.67  tff(c_2613, plain, (![C_560]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_560), '#skF_6') | ~l1_waybel_0(C_560, '#skF_6') | v2_struct_0(C_560) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2608])).
% 12.62/4.67  tff(c_2615, plain, (![C_561]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_561), '#skF_6') | ~l1_waybel_0(C_561, '#skF_6') | v2_struct_0(C_561))), inference(negUnitSimplification, [status(thm)], [c_80, c_2613])).
% 12.62/4.67  tff(c_89, plain, (![B_185, A_186]: (l1_orders_2(B_185) | ~l1_waybel_0(B_185, A_186) | ~l1_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.62/4.67  tff(c_93, plain, (l1_orders_2('#skF_8') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_89])).
% 12.62/4.67  tff(c_94, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_93])).
% 12.62/4.67  tff(c_97, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_6, c_94])).
% 12.62/4.67  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_97])).
% 12.62/4.67  tff(c_103, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_93])).
% 12.62/4.67  tff(c_309, plain, (![A_227, B_228, C_229]: (l1_waybel_0(k3_waybel_2(A_227, B_228, C_229), A_227) | ~l1_waybel_0(C_229, A_227) | v2_struct_0(C_229) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_202])).
% 12.62/4.67  tff(c_321, plain, (![C_229]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_229), '#skF_6') | ~l1_waybel_0(C_229, '#skF_6') | v2_struct_0(C_229) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_309])).
% 12.62/4.67  tff(c_326, plain, (![C_229]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_229), '#skF_6') | ~l1_waybel_0(C_229, '#skF_6') | v2_struct_0(C_229) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_321])).
% 12.62/4.67  tff(c_328, plain, (![C_230]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_230), '#skF_6') | ~l1_waybel_0(C_230, '#skF_6') | v2_struct_0(C_230))), inference(negUnitSimplification, [status(thm)], [c_80, c_326])).
% 12.62/4.67  tff(c_8, plain, (![B_6, A_4]: (l1_orders_2(B_6) | ~l1_waybel_0(B_6, A_4) | ~l1_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.62/4.67  tff(c_331, plain, (![C_230]: (l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_230)) | ~l1_struct_0('#skF_6') | ~l1_waybel_0(C_230, '#skF_6') | v2_struct_0(C_230))), inference(resolution, [status(thm)], [c_328, c_8])).
% 12.62/4.67  tff(c_334, plain, (![C_230]: (l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_230)) | ~l1_waybel_0(C_230, '#skF_6') | v2_struct_0(C_230))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_331])).
% 12.62/4.67  tff(c_102, plain, (l1_orders_2('#skF_8')), inference(splitRight, [status(thm)], [c_93])).
% 12.62/4.67  tff(c_72, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_327, plain, (![C_229]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_229), '#skF_6') | ~l1_waybel_0(C_229, '#skF_6') | v2_struct_0(C_229))), inference(negUnitSimplification, [status(thm)], [c_80, c_326])).
% 12.62/4.67  tff(c_62, plain, (![A_175, B_176, C_177]: (v6_waybel_0(k3_waybel_2(A_175, B_176, C_177), A_175) | ~l1_waybel_0(C_177, A_175) | v2_struct_0(C_177) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.62/4.67  tff(c_42, plain, (![A_55]: (v4_orders_2(g1_orders_2(u1_struct_0(A_55), u1_orders_2(A_55))) | ~v4_orders_2(A_55) | ~l1_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.62/4.67  tff(c_531, plain, (![A_272, B_273, C_274]: (g1_orders_2(u1_struct_0(k3_waybel_2(A_272, B_273, C_274)), u1_orders_2(k3_waybel_2(A_272, B_273, C_274)))=g1_orders_2(u1_struct_0(C_274), u1_orders_2(C_274)) | ~l1_waybel_0(k3_waybel_2(A_272, B_273, C_274), A_272) | ~v6_waybel_0(k3_waybel_2(A_272, B_273, C_274), A_272) | ~l1_waybel_0(C_274, A_272) | v2_struct_0(C_274) | ~m1_subset_1(B_273, u1_struct_0(A_272)) | ~l1_orders_2(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.62/4.67  tff(c_40, plain, (![A_55]: (v4_orders_2(A_55) | ~v4_orders_2(g1_orders_2(u1_struct_0(A_55), u1_orders_2(A_55))) | ~l1_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.62/4.67  tff(c_2218, plain, (![A_495, B_496, C_497]: (v4_orders_2(k3_waybel_2(A_495, B_496, C_497)) | ~v4_orders_2(g1_orders_2(u1_struct_0(C_497), u1_orders_2(C_497))) | ~l1_orders_2(k3_waybel_2(A_495, B_496, C_497)) | v2_struct_0(k3_waybel_2(A_495, B_496, C_497)) | ~l1_waybel_0(k3_waybel_2(A_495, B_496, C_497), A_495) | ~v6_waybel_0(k3_waybel_2(A_495, B_496, C_497), A_495) | ~l1_waybel_0(C_497, A_495) | v2_struct_0(C_497) | ~m1_subset_1(B_496, u1_struct_0(A_495)) | ~l1_orders_2(A_495) | v2_struct_0(A_495))), inference(superposition, [status(thm), theory('equality')], [c_531, c_40])).
% 12.62/4.67  tff(c_2242, plain, (![A_498, B_499, A_500]: (v4_orders_2(k3_waybel_2(A_498, B_499, A_500)) | ~l1_orders_2(k3_waybel_2(A_498, B_499, A_500)) | v2_struct_0(k3_waybel_2(A_498, B_499, A_500)) | ~l1_waybel_0(k3_waybel_2(A_498, B_499, A_500), A_498) | ~v6_waybel_0(k3_waybel_2(A_498, B_499, A_500), A_498) | ~l1_waybel_0(A_500, A_498) | ~m1_subset_1(B_499, u1_struct_0(A_498)) | ~l1_orders_2(A_498) | v2_struct_0(A_498) | ~v4_orders_2(A_500) | ~l1_orders_2(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_42, c_2218])).
% 12.62/4.67  tff(c_2247, plain, (![A_501, B_502, C_503]: (v4_orders_2(k3_waybel_2(A_501, B_502, C_503)) | ~l1_orders_2(k3_waybel_2(A_501, B_502, C_503)) | v2_struct_0(k3_waybel_2(A_501, B_502, C_503)) | ~l1_waybel_0(k3_waybel_2(A_501, B_502, C_503), A_501) | ~v4_orders_2(C_503) | ~l1_orders_2(C_503) | ~l1_waybel_0(C_503, A_501) | v2_struct_0(C_503) | ~m1_subset_1(B_502, u1_struct_0(A_501)) | ~l1_orders_2(A_501) | v2_struct_0(A_501))), inference(resolution, [status(thm)], [c_62, c_2242])).
% 12.62/4.67  tff(c_2255, plain, (![C_229]: (v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_229)) | ~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_229)) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', C_229)) | ~v4_orders_2(C_229) | ~l1_orders_2(C_229) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(C_229, '#skF_6') | v2_struct_0(C_229))), inference(resolution, [status(thm)], [c_327, c_2247])).
% 12.62/4.67  tff(c_2261, plain, (![C_229]: (v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_229)) | ~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_229)) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', C_229)) | ~v4_orders_2(C_229) | ~l1_orders_2(C_229) | v2_struct_0('#skF_6') | ~l1_waybel_0(C_229, '#skF_6') | v2_struct_0(C_229))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2255])).
% 12.62/4.67  tff(c_2263, plain, (![C_504]: (v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_504)) | ~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', C_504)) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', C_504)) | ~v4_orders_2(C_504) | ~l1_orders_2(C_504) | ~l1_waybel_0(C_504, '#skF_6') | v2_struct_0(C_504))), inference(negUnitSimplification, [status(thm)], [c_80, c_2261])).
% 12.62/4.67  tff(c_66, plain, (~l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'), '#skF_6') | ~v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_83, plain, (~v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_66])).
% 12.62/4.67  tff(c_2269, plain, (~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~v4_orders_2('#skF_8') | ~l1_orders_2('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2263, c_83])).
% 12.62/4.67  tff(c_2273, plain, (~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_72, c_2269])).
% 12.62/4.67  tff(c_2274, plain, (~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2273])).
% 12.62/4.67  tff(c_2311, plain, (~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2274])).
% 12.62/4.67  tff(c_2314, plain, (~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_334, c_2311])).
% 12.62/4.67  tff(c_2317, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2314])).
% 12.62/4.67  tff(c_2319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2317])).
% 12.62/4.67  tff(c_2320, plain, (v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_2274])).
% 12.62/4.67  tff(c_64, plain, (![A_175, B_176, C_177]: (~v2_struct_0(k3_waybel_2(A_175, B_176, C_177)) | ~l1_waybel_0(C_177, A_175) | v2_struct_0(C_177) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.62/4.67  tff(c_2360, plain, (~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2320, c_64])).
% 12.62/4.67  tff(c_2363, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_2360])).
% 12.62/4.67  tff(c_2365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_2363])).
% 12.62/4.67  tff(c_2366, plain, (~v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'), '#skF_6') | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 12.62/4.67  tff(c_2389, plain, (~l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2366])).
% 12.62/4.67  tff(c_2618, plain, (~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2615, c_2389])).
% 12.62/4.67  tff(c_2624, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2618])).
% 12.62/4.67  tff(c_2626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2624])).
% 12.62/4.67  tff(c_2628, plain, (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_2366])).
% 12.62/4.67  tff(c_2631, plain, (l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2628, c_8])).
% 12.62/4.67  tff(c_2634, plain, (l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2631])).
% 12.62/4.67  tff(c_2367, plain, (v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 12.62/4.67  tff(c_3125, plain, (![A_654, B_655, C_656]: (g1_orders_2(u1_struct_0(k3_waybel_2(A_654, B_655, C_656)), u1_orders_2(k3_waybel_2(A_654, B_655, C_656)))=g1_orders_2(u1_struct_0(C_656), u1_orders_2(C_656)) | ~l1_waybel_0(k3_waybel_2(A_654, B_655, C_656), A_654) | ~v6_waybel_0(k3_waybel_2(A_654, B_655, C_656), A_654) | ~l1_waybel_0(C_656, A_654) | v2_struct_0(C_656) | ~m1_subset_1(B_655, u1_struct_0(A_654)) | ~l1_orders_2(A_654) | v2_struct_0(A_654))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.62/4.67  tff(c_6365, plain, (![C_957, A_958, B_959]: (v4_orders_2(g1_orders_2(u1_struct_0(C_957), u1_orders_2(C_957))) | ~v4_orders_2(k3_waybel_2(A_958, B_959, C_957)) | ~l1_orders_2(k3_waybel_2(A_958, B_959, C_957)) | v2_struct_0(k3_waybel_2(A_958, B_959, C_957)) | ~l1_waybel_0(k3_waybel_2(A_958, B_959, C_957), A_958) | ~v6_waybel_0(k3_waybel_2(A_958, B_959, C_957), A_958) | ~l1_waybel_0(C_957, A_958) | v2_struct_0(C_957) | ~m1_subset_1(B_959, u1_struct_0(A_958)) | ~l1_orders_2(A_958) | v2_struct_0(A_958))), inference(superposition, [status(thm), theory('equality')], [c_3125, c_42])).
% 12.62/4.67  tff(c_6370, plain, (![C_962, A_963, B_964]: (v4_orders_2(g1_orders_2(u1_struct_0(C_962), u1_orders_2(C_962))) | ~v4_orders_2(k3_waybel_2(A_963, B_964, C_962)) | ~l1_orders_2(k3_waybel_2(A_963, B_964, C_962)) | v2_struct_0(k3_waybel_2(A_963, B_964, C_962)) | ~l1_waybel_0(k3_waybel_2(A_963, B_964, C_962), A_963) | ~l1_waybel_0(C_962, A_963) | v2_struct_0(C_962) | ~m1_subset_1(B_964, u1_struct_0(A_963)) | ~l1_orders_2(A_963) | v2_struct_0(A_963))), inference(resolution, [status(thm)], [c_62, c_6365])).
% 12.62/4.67  tff(c_6388, plain, (v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | ~v4_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2628, c_6370])).
% 12.62/4.67  tff(c_6402, plain, (v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_2634, c_2367, c_6388])).
% 12.62/4.67  tff(c_6403, plain, (v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_6402])).
% 12.62/4.67  tff(c_6404, plain, (v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_6403])).
% 12.62/4.67  tff(c_6457, plain, (~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_6404, c_64])).
% 12.62/4.67  tff(c_6460, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_6457])).
% 12.62/4.67  tff(c_6462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_6460])).
% 12.62/4.67  tff(c_6464, plain, (~v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_6403])).
% 12.62/4.67  tff(c_2627, plain, (~v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_2366])).
% 12.62/4.67  tff(c_2635, plain, (~v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2627])).
% 12.62/4.67  tff(c_2801, plain, (![A_600, B_601, C_602]: (l1_waybel_0(k3_waybel_2(A_600, B_601, C_602), A_600) | ~l1_waybel_0(C_602, A_600) | v2_struct_0(C_602) | ~m1_subset_1(B_601, u1_struct_0(A_600)) | ~l1_orders_2(A_600) | v2_struct_0(A_600))), inference(cnfTransformation, [status(thm)], [f_202])).
% 12.62/4.67  tff(c_2811, plain, (![C_602]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_602), '#skF_6') | ~l1_waybel_0(C_602, '#skF_6') | v2_struct_0(C_602) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_2801])).
% 12.62/4.67  tff(c_2816, plain, (![C_602]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_602), '#skF_6') | ~l1_waybel_0(C_602, '#skF_6') | v2_struct_0(C_602) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2811])).
% 12.62/4.67  tff(c_2817, plain, (![C_602]: (l1_waybel_0(k3_waybel_2('#skF_6', '#skF_7', C_602), '#skF_6') | ~l1_waybel_0(C_602, '#skF_6') | v2_struct_0(C_602))), inference(negUnitSimplification, [status(thm)], [c_80, c_2816])).
% 12.62/4.67  tff(c_2387, plain, (l1_orders_2('#skF_8')), inference(splitRight, [status(thm)], [c_2377])).
% 12.62/4.67  tff(c_70, plain, (v7_waybel_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_247])).
% 12.62/4.67  tff(c_2650, plain, (![A_568, B_569, C_570]: (l1_waybel_0(k3_yellow_6(A_568, B_569, C_570), B_569) | ~m1_subset_1(C_570, u1_struct_0(B_569)) | ~l1_struct_0(B_569) | v2_struct_0(B_569) | ~l1_orders_2(A_568))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.62/4.67  tff(c_2656, plain, (![A_568]: (l1_waybel_0(k3_yellow_6(A_568, '#skF_6', '#skF_7'), '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2(A_568))), inference(resolution, [status(thm)], [c_76, c_2650])).
% 12.62/4.67  tff(c_2661, plain, (![A_568]: (l1_waybel_0(k3_yellow_6(A_568, '#skF_6', '#skF_7'), '#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2(A_568))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2656])).
% 12.62/4.67  tff(c_2663, plain, (![A_571]: (l1_waybel_0(k3_yellow_6(A_571, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(A_571))), inference(negUnitSimplification, [status(thm)], [c_80, c_2661])).
% 12.62/4.67  tff(c_2666, plain, (![A_571]: (l1_orders_2(k3_yellow_6(A_571, '#skF_6', '#skF_7')) | ~l1_struct_0('#skF_6') | ~l1_orders_2(A_571))), inference(resolution, [status(thm)], [c_2663, c_8])).
% 12.62/4.67  tff(c_2669, plain, (![A_571]: (l1_orders_2(k3_yellow_6(A_571, '#skF_6', '#skF_7')) | ~l1_orders_2(A_571))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2666])).
% 12.62/4.67  tff(c_30, plain, (![A_48, B_49, C_50]: (v6_waybel_0(k3_yellow_6(A_48, B_49, C_50), B_49) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l1_struct_0(B_49) | v2_struct_0(B_49) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.62/4.67  tff(c_6463, plain, (v4_orders_2(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8')))), inference(splitRight, [status(thm)], [c_6403])).
% 12.62/4.67  tff(c_2673, plain, (![A_579, B_580, C_581]: (u1_struct_0(k3_yellow_6(A_579, B_580, C_581))=u1_struct_0(A_579) | ~m1_subset_1(C_581, u1_struct_0(B_580)) | ~l1_struct_0(B_580) | v2_struct_0(B_580) | ~l1_orders_2(A_579))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.62/4.67  tff(c_2679, plain, (![A_579]: (u1_struct_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'))=u1_struct_0(A_579) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2(A_579))), inference(resolution, [status(thm)], [c_76, c_2673])).
% 12.62/4.67  tff(c_2684, plain, (![A_579]: (u1_struct_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'))=u1_struct_0(A_579) | v2_struct_0('#skF_6') | ~l1_orders_2(A_579))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2679])).
% 12.62/4.67  tff(c_2685, plain, (![A_579]: (u1_struct_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'))=u1_struct_0(A_579) | ~l1_orders_2(A_579))), inference(negUnitSimplification, [status(thm)], [c_80, c_2684])).
% 12.62/4.67  tff(c_2990, plain, (![A_638, B_639, C_640]: (g1_orders_2(u1_struct_0(k3_yellow_6(A_638, B_639, C_640)), u1_orders_2(k3_yellow_6(A_638, B_639, C_640)))=g1_orders_2(u1_struct_0(A_638), u1_orders_2(A_638)) | ~l1_waybel_0(k3_yellow_6(A_638, B_639, C_640), B_639) | ~v6_waybel_0(k3_yellow_6(A_638, B_639, C_640), B_639) | ~m1_subset_1(C_640, u1_struct_0(B_639)) | ~l1_struct_0(B_639) | v2_struct_0(B_639) | ~l1_orders_2(A_638))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.62/4.67  tff(c_3017, plain, (![A_579]: (g1_orders_2(u1_struct_0(A_579), u1_orders_2(k3_yellow_6(A_579, '#skF_6', '#skF_7')))=g1_orders_2(u1_struct_0(A_579), u1_orders_2(A_579)) | ~l1_waybel_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2(A_579) | ~l1_orders_2(A_579))), inference(superposition, [status(thm), theory('equality')], [c_2685, c_2990])).
% 12.62/4.67  tff(c_3021, plain, (![A_579]: (g1_orders_2(u1_struct_0(A_579), u1_orders_2(k3_yellow_6(A_579, '#skF_6', '#skF_7')))=g1_orders_2(u1_struct_0(A_579), u1_orders_2(A_579)) | ~l1_waybel_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6(A_579, '#skF_6', '#skF_7'), '#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2(A_579))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_76, c_3017])).
% 12.62/4.67  tff(c_3042, plain, (![A_646]: (g1_orders_2(u1_struct_0(A_646), u1_orders_2(k3_yellow_6(A_646, '#skF_6', '#skF_7')))=g1_orders_2(u1_struct_0(A_646), u1_orders_2(A_646)) | ~l1_waybel_0(k3_yellow_6(A_646, '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6(A_646, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(A_646))), inference(negUnitSimplification, [status(thm)], [c_80, c_3021])).
% 12.62/4.67  tff(c_2686, plain, (![A_582]: (u1_struct_0(k3_yellow_6(A_582, '#skF_6', '#skF_7'))=u1_struct_0(A_582) | ~l1_orders_2(A_582))), inference(negUnitSimplification, [status(thm)], [c_80, c_2684])).
% 12.62/4.67  tff(c_2696, plain, (![A_582]: (v4_orders_2(k3_yellow_6(A_582, '#skF_6', '#skF_7')) | ~v4_orders_2(g1_orders_2(u1_struct_0(A_582), u1_orders_2(k3_yellow_6(A_582, '#skF_6', '#skF_7')))) | ~l1_orders_2(k3_yellow_6(A_582, '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6(A_582, '#skF_6', '#skF_7')) | ~l1_orders_2(A_582))), inference(superposition, [status(thm), theory('equality')], [c_2686, c_40])).
% 12.62/4.67  tff(c_3048, plain, (![A_646]: (v4_orders_2(k3_yellow_6(A_646, '#skF_6', '#skF_7')) | ~v4_orders_2(g1_orders_2(u1_struct_0(A_646), u1_orders_2(A_646))) | ~l1_orders_2(k3_yellow_6(A_646, '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6(A_646, '#skF_6', '#skF_7')) | ~l1_orders_2(A_646) | ~l1_waybel_0(k3_yellow_6(A_646, '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6(A_646, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(A_646))), inference(superposition, [status(thm), theory('equality')], [c_3042, c_2696])).
% 12.62/4.67  tff(c_6471, plain, (v4_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_6463, c_3048])).
% 12.62/4.67  tff(c_6483, plain, (v4_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6') | ~v6_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_6471])).
% 12.62/4.67  tff(c_6585, plain, (~v6_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_6483])).
% 12.62/4.67  tff(c_6588, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_30, c_6585])).
% 12.62/4.67  tff(c_6591, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2388, c_76, c_6588])).
% 12.62/4.67  tff(c_6593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_6591])).
% 12.62/4.67  tff(c_6594, plain, (~l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v4_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6483])).
% 12.62/4.67  tff(c_6604, plain, (~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_6594])).
% 12.62/4.67  tff(c_6607, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_2669, c_6604])).
% 12.62/4.67  tff(c_6611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2387, c_6607])).
% 12.62/4.67  tff(c_6613, plain, (l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6594])).
% 12.62/4.67  tff(c_2662, plain, (![A_568]: (l1_waybel_0(k3_yellow_6(A_568, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(A_568))), inference(negUnitSimplification, [status(thm)], [c_80, c_2661])).
% 12.62/4.67  tff(c_6612, plain, (~l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6') | v4_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6594])).
% 12.62/4.67  tff(c_6614, plain, (~l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_6612])).
% 12.62/4.67  tff(c_6617, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_2662, c_6614])).
% 12.62/4.67  tff(c_6621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2387, c_6617])).
% 12.62/4.67  tff(c_6623, plain, (l1_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_6612])).
% 12.62/4.67  tff(c_38, plain, (![A_54]: (v7_waybel_0(g1_orders_2(u1_struct_0(A_54), u1_orders_2(A_54))) | ~v7_waybel_0(A_54) | ~l1_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.62/4.67  tff(c_36, plain, (![A_54]: (v7_waybel_0(A_54) | ~v7_waybel_0(g1_orders_2(u1_struct_0(A_54), u1_orders_2(A_54))) | ~l1_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.62/4.67  tff(c_4764, plain, (![A_820, B_821, C_822]: (v7_waybel_0(k3_yellow_6(A_820, B_821, C_822)) | ~v7_waybel_0(g1_orders_2(u1_struct_0(A_820), u1_orders_2(A_820))) | ~l1_orders_2(k3_yellow_6(A_820, B_821, C_822)) | v2_struct_0(k3_yellow_6(A_820, B_821, C_822)) | ~l1_waybel_0(k3_yellow_6(A_820, B_821, C_822), B_821) | ~v6_waybel_0(k3_yellow_6(A_820, B_821, C_822), B_821) | ~m1_subset_1(C_822, u1_struct_0(B_821)) | ~l1_struct_0(B_821) | v2_struct_0(B_821) | ~l1_orders_2(A_820))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_36])).
% 12.62/4.67  tff(c_5573, plain, (![A_864, B_865, C_866]: (v7_waybel_0(k3_yellow_6(A_864, B_865, C_866)) | ~l1_orders_2(k3_yellow_6(A_864, B_865, C_866)) | v2_struct_0(k3_yellow_6(A_864, B_865, C_866)) | ~l1_waybel_0(k3_yellow_6(A_864, B_865, C_866), B_865) | ~v6_waybel_0(k3_yellow_6(A_864, B_865, C_866), B_865) | ~m1_subset_1(C_866, u1_struct_0(B_865)) | ~l1_struct_0(B_865) | v2_struct_0(B_865) | ~v7_waybel_0(A_864) | ~l1_orders_2(A_864) | v2_struct_0(A_864))), inference(resolution, [status(thm)], [c_38, c_4764])).
% 12.62/4.67  tff(c_5577, plain, (![A_48, B_49, C_50]: (v7_waybel_0(k3_yellow_6(A_48, B_49, C_50)) | ~l1_orders_2(k3_yellow_6(A_48, B_49, C_50)) | v2_struct_0(k3_yellow_6(A_48, B_49, C_50)) | ~l1_waybel_0(k3_yellow_6(A_48, B_49, C_50), B_49) | ~v7_waybel_0(A_48) | v2_struct_0(A_48) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l1_struct_0(B_49) | v2_struct_0(B_49) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_30, c_5573])).
% 12.62/4.67  tff(c_6682, plain, (v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~v7_waybel_0('#skF_8') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_6623, c_5577])).
% 12.62/4.67  tff(c_6698, plain, (v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2388, c_76, c_70, c_6613, c_6682])).
% 12.62/4.67  tff(c_6699, plain, (v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_6698])).
% 12.62/4.67  tff(c_6716, plain, (v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_6699])).
% 12.62/4.67  tff(c_34, plain, (![A_51, B_52, C_53]: (~v2_struct_0(k3_yellow_6(A_51, B_52, C_53)) | ~m1_subset_1(C_53, u1_struct_0(B_52)) | ~l1_struct_0(B_52) | v2_struct_0(B_52) | ~l1_orders_2(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.62/4.67  tff(c_6721, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_6716, c_34])).
% 12.62/4.67  tff(c_6727, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2388, c_76, c_6721])).
% 12.62/4.67  tff(c_6729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_80, c_6727])).
% 12.62/4.67  tff(c_6731, plain, (~v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6699])).
% 12.62/4.67  tff(c_6730, plain, (v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6699])).
% 12.62/4.67  tff(c_5796, plain, (![A_892, B_893, C_894]: (v7_waybel_0(g1_orders_2(u1_struct_0(A_892), u1_orders_2(A_892))) | ~v7_waybel_0(k3_yellow_6(A_892, B_893, C_894)) | ~l1_orders_2(k3_yellow_6(A_892, B_893, C_894)) | v2_struct_0(k3_yellow_6(A_892, B_893, C_894)) | ~l1_waybel_0(k3_yellow_6(A_892, B_893, C_894), B_893) | ~v6_waybel_0(k3_yellow_6(A_892, B_893, C_894), B_893) | ~m1_subset_1(C_894, u1_struct_0(B_893)) | ~l1_struct_0(B_893) | v2_struct_0(B_893) | ~l1_orders_2(A_892))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_38])).
% 12.62/4.67  tff(c_5799, plain, (![A_48, B_49, C_50]: (v7_waybel_0(g1_orders_2(u1_struct_0(A_48), u1_orders_2(A_48))) | ~v7_waybel_0(k3_yellow_6(A_48, B_49, C_50)) | ~l1_orders_2(k3_yellow_6(A_48, B_49, C_50)) | v2_struct_0(k3_yellow_6(A_48, B_49, C_50)) | ~l1_waybel_0(k3_yellow_6(A_48, B_49, C_50), B_49) | ~m1_subset_1(C_50, u1_struct_0(B_49)) | ~l1_struct_0(B_49) | v2_struct_0(B_49) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_30, c_5796])).
% 12.62/4.67  tff(c_6678, plain, (v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | ~v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~l1_orders_2(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_6623, c_5799])).
% 12.62/4.67  tff(c_6690, plain, (v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | ~v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2388, c_76, c_6613, c_6678])).
% 12.62/4.67  tff(c_6691, plain, (v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | ~v7_waybel_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7')) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_6690])).
% 12.62/4.67  tff(c_6773, plain, (v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))) | v2_struct_0(k3_yellow_6('#skF_8', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6730, c_6691])).
% 12.62/4.67  tff(c_6774, plain, (v7_waybel_0(g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_6731, c_6773])).
% 12.62/4.67  tff(c_3140, plain, (![A_654, B_655, C_656]: (v7_waybel_0(k3_waybel_2(A_654, B_655, C_656)) | ~v7_waybel_0(g1_orders_2(u1_struct_0(C_656), u1_orders_2(C_656))) | ~l1_orders_2(k3_waybel_2(A_654, B_655, C_656)) | v2_struct_0(k3_waybel_2(A_654, B_655, C_656)) | ~l1_waybel_0(k3_waybel_2(A_654, B_655, C_656), A_654) | ~v6_waybel_0(k3_waybel_2(A_654, B_655, C_656), A_654) | ~l1_waybel_0(C_656, A_654) | v2_struct_0(C_656) | ~m1_subset_1(B_655, u1_struct_0(A_654)) | ~l1_orders_2(A_654) | v2_struct_0(A_654))), inference(superposition, [status(thm), theory('equality')], [c_3125, c_36])).
% 12.62/4.67  tff(c_6776, plain, (![A_654, B_655]: (v7_waybel_0(k3_waybel_2(A_654, B_655, '#skF_8')) | ~l1_orders_2(k3_waybel_2(A_654, B_655, '#skF_8')) | v2_struct_0(k3_waybel_2(A_654, B_655, '#skF_8')) | ~l1_waybel_0(k3_waybel_2(A_654, B_655, '#skF_8'), A_654) | ~v6_waybel_0(k3_waybel_2(A_654, B_655, '#skF_8'), A_654) | ~l1_waybel_0('#skF_8', A_654) | v2_struct_0('#skF_8') | ~m1_subset_1(B_655, u1_struct_0(A_654)) | ~l1_orders_2(A_654) | v2_struct_0(A_654))), inference(resolution, [status(thm)], [c_6774, c_3140])).
% 12.62/4.67  tff(c_10629, plain, (![A_1113, B_1114]: (v7_waybel_0(k3_waybel_2(A_1113, B_1114, '#skF_8')) | ~l1_orders_2(k3_waybel_2(A_1113, B_1114, '#skF_8')) | v2_struct_0(k3_waybel_2(A_1113, B_1114, '#skF_8')) | ~l1_waybel_0(k3_waybel_2(A_1113, B_1114, '#skF_8'), A_1113) | ~v6_waybel_0(k3_waybel_2(A_1113, B_1114, '#skF_8'), A_1113) | ~l1_waybel_0('#skF_8', A_1113) | ~m1_subset_1(B_1114, u1_struct_0(A_1113)) | ~l1_orders_2(A_1113) | v2_struct_0(A_1113))), inference(negUnitSimplification, [status(thm)], [c_74, c_6776])).
% 12.62/4.67  tff(c_10633, plain, (![A_175, B_176]: (v7_waybel_0(k3_waybel_2(A_175, B_176, '#skF_8')) | ~l1_orders_2(k3_waybel_2(A_175, B_176, '#skF_8')) | v2_struct_0(k3_waybel_2(A_175, B_176, '#skF_8')) | ~l1_waybel_0(k3_waybel_2(A_175, B_176, '#skF_8'), A_175) | ~l1_waybel_0('#skF_8', A_175) | v2_struct_0('#skF_8') | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_62, c_10629])).
% 12.62/4.67  tff(c_11084, plain, (![A_1128, B_1129]: (v7_waybel_0(k3_waybel_2(A_1128, B_1129, '#skF_8')) | ~l1_orders_2(k3_waybel_2(A_1128, B_1129, '#skF_8')) | v2_struct_0(k3_waybel_2(A_1128, B_1129, '#skF_8')) | ~l1_waybel_0(k3_waybel_2(A_1128, B_1129, '#skF_8'), A_1128) | ~l1_waybel_0('#skF_8', A_1128) | ~m1_subset_1(B_1129, u1_struct_0(A_1128)) | ~l1_orders_2(A_1128) | v2_struct_0(A_1128))), inference(negUnitSimplification, [status(thm)], [c_74, c_10633])).
% 12.62/4.67  tff(c_11117, plain, (v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~l1_orders_2(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2817, c_11084])).
% 12.62/4.67  tff(c_11154, plain, (v7_waybel_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_78, c_76, c_2634, c_11117])).
% 12.62/4.67  tff(c_11156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_80, c_6464, c_2635, c_11154])).
% 12.62/4.67  tff(c_11157, plain, (v2_struct_0(k3_waybel_2('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_2627])).
% 12.62/4.67  tff(c_11253, plain, (![A_1152, B_1153, C_1154]: (~v2_struct_0(k3_waybel_2(A_1152, B_1153, C_1154)) | ~l1_waybel_0(C_1154, A_1152) | v2_struct_0(C_1154) | ~m1_subset_1(B_1153, u1_struct_0(A_1152)) | ~l1_orders_2(A_1152) | v2_struct_0(A_1152))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.62/4.67  tff(c_11255, plain, (~l1_waybel_0('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_11157, c_11253])).
% 12.62/4.67  tff(c_11258, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_11255])).
% 12.62/4.67  tff(c_11260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_11258])).
% 12.62/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.62/4.67  
% 12.62/4.67  Inference rules
% 12.62/4.67  ----------------------
% 12.62/4.67  #Ref     : 10
% 12.62/4.67  #Sup     : 3064
% 12.62/4.67  #Fact    : 0
% 12.62/4.67  #Define  : 0
% 12.62/4.67  #Split   : 20
% 12.62/4.67  #Chain   : 0
% 12.62/4.67  #Close   : 0
% 12.62/4.67  
% 12.62/4.67  Ordering : KBO
% 12.62/4.67  
% 12.62/4.67  Simplification rules
% 12.62/4.67  ----------------------
% 12.62/4.67  #Subsume      : 257
% 12.62/4.67  #Demod        : 1473
% 12.62/4.67  #Tautology    : 405
% 12.62/4.67  #SimpNegUnit  : 337
% 12.62/4.67  #BackRed      : 1
% 12.62/4.67  
% 12.62/4.67  #Partial instantiations: 0
% 12.62/4.67  #Strategies tried      : 1
% 12.62/4.67  
% 12.62/4.67  Timing (in seconds)
% 12.62/4.67  ----------------------
% 12.62/4.67  Preprocessing        : 0.42
% 12.62/4.67  Parsing              : 0.21
% 12.62/4.67  CNF conversion       : 0.05
% 12.62/4.67  Main loop            : 3.45
% 12.62/4.67  Inferencing          : 1.02
% 12.62/4.67  Reduction            : 0.92
% 12.62/4.67  Demodulation         : 0.65
% 12.62/4.67  BG Simplification    : 0.16
% 12.62/4.67  Subsumption          : 1.17
% 12.62/4.67  Abstraction          : 0.14
% 12.62/4.67  MUC search           : 0.00
% 12.62/4.67  Cooper               : 0.00
% 12.62/4.67  Total                : 3.93
% 12.62/4.67  Index Insertion      : 0.00
% 12.62/4.67  Index Deletion       : 0.00
% 12.62/4.67  Index Matching       : 0.00
% 12.62/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
