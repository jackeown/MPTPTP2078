%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1547+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:02 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 194 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  195 ( 784 expanded)
%              Number of equality atoms :   11 (  68 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k12_lattice3(A,B,C)
                <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

tff(c_44,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r3_orders_2('#skF_2','#skF_3','#skF_4')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_49,plain,(
    ! [A_62,B_63,C_64] :
      ( r3_orders_2(A_62,B_63,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_56,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_51])).

tff(c_60,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_63])).

tff(c_69,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_70,plain,(
    ! [B_65] :
      ( r3_orders_2('#skF_2',B_65,B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_75,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_141,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_orders_2(A_76,B_77,C_78)
      | ~ r3_orders_2(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_141])).

tff(c_160,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_147])).

tff(c_161,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_160])).

tff(c_149,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_164,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_26,c_149])).

tff(c_165,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_164])).

tff(c_16,plain,(
    ! [A_11,B_35,C_47,D_53] :
      ( r1_orders_2(A_11,'#skF_1'(A_11,B_35,C_47,D_53),B_35)
      | k12_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,D_53,C_47)
      | ~ r1_orders_2(A_11,D_53,B_35)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v2_lattice3(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_269,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( ~ r1_orders_2(A_125,'#skF_1'(A_125,B_126,C_127,D_128),D_128)
      | k12_lattice3(A_125,B_126,C_127) = D_128
      | ~ r1_orders_2(A_125,D_128,C_127)
      | ~ r1_orders_2(A_125,D_128,B_126)
      | ~ m1_subset_1(D_128,u1_struct_0(A_125))
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v2_lattice3(A_125)
      | ~ v5_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_280,plain,(
    ! [A_129,B_130,C_131] :
      ( k12_lattice3(A_129,B_130,C_131) = B_130
      | ~ r1_orders_2(A_129,B_130,C_131)
      | ~ r1_orders_2(A_129,B_130,B_130)
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v2_lattice3(A_129)
      | ~ v5_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_16,c_269])).

tff(c_296,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_165,c_280])).

tff(c_312,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_161,c_296])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_312])).

tff(c_316,plain,(
    ~ r3_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_323,plain,(
    ! [A_132,B_133,C_134] :
      ( r3_orders_2(A_132,B_133,B_133)
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_325,plain,(
    ! [B_133] :
      ( r3_orders_2('#skF_2',B_133,B_133)
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_323])).

tff(c_330,plain,(
    ! [B_133] :
      ( r3_orders_2('#skF_2',B_133,B_133)
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_325])).

tff(c_334,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_337,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_337])).

tff(c_343,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_397,plain,(
    ! [A_144,B_145,C_146] :
      ( r3_orders_2(A_144,B_145,C_146)
      | ~ r1_orders_2(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_403,plain,(
    ! [B_145] :
      ( r3_orders_2('#skF_2',B_145,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_397])).

tff(c_411,plain,(
    ! [B_145] :
      ( r3_orders_2('#skF_2',B_145,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_403])).

tff(c_440,plain,(
    ! [B_151] :
      ( r3_orders_2('#skF_2',B_151,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_151,'#skF_4')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_411])).

tff(c_447,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_440])).

tff(c_456,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_447])).

tff(c_315,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_518,plain,(
    ! [A_165,B_166,C_167] :
      ( r1_orders_2(A_165,k12_lattice3(A_165,B_166,C_167),C_167)
      | ~ m1_subset_1(k12_lattice3(A_165,B_166,C_167),u1_struct_0(A_165))
      | ~ m1_subset_1(C_167,u1_struct_0(A_165))
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v2_lattice3(A_165)
      | ~ v5_orders_2(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_522,plain,
    ( r1_orders_2('#skF_2',k12_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_518])).

tff(c_525,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_28,c_315,c_522])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_525])).

%------------------------------------------------------------------------------
