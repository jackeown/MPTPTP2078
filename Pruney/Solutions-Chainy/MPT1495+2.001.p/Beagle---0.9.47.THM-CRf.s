%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:43 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  255 (1768 expanded)
%              Number of leaves         :   47 ( 649 expanded)
%              Depth                    :   30
%              Number of atoms          :  825 (6752 expanded)
%              Number of equality atoms :   24 ( 241 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r3_lattices > r3_lattice3 > r1_orders_2 > r1_lattices > r1_lattice3 > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_orders_2 > v5_lattices > v4_orders_2 > v4_lattices > v3_orders_2 > v2_struct_0 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k5_lattice3,type,(
    k5_lattice3: ( $i * $i ) > $i )).

tff(k4_lattice3,type,(
    k4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_226,negated_conjecture,(
    ~ ! [A,B] :
        ( ( ~ v2_struct_0(B)
          & v10_lattices(B)
          & l3_lattices(B) )
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(B))
           => ( r3_lattice3(B,C,A)
            <=> r1_lattice3(k3_lattice3(B),A,k4_lattice3(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_lattice3)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_99,axiom,(
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

tff(f_62,axiom,(
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

tff(f_81,axiom,(
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

tff(f_165,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k4_lattice3(A,B),u1_struct_0(k3_lattice3(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattice3)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & l1_orders_2(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( ~ v2_struct_0(k3_lattice3(A))
        & v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_211,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_lattices(A,B,C)
              <=> r3_orders_2(k3_lattice3(A),k4_lattice3(A,B),k4_lattice3(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

tff(c_86,plain,
    ( r3_lattice3('#skF_4','#skF_5','#skF_3')
    | r1_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_92,plain,(
    r1_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ r1_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5'))
    | ~ r3_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_101,plain,(
    ~ r3_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_76,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_74,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_102,plain,(
    ! [A_74,B_75] :
      ( k4_lattice3(A_74,B_75) = B_75
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | ~ v10_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_105,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_102])).

tff(c_108,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_105])).

tff(c_109,plain,(
    k4_lattice3('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_108])).

tff(c_110,plain,(
    r1_lattice3(k3_lattice3('#skF_4'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_92])).

tff(c_30,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | r3_lattice3(A_8,B_20,C_26)
      | ~ m1_subset_1(B_20,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_4] :
      ( v6_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_431,plain,(
    ! [A_133,B_134,C_135] :
      ( r3_lattices(A_133,B_134,C_135)
      | ~ r1_lattices(A_133,B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l3_lattices(A_133)
      | ~ v9_lattices(A_133)
      | ~ v8_lattices(A_133)
      | ~ v6_lattices(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_445,plain,(
    ! [B_134] :
      ( r3_lattices('#skF_4',B_134,'#skF_5')
      | ~ r1_lattices('#skF_4',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_431])).

tff(c_454,plain,(
    ! [B_134] :
      ( r3_lattices('#skF_4',B_134,'#skF_5')
      | ~ r1_lattices('#skF_4',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_445])).

tff(c_455,plain,(
    ! [B_134] :
      ( r3_lattices('#skF_4',B_134,'#skF_5')
      | ~ r1_lattices('#skF_4',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_454])).

tff(c_456,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_459,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_456])).

tff(c_462,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_459])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_462])).

tff(c_466,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_8,plain,(
    ! [A_4] :
      ( v8_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_4] :
      ( v9_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_465,plain,(
    ! [B_134] :
      ( ~ v8_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | r3_lattices('#skF_4',B_134,'#skF_5')
      | ~ r1_lattices('#skF_4',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_476,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_479,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_476])).

tff(c_482,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_479])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_482])).

tff(c_485,plain,(
    ! [B_134] :
      ( ~ v8_lattices('#skF_4')
      | r3_lattices('#skF_4',B_134,'#skF_5')
      | ~ r1_lattices('#skF_4',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_487,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_490,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_487])).

tff(c_493,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_490])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_493])).

tff(c_497,plain,(
    v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_486,plain,(
    v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_117,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k4_lattice3(A_81,B_82),u1_struct_0(k3_lattice3(A_81)))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_126,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_117])).

tff(c_130,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_126])).

tff(c_131,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_130])).

tff(c_44,plain,(
    ! [A_48] :
      ( l1_orders_2(k3_lattice3(A_48))
      | ~ l3_lattices(A_48)
      | ~ v10_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_62,plain,(
    ! [A_53] :
      ( v3_orders_2(k3_lattice3(A_53))
      | ~ l3_lattices(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_239,plain,(
    ! [A_111,B_112,C_113] :
      ( r3_orders_2(A_111,B_112,C_113)
      | ~ r1_orders_2(A_111,B_112,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_254,plain,(
    ! [B_112] :
      ( r3_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ m1_subset_1(B_112,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_131,c_239])).

tff(c_420,plain,(
    ~ v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_423,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_420])).

tff(c_426,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_423])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_426])).

tff(c_429,plain,(
    ! [B_112] :
      ( ~ l1_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ m1_subset_1(B_112,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_823,plain,(
    ~ l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_826,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_823])).

tff(c_829,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_826])).

tff(c_831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_829])).

tff(c_833,plain,(
    l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_195,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1('#skF_1'(A_96,B_97,C_98),u1_struct_0(A_96))
      | r3_lattice3(A_96,B_97,C_98)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l3_lattices(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_30,B_32] :
      ( k4_lattice3(A_30,B_32) = B_32
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_315,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_lattice3(A_125,'#skF_1'(A_125,B_126,C_127)) = '#skF_1'(A_125,B_126,C_127)
      | ~ v10_lattices(A_125)
      | r3_lattice3(A_125,B_126,C_127)
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_195,c_32])).

tff(c_327,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | ~ v10_lattices('#skF_4')
      | r3_lattice3('#skF_4','#skF_5',C_127)
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_315])).

tff(c_335,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | r3_lattice3('#skF_4','#skF_5',C_127)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_327])).

tff(c_337,plain,(
    ! [C_128] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_128)) = '#skF_1'('#skF_4','#skF_5',C_128)
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_335])).

tff(c_54,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k4_lattice3(A_49,B_50),u1_struct_0(k3_lattice3(A_49)))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | ~ v10_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_346,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_54])).

tff(c_355,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_346])).

tff(c_356,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_355])).

tff(c_28,plain,(
    ! [A_8,B_20,C_26] :
      ( r2_hidden('#skF_1'(A_8,B_20,C_26),C_26)
      | r3_lattice3(A_8,B_20,C_26)
      | ~ m1_subset_1(B_20,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_231,plain,(
    ! [A_104,C_105,D_106,B_107] :
      ( r1_orders_2(A_104,C_105,D_106)
      | ~ r2_hidden(D_106,B_107)
      | ~ m1_subset_1(D_106,u1_struct_0(A_104))
      | ~ r1_lattice3(A_104,B_107,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4201,plain,(
    ! [A_279,B_281,C_277,C_278,A_280] :
      ( r1_orders_2(A_279,C_278,'#skF_1'(A_280,B_281,C_277))
      | ~ m1_subset_1('#skF_1'(A_280,B_281,C_277),u1_struct_0(A_279))
      | ~ r1_lattice3(A_279,C_277,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | r3_lattice3(A_280,B_281,C_277)
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l3_lattices(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_4203,plain,(
    ! [C_278,C_128] :
      ( r1_orders_2(k3_lattice3('#skF_4'),C_278,'#skF_1'('#skF_4','#skF_5',C_128))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_128,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(resolution,[status(thm)],[c_356,c_4201])).

tff(c_4208,plain,(
    ! [C_278,C_128] :
      ( r1_orders_2(k3_lattice3('#skF_4'),C_278,'#skF_1'('#skF_4','#skF_5',C_128))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_128,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_833,c_4203])).

tff(c_4209,plain,(
    ! [C_278,C_128] :
      ( r1_orders_2(k3_lattice3('#skF_4'),C_278,'#skF_1'('#skF_4','#skF_5',C_128))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_128,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4208])).

tff(c_336,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | r3_lattice3('#skF_4','#skF_5',C_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_335])).

tff(c_832,plain,(
    ! [B_112] :
      ( v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_112,'#skF_5')
      | ~ m1_subset_1(B_112,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_864,plain,(
    v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_66,plain,(
    ! [A_53] :
      ( ~ v2_struct_0(k3_lattice3(A_53))
      | ~ l3_lattices(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_910,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_864,c_66])).

tff(c_913,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_910])).

tff(c_915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_913])).

tff(c_917,plain,(
    ~ v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_430,plain,(
    v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_5270,plain,(
    ! [A_323,B_324,B_325] :
      ( r3_orders_2(k3_lattice3(A_323),B_324,k4_lattice3(A_323,B_325))
      | ~ r1_orders_2(k3_lattice3(A_323),B_324,k4_lattice3(A_323,B_325))
      | ~ m1_subset_1(B_324,u1_struct_0(k3_lattice3(A_323)))
      | ~ l1_orders_2(k3_lattice3(A_323))
      | ~ v3_orders_2(k3_lattice3(A_323))
      | v2_struct_0(k3_lattice3(A_323))
      | ~ m1_subset_1(B_325,u1_struct_0(A_323))
      | ~ l3_lattices(A_323)
      | ~ v10_lattices(A_323)
      | v2_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_54,c_239])).

tff(c_636,plain,(
    ! [A_144,B_145,C_146] :
      ( r3_lattices(A_144,B_145,C_146)
      | ~ r3_orders_2(k3_lattice3(A_144),k4_lattice3(A_144,B_145),k4_lattice3(A_144,C_146))
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l3_lattices(A_144)
      | ~ v10_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_654,plain,(
    ! [C_146] :
      ( r3_lattices('#skF_4','#skF_5',C_146)
      | ~ r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_146))
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_636])).

tff(c_666,plain,(
    ! [C_146] :
      ( r3_lattices('#skF_4','#skF_5',C_146)
      | ~ r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_146))
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_654])).

tff(c_667,plain,(
    ! [C_146] :
      ( r3_lattices('#skF_4','#skF_5',C_146)
      | ~ r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_146))
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_666])).

tff(c_5274,plain,(
    ! [B_325] :
      ( r3_lattices('#skF_4','#skF_5',B_325)
      | ~ r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_325))
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5270,c_667])).

tff(c_5325,plain,(
    ! [B_325] :
      ( r3_lattices('#skF_4','#skF_5',B_325)
      | ~ r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_325))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_430,c_833,c_131,c_5274])).

tff(c_5365,plain,(
    ! [B_326] :
      ( r3_lattices('#skF_4','#skF_5',B_326)
      | ~ r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_326))
      | ~ m1_subset_1(B_326,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_917,c_5325])).

tff(c_5416,plain,(
    ! [C_327] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_327))
      | ~ r1_orders_2(k3_lattice3('#skF_4'),'#skF_5','#skF_1'('#skF_4','#skF_5',C_327))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_327),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_5365])).

tff(c_5420,plain,(
    ! [C_128] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_128))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_128,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(resolution,[status(thm)],[c_4209,c_5416])).

tff(c_5428,plain,(
    ! [C_328] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_328))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_328,'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_328),u1_struct_0('#skF_4'))
      | r3_lattice3('#skF_4','#skF_5',C_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_5420])).

tff(c_5432,plain,(
    ! [C_26] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_26))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_26)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_5428])).

tff(c_5435,plain,(
    ! [C_26] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_26))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_26)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5432])).

tff(c_5437,plain,(
    ! [C_329] :
      ( r3_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_329))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_329,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5435])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_lattices(A_5,B_6,C_7)
      | ~ r3_lattices(A_5,B_6,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | ~ v9_lattices(A_5)
      | ~ v8_lattices(A_5)
      | ~ v6_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5439,plain,(
    ! [C_329] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_329))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_329),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_329,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_329) ) ),
    inference(resolution,[status(thm)],[c_5437,c_22])).

tff(c_5442,plain,(
    ! [C_329] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_329))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_329),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_329,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_497,c_486,c_74,c_72,c_5439])).

tff(c_5444,plain,(
    ! [C_330] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_330))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_330),u1_struct_0('#skF_4'))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_330,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_330) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5442])).

tff(c_5448,plain,(
    ! [C_26] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_26))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_26)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_5444])).

tff(c_5451,plain,(
    ! [C_26] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_26))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_26)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5448])).

tff(c_5453,plain,(
    ! [C_331] :
      ( r1_lattices('#skF_4','#skF_5','#skF_1'('#skF_4','#skF_5',C_331))
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_331,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_331) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5451])).

tff(c_26,plain,(
    ! [A_8,B_20,C_26] :
      ( ~ r1_lattices(A_8,B_20,'#skF_1'(A_8,B_20,C_26))
      | r3_lattice3(A_8,B_20,C_26)
      | ~ m1_subset_1(B_20,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5456,plain,(
    ! [C_331] :
      ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_331,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_331) ) ),
    inference(resolution,[status(thm)],[c_5453,c_26])).

tff(c_5459,plain,(
    ! [C_331] :
      ( v2_struct_0('#skF_4')
      | ~ r1_lattice3(k3_lattice3('#skF_4'),C_331,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5456])).

tff(c_5461,plain,(
    ! [C_332] :
      ( ~ r1_lattice3(k3_lattice3('#skF_4'),C_332,'#skF_5')
      | r3_lattice3('#skF_4','#skF_5',C_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5459])).

tff(c_5464,plain,(
    r3_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_5461])).

tff(c_5468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_5464])).

tff(c_5469,plain,(
    r3_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_5480,plain,(
    ! [A_340,B_341] :
      ( k4_lattice3(A_340,B_341) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0(A_340))
      | ~ l3_lattices(A_340)
      | ~ v10_lattices(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5483,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_5480])).

tff(c_5486,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5483])).

tff(c_5487,plain,(
    k4_lattice3('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5486])).

tff(c_5496,plain,(
    ! [A_350,B_351] :
      ( m1_subset_1(k4_lattice3(A_350,B_351),u1_struct_0(k3_lattice3(A_350)))
      | ~ m1_subset_1(B_351,u1_struct_0(A_350))
      | ~ l3_lattices(A_350)
      | ~ v10_lattices(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5505,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5487,c_5496])).

tff(c_5509,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_5505])).

tff(c_5510,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5509])).

tff(c_5617,plain,(
    ! [A_377,B_378,C_379] :
      ( r3_orders_2(A_377,B_378,C_379)
      | ~ r1_orders_2(A_377,B_378,C_379)
      | ~ m1_subset_1(C_379,u1_struct_0(A_377))
      | ~ m1_subset_1(B_378,u1_struct_0(A_377))
      | ~ l1_orders_2(A_377)
      | ~ v3_orders_2(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5633,plain,(
    ! [B_378] :
      ( r3_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ m1_subset_1(B_378,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5510,c_5617])).

tff(c_5692,plain,(
    ~ v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5633])).

tff(c_5695,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5692])).

tff(c_5698,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5695])).

tff(c_5700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5698])).

tff(c_5701,plain,(
    ! [B_378] :
      ( ~ l1_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ m1_subset_1(B_378,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_5633])).

tff(c_5703,plain,(
    ~ l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5701])).

tff(c_5706,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_5703])).

tff(c_5709,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5706])).

tff(c_5711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5709])).

tff(c_5713,plain,(
    l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5701])).

tff(c_42,plain,(
    ! [A_36,B_43,C_44] :
      ( m1_subset_1('#skF_2'(A_36,B_43,C_44),u1_struct_0(A_36))
      | r1_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5527,plain,(
    ! [A_352,B_353,C_354] :
      ( m1_subset_1('#skF_2'(A_352,B_353,C_354),u1_struct_0(A_352))
      | r1_lattice3(A_352,B_353,C_354)
      | ~ m1_subset_1(C_354,u1_struct_0(A_352))
      | ~ l1_orders_2(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( k5_lattice3(A_33,B_35) = B_35
      | ~ m1_subset_1(B_35,u1_struct_0(k3_lattice3(A_33)))
      | ~ l3_lattices(A_33)
      | ~ v10_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7005,plain,(
    ! [A_451,B_452,C_453] :
      ( k5_lattice3(A_451,'#skF_2'(k3_lattice3(A_451),B_452,C_453)) = '#skF_2'(k3_lattice3(A_451),B_452,C_453)
      | ~ l3_lattices(A_451)
      | ~ v10_lattices(A_451)
      | v2_struct_0(A_451)
      | r1_lattice3(k3_lattice3(A_451),B_452,C_453)
      | ~ m1_subset_1(C_453,u1_struct_0(k3_lattice3(A_451)))
      | ~ l1_orders_2(k3_lattice3(A_451)) ) ),
    inference(resolution,[status(thm)],[c_5527,c_34])).

tff(c_7022,plain,(
    ! [B_452] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_452,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_452,'#skF_5')
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_452,'#skF_5')
      | ~ l1_orders_2(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5510,c_7005])).

tff(c_7042,plain,(
    ! [B_452] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_452,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_452,'#skF_5')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_452,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_76,c_74,c_7022])).

tff(c_7045,plain,(
    ! [B_454] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5')
      | r1_lattice3(k3_lattice3('#skF_4'),B_454,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7042])).

tff(c_56,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k5_lattice3(A_51,B_52),u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,u1_struct_0(k3_lattice3(A_51)))
      | ~ l3_lattices(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_7051,plain,(
    ! [B_454] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_454,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7045,c_56])).

tff(c_7057,plain,(
    ! [B_454] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_454,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_454,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7051])).

tff(c_7060,plain,(
    ! [B_455] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_455,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_455,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | r1_lattice3(k3_lattice3('#skF_4'),B_455,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7057])).

tff(c_7064,plain,(
    ! [B_43] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_7060])).

tff(c_7067,plain,(
    ! [B_43] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5510,c_7064])).

tff(c_40,plain,(
    ! [A_36,B_43,C_44] :
      ( r2_hidden('#skF_2'(A_36,B_43,C_44),B_43)
      | r1_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5639,plain,(
    ! [A_380,B_381,D_382,C_383] :
      ( r1_lattices(A_380,B_381,D_382)
      | ~ r2_hidden(D_382,C_383)
      | ~ m1_subset_1(D_382,u1_struct_0(A_380))
      | ~ r3_lattice3(A_380,B_381,C_383)
      | ~ m1_subset_1(B_381,u1_struct_0(A_380))
      | ~ l3_lattices(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9848,plain,(
    ! [A_548,A_547,B_546,B_545,C_549] :
      ( r1_lattices(A_547,B_545,'#skF_2'(A_548,B_546,C_549))
      | ~ m1_subset_1('#skF_2'(A_548,B_546,C_549),u1_struct_0(A_547))
      | ~ r3_lattice3(A_547,B_545,B_546)
      | ~ m1_subset_1(B_545,u1_struct_0(A_547))
      | ~ l3_lattices(A_547)
      | v2_struct_0(A_547)
      | r1_lattice3(A_548,B_546,C_549)
      | ~ m1_subset_1(C_549,u1_struct_0(A_548))
      | ~ l1_orders_2(A_548) ) ),
    inference(resolution,[status(thm)],[c_40,c_5639])).

tff(c_9852,plain,(
    ! [B_545,B_43] :
      ( r1_lattices('#skF_4',B_545,'#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'))
      | ~ r3_lattice3('#skF_4',B_545,B_43)
      | ~ m1_subset_1(B_545,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7067,c_9848])).

tff(c_9861,plain,(
    ! [B_545,B_43] :
      ( r1_lattices('#skF_4',B_545,'#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'))
      | ~ r3_lattice3('#skF_4',B_545,B_43)
      | ~ m1_subset_1(B_545,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5510,c_74,c_9852])).

tff(c_9862,plain,(
    ! [B_545,B_43] :
      ( r1_lattices('#skF_4',B_545,'#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'))
      | ~ r3_lattice3('#skF_4',B_545,B_43)
      | ~ m1_subset_1(B_545,u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9861])).

tff(c_5714,plain,(
    ! [A_388,B_389,C_390] :
      ( r3_lattices(A_388,B_389,C_390)
      | ~ r1_lattices(A_388,B_389,C_390)
      | ~ m1_subset_1(C_390,u1_struct_0(A_388))
      | ~ m1_subset_1(B_389,u1_struct_0(A_388))
      | ~ l3_lattices(A_388)
      | ~ v9_lattices(A_388)
      | ~ v8_lattices(A_388)
      | ~ v6_lattices(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5726,plain,(
    ! [B_389] :
      ( r3_lattices('#skF_4',B_389,'#skF_5')
      | ~ r1_lattices('#skF_4',B_389,'#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_5714])).

tff(c_5734,plain,(
    ! [B_389] :
      ( r3_lattices('#skF_4',B_389,'#skF_5')
      | ~ r1_lattices('#skF_4',B_389,'#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5726])).

tff(c_5735,plain,(
    ! [B_389] :
      ( r3_lattices('#skF_4',B_389,'#skF_5')
      | ~ r1_lattices('#skF_4',B_389,'#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5734])).

tff(c_5736,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5735])).

tff(c_5739,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_5736])).

tff(c_5742,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_5739])).

tff(c_5744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5742])).

tff(c_5746,plain,(
    v6_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5735])).

tff(c_5745,plain,(
    ! [B_389] :
      ( ~ v8_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | r3_lattices('#skF_4',B_389,'#skF_5')
      | ~ r1_lattices('#skF_4',B_389,'#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_5735])).

tff(c_5747,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5745])).

tff(c_5750,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_5747])).

tff(c_5753,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_5750])).

tff(c_5755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5753])).

tff(c_5756,plain,(
    ! [B_389] :
      ( ~ v8_lattices('#skF_4')
      | r3_lattices('#skF_4',B_389,'#skF_5')
      | ~ r1_lattices('#skF_4',B_389,'#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_5745])).

tff(c_5758,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5756])).

tff(c_5761,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_5758])).

tff(c_5764,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_5761])).

tff(c_5766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5764])).

tff(c_5768,plain,(
    v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5756])).

tff(c_5757,plain,(
    v9_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5745])).

tff(c_7068,plain,(
    ! [B_456] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5510,c_7064])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( r3_lattices(A_5,B_6,C_7)
      | ~ r1_lattices(A_5,B_6,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | ~ v9_lattices(A_5)
      | ~ v8_lattices(A_5)
      | ~ v6_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7077,plain,(
    ! [B_6,B_456] :
      ( r3_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ r1_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7068,c_20])).

tff(c_7096,plain,(
    ! [B_6,B_456] :
      ( r3_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ r1_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5768,c_5757,c_74,c_7077])).

tff(c_7097,plain,(
    ! [B_6,B_456] :
      ( r3_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ r1_lattices('#skF_4',B_6,'#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7096])).

tff(c_7084,plain,(
    ! [B_456] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5')
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7068,c_32])).

tff(c_7106,plain,(
    ! [B_456] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5')
      | v2_struct_0('#skF_4')
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7084])).

tff(c_7108,plain,(
    ! [B_457] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_457,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_457,'#skF_5')
      | r1_lattice3(k3_lattice3('#skF_4'),B_457,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7106])).

tff(c_5712,plain,(
    ! [B_378] :
      ( v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_378,'#skF_5')
      | ~ m1_subset_1(B_378,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_5701])).

tff(c_5828,plain,(
    v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5712])).

tff(c_5831,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5828,c_66])).

tff(c_5834,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5831])).

tff(c_5836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5834])).

tff(c_5838,plain,(
    ~ v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5712])).

tff(c_5702,plain,(
    v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5633])).

tff(c_5873,plain,(
    ! [A_397,B_398,C_399] :
      ( r3_orders_2(k3_lattice3(A_397),k4_lattice3(A_397,B_398),k4_lattice3(A_397,C_399))
      | ~ r3_lattices(A_397,B_398,C_399)
      | ~ m1_subset_1(C_399,u1_struct_0(A_397))
      | ~ m1_subset_1(B_398,u1_struct_0(A_397))
      | ~ l3_lattices(A_397)
      | ~ v10_lattices(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_5884,plain,(
    ! [C_399] :
      ( r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_399))
      | ~ r3_lattices('#skF_4','#skF_5',C_399)
      | ~ m1_subset_1(C_399,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5487,c_5873])).

tff(c_5890,plain,(
    ! [C_399] :
      ( r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_399))
      | ~ r3_lattices('#skF_4','#skF_5',C_399)
      | ~ m1_subset_1(C_399,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_5884])).

tff(c_5895,plain,(
    ! [C_400] :
      ( r3_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_400))
      | ~ r3_lattices('#skF_4','#skF_5',C_400)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5890])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_orders_2(A_1,B_2,C_3)
      | ~ r3_orders_2(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,u1_struct_0(A_1))
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5897,plain,(
    ! [C_400] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_400))
      | ~ m1_subset_1(k4_lattice3('#skF_4',C_400),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4','#skF_5',C_400)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5895,c_4])).

tff(c_5907,plain,(
    ! [C_400] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_400))
      | ~ m1_subset_1(k4_lattice3('#skF_4',C_400),u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4','#skF_5',C_400)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_5713,c_5510,c_5897])).

tff(c_6077,plain,(
    ! [C_413] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',C_413))
      | ~ m1_subset_1(k4_lattice3('#skF_4',C_413),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ r3_lattices('#skF_4','#skF_5',C_413)
      | ~ m1_subset_1(C_413,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5838,c_5907])).

tff(c_6085,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_50))
      | ~ r3_lattices('#skF_4','#skF_5',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_6077])).

tff(c_6094,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_50))
      | ~ r3_lattices('#skF_4','#skF_5',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6085])).

tff(c_6095,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5',k4_lattice3('#skF_4',B_50))
      | ~ r3_lattices('#skF_4','#skF_5',B_50)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6094])).

tff(c_10606,plain,(
    ! [B_589] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_589,'#skF_5'))
      | ~ r3_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_589,'#skF_5'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_589,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_589,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7108,c_6095])).

tff(c_38,plain,(
    ! [A_36,C_44,B_43] :
      ( ~ r1_orders_2(A_36,C_44,'#skF_2'(A_36,B_43,C_44))
      | r1_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10609,plain,(
    ! [B_589] :
      ( ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_589,'#skF_5'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_589,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_589,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10606,c_38])).

tff(c_10613,plain,(
    ! [B_590] :
      ( ~ r3_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_590,'#skF_5'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_590,'#skF_5'),u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_590,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5713,c_5510,c_10609])).

tff(c_10618,plain,(
    ! [B_591] :
      ( ~ r3_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_591,'#skF_5'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_591,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7067,c_10613])).

tff(c_10622,plain,(
    ! [B_456] :
      ( ~ r1_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_456,'#skF_5'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_456,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7097,c_10618])).

tff(c_10636,plain,(
    ! [B_597] :
      ( ~ r1_lattices('#skF_4','#skF_5','#skF_2'(k3_lattice3('#skF_4'),B_597,'#skF_5'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_597,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10622])).

tff(c_10640,plain,(
    ! [B_43] :
      ( ~ r3_lattice3('#skF_4','#skF_5',B_43)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | r1_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9862,c_10636])).

tff(c_10644,plain,(
    ! [B_598] :
      ( ~ r3_lattice3('#skF_4','#skF_5',B_598)
      | r1_lattice3(k3_lattice3('#skF_4'),B_598,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10640])).

tff(c_5470,plain,(
    ~ r1_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_5488,plain,(
    ~ r1_lattice3(k3_lattice3('#skF_4'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_5470])).

tff(c_10647,plain,(
    ~ r3_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_10644,c_5488])).

tff(c_10651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_10647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/3.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.27  
% 8.97/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.28  %$ r3_orders_2 > r3_lattices > r3_lattice3 > r1_orders_2 > r1_lattices > r1_lattice3 > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_orders_2 > v5_lattices > v4_orders_2 > v4_lattices > v3_orders_2 > v2_struct_0 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 8.97/3.28  
% 8.97/3.28  %Foreground sorts:
% 8.97/3.28  
% 8.97/3.28  
% 8.97/3.28  %Background operators:
% 8.97/3.28  
% 8.97/3.28  
% 8.97/3.28  %Foreground operators:
% 8.97/3.28  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.97/3.28  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 8.97/3.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.97/3.28  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 8.97/3.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.97/3.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.97/3.28  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 8.97/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/3.28  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 8.97/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.97/3.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.97/3.28  tff(k5_lattice3, type, k5_lattice3: ($i * $i) > $i).
% 8.97/3.28  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 8.97/3.28  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.97/3.28  tff('#skF_5', type, '#skF_5': $i).
% 8.97/3.28  tff(v4_lattices, type, v4_lattices: $i > $o).
% 8.97/3.28  tff(v6_lattices, type, v6_lattices: $i > $o).
% 8.97/3.28  tff(v9_lattices, type, v9_lattices: $i > $o).
% 8.97/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.97/3.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.97/3.28  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 8.97/3.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.97/3.28  tff(v5_lattices, type, v5_lattices: $i > $o).
% 8.97/3.28  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.97/3.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.97/3.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.97/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/3.28  tff('#skF_4', type, '#skF_4': $i).
% 8.97/3.28  tff(v8_lattices, type, v8_lattices: $i > $o).
% 8.97/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/3.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.97/3.28  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 8.97/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.97/3.28  tff(v7_lattices, type, v7_lattices: $i > $o).
% 8.97/3.28  
% 9.39/3.31  tff(f_226, negated_conjecture, ~(![A, B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (r3_lattice3(B, C, A) <=> r1_lattice3(k3_lattice3(B), A, k4_lattice3(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_lattice3)).
% 9.39/3.31  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 9.39/3.31  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 9.39/3.31  tff(f_62, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 9.39/3.31  tff(f_81, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 9.39/3.31  tff(f_165, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k4_lattice3(A, B), u1_struct_0(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattice3)).
% 9.39/3.31  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & l1_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_lattice3)).
% 9.39/3.31  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((~v2_struct_0(k3_lattice3(A)) & v1_orders_2(k3_lattice3(A))) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_lattice3)).
% 9.39/3.31  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.39/3.31  tff(f_137, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 9.39/3.31  tff(f_211, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) <=> r3_orders_2(k3_lattice3(A), k4_lattice3(A, B), k4_lattice3(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_lattice3)).
% 9.39/3.31  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k3_lattice3(A))) => (k5_lattice3(A, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattice3)).
% 9.39/3.31  tff(f_176, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(k3_lattice3(A)))) => m1_subset_1(k5_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 9.39/3.31  tff(c_86, plain, (r3_lattice3('#skF_4', '#skF_5', '#skF_3') | r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_92, plain, (r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 9.39/3.31  tff(c_80, plain, (~r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5')) | ~r3_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_101, plain, (~r3_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80])).
% 9.39/3.31  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_76, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_74, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_72, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 9.39/3.31  tff(c_102, plain, (![A_74, B_75]: (k4_lattice3(A_74, B_75)=B_75 | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v10_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.31  tff(c_105, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_102])).
% 9.39/3.31  tff(c_108, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_105])).
% 9.39/3.31  tff(c_109, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_108])).
% 9.39/3.31  tff(c_110, plain, (r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_92])).
% 9.39/3.31  tff(c_30, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | r3_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.39/3.31  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.39/3.31  tff(c_431, plain, (![A_133, B_134, C_135]: (r3_lattices(A_133, B_134, C_135) | ~r1_lattices(A_133, B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l3_lattices(A_133) | ~v9_lattices(A_133) | ~v8_lattices(A_133) | ~v6_lattices(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.39/3.31  tff(c_445, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_431])).
% 9.39/3.31  tff(c_454, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_445])).
% 9.39/3.31  tff(c_455, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_454])).
% 9.39/3.31  tff(c_456, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_455])).
% 9.39/3.31  tff(c_459, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_12, c_456])).
% 9.39/3.31  tff(c_462, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_459])).
% 9.39/3.31  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_462])).
% 9.39/3.31  tff(c_466, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_455])).
% 9.39/3.31  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.39/3.31  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.39/3.31  tff(c_465, plain, (![B_134]: (~v8_lattices('#skF_4') | ~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_455])).
% 9.39/3.31  tff(c_476, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_465])).
% 9.39/3.31  tff(c_479, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_6, c_476])).
% 9.39/3.31  tff(c_482, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_479])).
% 9.39/3.31  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_482])).
% 9.39/3.31  tff(c_485, plain, (![B_134]: (~v8_lattices('#skF_4') | r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_465])).
% 9.39/3.31  tff(c_487, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_485])).
% 9.39/3.31  tff(c_490, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_487])).
% 9.39/3.31  tff(c_493, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_490])).
% 9.39/3.31  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_493])).
% 9.39/3.31  tff(c_497, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_485])).
% 9.39/3.31  tff(c_486, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_465])).
% 9.39/3.31  tff(c_117, plain, (![A_81, B_82]: (m1_subset_1(k4_lattice3(A_81, B_82), u1_struct_0(k3_lattice3(A_81))) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.39/3.31  tff(c_126, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_109, c_117])).
% 9.39/3.31  tff(c_130, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_126])).
% 9.39/3.31  tff(c_131, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_130])).
% 9.39/3.31  tff(c_44, plain, (![A_48]: (l1_orders_2(k3_lattice3(A_48)) | ~l3_lattices(A_48) | ~v10_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.39/3.31  tff(c_62, plain, (![A_53]: (v3_orders_2(k3_lattice3(A_53)) | ~l3_lattices(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_194])).
% 9.39/3.31  tff(c_239, plain, (![A_111, B_112, C_113]: (r3_orders_2(A_111, B_112, C_113) | ~r1_orders_2(A_111, B_112, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.39/3.31  tff(c_254, plain, (![B_112]: (r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_131, c_239])).
% 9.39/3.31  tff(c_420, plain, (~v3_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_254])).
% 9.39/3.31  tff(c_423, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_420])).
% 9.39/3.31  tff(c_426, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_423])).
% 9.39/3.31  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_426])).
% 9.39/3.31  tff(c_429, plain, (![B_112]: (~l1_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_254])).
% 9.39/3.31  tff(c_823, plain, (~l1_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_429])).
% 9.39/3.31  tff(c_826, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_823])).
% 9.39/3.31  tff(c_829, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_826])).
% 9.39/3.31  tff(c_831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_829])).
% 9.39/3.31  tff(c_833, plain, (l1_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_429])).
% 9.39/3.31  tff(c_195, plain, (![A_96, B_97, C_98]: (m1_subset_1('#skF_1'(A_96, B_97, C_98), u1_struct_0(A_96)) | r3_lattice3(A_96, B_97, C_98) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l3_lattices(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.39/3.31  tff(c_32, plain, (![A_30, B_32]: (k4_lattice3(A_30, B_32)=B_32 | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.31  tff(c_315, plain, (![A_125, B_126, C_127]: (k4_lattice3(A_125, '#skF_1'(A_125, B_126, C_127))='#skF_1'(A_125, B_126, C_127) | ~v10_lattices(A_125) | r3_lattice3(A_125, B_126, C_127) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_195, c_32])).
% 9.39/3.31  tff(c_327, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | ~v10_lattices('#skF_4') | r3_lattice3('#skF_4', '#skF_5', C_127) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_315])).
% 9.39/3.31  tff(c_335, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | r3_lattice3('#skF_4', '#skF_5', C_127) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_327])).
% 9.39/3.31  tff(c_337, plain, (![C_128]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_128))='#skF_1'('#skF_4', '#skF_5', C_128) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(negUnitSimplification, [status(thm)], [c_78, c_335])).
% 9.39/3.31  tff(c_54, plain, (![A_49, B_50]: (m1_subset_1(k4_lattice3(A_49, B_50), u1_struct_0(k3_lattice3(A_49))) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v10_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.39/3.31  tff(c_346, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(superposition, [status(thm), theory('equality')], [c_337, c_54])).
% 9.39/3.31  tff(c_355, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_346])).
% 9.39/3.31  tff(c_356, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(negUnitSimplification, [status(thm)], [c_78, c_355])).
% 9.39/3.31  tff(c_28, plain, (![A_8, B_20, C_26]: (r2_hidden('#skF_1'(A_8, B_20, C_26), C_26) | r3_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.39/3.31  tff(c_231, plain, (![A_104, C_105, D_106, B_107]: (r1_orders_2(A_104, C_105, D_106) | ~r2_hidden(D_106, B_107) | ~m1_subset_1(D_106, u1_struct_0(A_104)) | ~r1_lattice3(A_104, B_107, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.39/3.31  tff(c_4201, plain, (![A_279, B_281, C_277, C_278, A_280]: (r1_orders_2(A_279, C_278, '#skF_1'(A_280, B_281, C_277)) | ~m1_subset_1('#skF_1'(A_280, B_281, C_277), u1_struct_0(A_279)) | ~r1_lattice3(A_279, C_277, C_278) | ~m1_subset_1(C_278, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | r3_lattice3(A_280, B_281, C_277) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l3_lattices(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_28, c_231])).
% 9.39/3.31  tff(c_4203, plain, (![C_278, C_128]: (r1_orders_2(k3_lattice3('#skF_4'), C_278, '#skF_1'('#skF_4', '#skF_5', C_128)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_128, C_278) | ~m1_subset_1(C_278, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(resolution, [status(thm)], [c_356, c_4201])).
% 9.39/3.31  tff(c_4208, plain, (![C_278, C_128]: (r1_orders_2(k3_lattice3('#skF_4'), C_278, '#skF_1'('#skF_4', '#skF_5', C_128)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_128, C_278) | ~m1_subset_1(C_278, u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_833, c_4203])).
% 9.39/3.31  tff(c_4209, plain, (![C_278, C_128]: (r1_orders_2(k3_lattice3('#skF_4'), C_278, '#skF_1'('#skF_4', '#skF_5', C_128)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_128, C_278) | ~m1_subset_1(C_278, u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(negUnitSimplification, [status(thm)], [c_78, c_4208])).
% 9.39/3.31  tff(c_336, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | r3_lattice3('#skF_4', '#skF_5', C_127))), inference(negUnitSimplification, [status(thm)], [c_78, c_335])).
% 9.39/3.31  tff(c_832, plain, (![B_112]: (v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_429])).
% 9.39/3.31  tff(c_864, plain, (v2_struct_0(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_832])).
% 9.39/3.31  tff(c_66, plain, (![A_53]: (~v2_struct_0(k3_lattice3(A_53)) | ~l3_lattices(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_194])).
% 9.39/3.31  tff(c_910, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_864, c_66])).
% 9.39/3.31  tff(c_913, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_910])).
% 9.39/3.31  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_913])).
% 9.39/3.31  tff(c_917, plain, (~v2_struct_0(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_832])).
% 9.39/3.31  tff(c_430, plain, (v3_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_254])).
% 9.39/3.31  tff(c_5270, plain, (![A_323, B_324, B_325]: (r3_orders_2(k3_lattice3(A_323), B_324, k4_lattice3(A_323, B_325)) | ~r1_orders_2(k3_lattice3(A_323), B_324, k4_lattice3(A_323, B_325)) | ~m1_subset_1(B_324, u1_struct_0(k3_lattice3(A_323))) | ~l1_orders_2(k3_lattice3(A_323)) | ~v3_orders_2(k3_lattice3(A_323)) | v2_struct_0(k3_lattice3(A_323)) | ~m1_subset_1(B_325, u1_struct_0(A_323)) | ~l3_lattices(A_323) | ~v10_lattices(A_323) | v2_struct_0(A_323))), inference(resolution, [status(thm)], [c_54, c_239])).
% 9.39/3.31  tff(c_636, plain, (![A_144, B_145, C_146]: (r3_lattices(A_144, B_145, C_146) | ~r3_orders_2(k3_lattice3(A_144), k4_lattice3(A_144, B_145), k4_lattice3(A_144, C_146)) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l3_lattices(A_144) | ~v10_lattices(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.39/3.31  tff(c_654, plain, (![C_146]: (r3_lattices('#skF_4', '#skF_5', C_146) | ~r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_146)) | ~m1_subset_1(C_146, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_636])).
% 9.39/3.31  tff(c_666, plain, (![C_146]: (r3_lattices('#skF_4', '#skF_5', C_146) | ~r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_146)) | ~m1_subset_1(C_146, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_654])).
% 9.39/3.31  tff(c_667, plain, (![C_146]: (r3_lattices('#skF_4', '#skF_5', C_146) | ~r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_146)) | ~m1_subset_1(C_146, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_666])).
% 9.39/3.31  tff(c_5274, plain, (![B_325]: (r3_lattices('#skF_4', '#skF_5', B_325) | ~r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_325)) | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | ~m1_subset_1(B_325, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5270, c_667])).
% 9.39/3.31  tff(c_5325, plain, (![B_325]: (r3_lattices('#skF_4', '#skF_5', B_325) | ~r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_325)) | v2_struct_0(k3_lattice3('#skF_4')) | ~m1_subset_1(B_325, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_430, c_833, c_131, c_5274])).
% 9.39/3.31  tff(c_5365, plain, (![B_326]: (r3_lattices('#skF_4', '#skF_5', B_326) | ~r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_326)) | ~m1_subset_1(B_326, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_917, c_5325])).
% 9.39/3.31  tff(c_5416, plain, (![C_327]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_327)) | ~r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_327)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_327), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_327))), inference(superposition, [status(thm), theory('equality')], [c_336, c_5365])).
% 9.39/3.31  tff(c_5420, plain, (![C_128]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_128)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_128, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_128))), inference(resolution, [status(thm)], [c_4209, c_5416])).
% 9.39/3.31  tff(c_5428, plain, (![C_328]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_328)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_328, '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_328), u1_struct_0('#skF_4')) | r3_lattice3('#skF_4', '#skF_5', C_328))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_5420])).
% 9.39/3.31  tff(c_5432, plain, (![C_26]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_26)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_26) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_5428])).
% 9.39/3.31  tff(c_5435, plain, (![C_26]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_26)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_26) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5432])).
% 9.39/3.31  tff(c_5437, plain, (![C_329]: (r3_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_329)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_329, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_329))), inference(negUnitSimplification, [status(thm)], [c_78, c_5435])).
% 9.39/3.31  tff(c_22, plain, (![A_5, B_6, C_7]: (r1_lattices(A_5, B_6, C_7) | ~r3_lattices(A_5, B_6, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | ~v9_lattices(A_5) | ~v8_lattices(A_5) | ~v6_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.39/3.31  tff(c_5439, plain, (![C_329]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_329)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_329), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4') | ~r1_lattice3(k3_lattice3('#skF_4'), C_329, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_329))), inference(resolution, [status(thm)], [c_5437, c_22])).
% 9.39/3.31  tff(c_5442, plain, (![C_329]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_329)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_329), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_lattice3(k3_lattice3('#skF_4'), C_329, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_329))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_497, c_486, c_74, c_72, c_5439])).
% 9.39/3.31  tff(c_5444, plain, (![C_330]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_330)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_330), u1_struct_0('#skF_4')) | ~r1_lattice3(k3_lattice3('#skF_4'), C_330, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_330))), inference(negUnitSimplification, [status(thm)], [c_78, c_5442])).
% 9.39/3.31  tff(c_5448, plain, (![C_26]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_26)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_26) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_5444])).
% 9.39/3.31  tff(c_5451, plain, (![C_26]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_26)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_26) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5448])).
% 9.39/3.31  tff(c_5453, plain, (![C_331]: (r1_lattices('#skF_4', '#skF_5', '#skF_1'('#skF_4', '#skF_5', C_331)) | ~r1_lattice3(k3_lattice3('#skF_4'), C_331, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_331))), inference(negUnitSimplification, [status(thm)], [c_78, c_5451])).
% 9.39/3.31  tff(c_26, plain, (![A_8, B_20, C_26]: (~r1_lattices(A_8, B_20, '#skF_1'(A_8, B_20, C_26)) | r3_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.39/3.31  tff(c_5456, plain, (![C_331]: (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | ~r1_lattice3(k3_lattice3('#skF_4'), C_331, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_331))), inference(resolution, [status(thm)], [c_5453, c_26])).
% 9.39/3.31  tff(c_5459, plain, (![C_331]: (v2_struct_0('#skF_4') | ~r1_lattice3(k3_lattice3('#skF_4'), C_331, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_331))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5456])).
% 9.39/3.31  tff(c_5461, plain, (![C_332]: (~r1_lattice3(k3_lattice3('#skF_4'), C_332, '#skF_5') | r3_lattice3('#skF_4', '#skF_5', C_332))), inference(negUnitSimplification, [status(thm)], [c_78, c_5459])).
% 9.39/3.31  tff(c_5464, plain, (r3_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_5461])).
% 9.39/3.31  tff(c_5468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_5464])).
% 9.39/3.31  tff(c_5469, plain, (r3_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 9.39/3.31  tff(c_5480, plain, (![A_340, B_341]: (k4_lattice3(A_340, B_341)=B_341 | ~m1_subset_1(B_341, u1_struct_0(A_340)) | ~l3_lattices(A_340) | ~v10_lattices(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.31  tff(c_5483, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_5480])).
% 9.39/3.31  tff(c_5486, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5483])).
% 9.39/3.31  tff(c_5487, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_5486])).
% 9.39/3.31  tff(c_5496, plain, (![A_350, B_351]: (m1_subset_1(k4_lattice3(A_350, B_351), u1_struct_0(k3_lattice3(A_350))) | ~m1_subset_1(B_351, u1_struct_0(A_350)) | ~l3_lattices(A_350) | ~v10_lattices(A_350) | v2_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.39/3.31  tff(c_5505, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5487, c_5496])).
% 9.39/3.31  tff(c_5509, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_5505])).
% 9.39/3.31  tff(c_5510, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5509])).
% 9.39/3.31  tff(c_5617, plain, (![A_377, B_378, C_379]: (r3_orders_2(A_377, B_378, C_379) | ~r1_orders_2(A_377, B_378, C_379) | ~m1_subset_1(C_379, u1_struct_0(A_377)) | ~m1_subset_1(B_378, u1_struct_0(A_377)) | ~l1_orders_2(A_377) | ~v3_orders_2(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.39/3.31  tff(c_5633, plain, (![B_378]: (r3_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~m1_subset_1(B_378, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_5510, c_5617])).
% 9.39/3.31  tff(c_5692, plain, (~v3_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_5633])).
% 9.39/3.31  tff(c_5695, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5692])).
% 9.39/3.31  tff(c_5698, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5695])).
% 9.39/3.31  tff(c_5700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5698])).
% 9.39/3.31  tff(c_5701, plain, (![B_378]: (~l1_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~m1_subset_1(B_378, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_5633])).
% 9.39/3.31  tff(c_5703, plain, (~l1_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_5701])).
% 9.39/3.31  tff(c_5706, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_5703])).
% 9.39/3.31  tff(c_5709, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5706])).
% 9.39/3.31  tff(c_5711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5709])).
% 9.39/3.31  tff(c_5713, plain, (l1_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_5701])).
% 9.39/3.31  tff(c_42, plain, (![A_36, B_43, C_44]: (m1_subset_1('#skF_2'(A_36, B_43, C_44), u1_struct_0(A_36)) | r1_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.39/3.31  tff(c_5527, plain, (![A_352, B_353, C_354]: (m1_subset_1('#skF_2'(A_352, B_353, C_354), u1_struct_0(A_352)) | r1_lattice3(A_352, B_353, C_354) | ~m1_subset_1(C_354, u1_struct_0(A_352)) | ~l1_orders_2(A_352))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.46/3.31  tff(c_34, plain, (![A_33, B_35]: (k5_lattice3(A_33, B_35)=B_35 | ~m1_subset_1(B_35, u1_struct_0(k3_lattice3(A_33))) | ~l3_lattices(A_33) | ~v10_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.46/3.31  tff(c_7005, plain, (![A_451, B_452, C_453]: (k5_lattice3(A_451, '#skF_2'(k3_lattice3(A_451), B_452, C_453))='#skF_2'(k3_lattice3(A_451), B_452, C_453) | ~l3_lattices(A_451) | ~v10_lattices(A_451) | v2_struct_0(A_451) | r1_lattice3(k3_lattice3(A_451), B_452, C_453) | ~m1_subset_1(C_453, u1_struct_0(k3_lattice3(A_451))) | ~l1_orders_2(k3_lattice3(A_451)))), inference(resolution, [status(thm)], [c_5527, c_34])).
% 9.46/3.31  tff(c_7022, plain, (![B_452]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_452, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_452, '#skF_5') | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_452, '#skF_5') | ~l1_orders_2(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_5510, c_7005])).
% 9.46/3.31  tff(c_7042, plain, (![B_452]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_452, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_452, '#skF_5') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_452, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_76, c_74, c_7022])).
% 9.46/3.31  tff(c_7045, plain, (![B_454]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5') | r1_lattice3(k3_lattice3('#skF_4'), B_454, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_7042])).
% 9.46/3.31  tff(c_56, plain, (![A_51, B_52]: (m1_subset_1(k5_lattice3(A_51, B_52), u1_struct_0(A_51)) | ~m1_subset_1(B_52, u1_struct_0(k3_lattice3(A_51))) | ~l3_lattices(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.46/3.31  tff(c_7051, plain, (![B_454]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_454, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7045, c_56])).
% 9.46/3.31  tff(c_7057, plain, (![B_454]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_454, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_454, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7051])).
% 9.46/3.31  tff(c_7060, plain, (![B_455]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_455, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_455, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | r1_lattice3(k3_lattice3('#skF_4'), B_455, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_7057])).
% 9.46/3.31  tff(c_7064, plain, (![B_43]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_7060])).
% 9.46/3.31  tff(c_7067, plain, (![B_43]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5510, c_7064])).
% 9.46/3.31  tff(c_40, plain, (![A_36, B_43, C_44]: (r2_hidden('#skF_2'(A_36, B_43, C_44), B_43) | r1_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.46/3.31  tff(c_5639, plain, (![A_380, B_381, D_382, C_383]: (r1_lattices(A_380, B_381, D_382) | ~r2_hidden(D_382, C_383) | ~m1_subset_1(D_382, u1_struct_0(A_380)) | ~r3_lattice3(A_380, B_381, C_383) | ~m1_subset_1(B_381, u1_struct_0(A_380)) | ~l3_lattices(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.46/3.31  tff(c_9848, plain, (![A_548, A_547, B_546, B_545, C_549]: (r1_lattices(A_547, B_545, '#skF_2'(A_548, B_546, C_549)) | ~m1_subset_1('#skF_2'(A_548, B_546, C_549), u1_struct_0(A_547)) | ~r3_lattice3(A_547, B_545, B_546) | ~m1_subset_1(B_545, u1_struct_0(A_547)) | ~l3_lattices(A_547) | v2_struct_0(A_547) | r1_lattice3(A_548, B_546, C_549) | ~m1_subset_1(C_549, u1_struct_0(A_548)) | ~l1_orders_2(A_548))), inference(resolution, [status(thm)], [c_40, c_5639])).
% 9.46/3.31  tff(c_9852, plain, (![B_545, B_43]: (r1_lattices('#skF_4', B_545, '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5')) | ~r3_lattice3('#skF_4', B_545, B_43) | ~m1_subset_1(B_545, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(resolution, [status(thm)], [c_7067, c_9848])).
% 9.46/3.31  tff(c_9861, plain, (![B_545, B_43]: (r1_lattices('#skF_4', B_545, '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5')) | ~r3_lattice3('#skF_4', B_545, B_43) | ~m1_subset_1(B_545, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5510, c_74, c_9852])).
% 9.46/3.31  tff(c_9862, plain, (![B_545, B_43]: (r1_lattices('#skF_4', B_545, '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5')) | ~r3_lattice3('#skF_4', B_545, B_43) | ~m1_subset_1(B_545, u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_9861])).
% 9.46/3.31  tff(c_5714, plain, (![A_388, B_389, C_390]: (r3_lattices(A_388, B_389, C_390) | ~r1_lattices(A_388, B_389, C_390) | ~m1_subset_1(C_390, u1_struct_0(A_388)) | ~m1_subset_1(B_389, u1_struct_0(A_388)) | ~l3_lattices(A_388) | ~v9_lattices(A_388) | ~v8_lattices(A_388) | ~v6_lattices(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.31  tff(c_5726, plain, (![B_389]: (r3_lattices('#skF_4', B_389, '#skF_5') | ~r1_lattices('#skF_4', B_389, '#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_5714])).
% 9.46/3.31  tff(c_5734, plain, (![B_389]: (r3_lattices('#skF_4', B_389, '#skF_5') | ~r1_lattices('#skF_4', B_389, '#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5726])).
% 9.46/3.31  tff(c_5735, plain, (![B_389]: (r3_lattices('#skF_4', B_389, '#skF_5') | ~r1_lattices('#skF_4', B_389, '#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5734])).
% 9.46/3.31  tff(c_5736, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_5735])).
% 9.46/3.31  tff(c_5739, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_12, c_5736])).
% 9.46/3.31  tff(c_5742, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_5739])).
% 9.46/3.31  tff(c_5744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5742])).
% 9.46/3.31  tff(c_5746, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_5735])).
% 9.46/3.31  tff(c_5745, plain, (![B_389]: (~v8_lattices('#skF_4') | ~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_389, '#skF_5') | ~r1_lattices('#skF_4', B_389, '#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_5735])).
% 9.46/3.31  tff(c_5747, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_5745])).
% 9.46/3.31  tff(c_5750, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_6, c_5747])).
% 9.46/3.31  tff(c_5753, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_5750])).
% 9.46/3.31  tff(c_5755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5753])).
% 9.46/3.31  tff(c_5756, plain, (![B_389]: (~v8_lattices('#skF_4') | r3_lattices('#skF_4', B_389, '#skF_5') | ~r1_lattices('#skF_4', B_389, '#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_5745])).
% 9.46/3.31  tff(c_5758, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_5756])).
% 9.46/3.31  tff(c_5761, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_5758])).
% 9.46/3.31  tff(c_5764, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_5761])).
% 9.46/3.31  tff(c_5766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5764])).
% 9.46/3.31  tff(c_5768, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_5756])).
% 9.46/3.31  tff(c_5757, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_5745])).
% 9.46/3.31  tff(c_7068, plain, (![B_456]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5510, c_7064])).
% 9.46/3.31  tff(c_20, plain, (![A_5, B_6, C_7]: (r3_lattices(A_5, B_6, C_7) | ~r1_lattices(A_5, B_6, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | ~v9_lattices(A_5) | ~v8_lattices(A_5) | ~v6_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.31  tff(c_7077, plain, (![B_6, B_456]: (r3_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~r1_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~m1_subset_1(B_6, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(resolution, [status(thm)], [c_7068, c_20])).
% 9.46/3.31  tff(c_7096, plain, (![B_6, B_456]: (r3_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~r1_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~m1_subset_1(B_6, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5768, c_5757, c_74, c_7077])).
% 9.46/3.31  tff(c_7097, plain, (![B_6, B_456]: (r3_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~r1_lattices('#skF_4', B_6, '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~m1_subset_1(B_6, u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_7096])).
% 9.46/3.31  tff(c_7084, plain, (![B_456]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5') | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(resolution, [status(thm)], [c_7068, c_32])).
% 9.46/3.31  tff(c_7106, plain, (![B_456]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5') | v2_struct_0('#skF_4') | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7084])).
% 9.46/3.31  tff(c_7108, plain, (![B_457]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_457, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_457, '#skF_5') | r1_lattice3(k3_lattice3('#skF_4'), B_457, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_7106])).
% 9.46/3.31  tff(c_5712, plain, (![B_378]: (v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_378, '#skF_5') | ~m1_subset_1(B_378, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_5701])).
% 9.46/3.31  tff(c_5828, plain, (v2_struct_0(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_5712])).
% 9.46/3.31  tff(c_5831, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5828, c_66])).
% 9.46/3.31  tff(c_5834, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5831])).
% 9.46/3.31  tff(c_5836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5834])).
% 9.46/3.31  tff(c_5838, plain, (~v2_struct_0(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_5712])).
% 9.46/3.31  tff(c_5702, plain, (v3_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_5633])).
% 9.46/3.31  tff(c_5873, plain, (![A_397, B_398, C_399]: (r3_orders_2(k3_lattice3(A_397), k4_lattice3(A_397, B_398), k4_lattice3(A_397, C_399)) | ~r3_lattices(A_397, B_398, C_399) | ~m1_subset_1(C_399, u1_struct_0(A_397)) | ~m1_subset_1(B_398, u1_struct_0(A_397)) | ~l3_lattices(A_397) | ~v10_lattices(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.46/3.31  tff(c_5884, plain, (![C_399]: (r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_399)) | ~r3_lattices('#skF_4', '#skF_5', C_399) | ~m1_subset_1(C_399, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5487, c_5873])).
% 9.46/3.31  tff(c_5890, plain, (![C_399]: (r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_399)) | ~r3_lattices('#skF_4', '#skF_5', C_399) | ~m1_subset_1(C_399, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_5884])).
% 9.46/3.31  tff(c_5895, plain, (![C_400]: (r3_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_400)) | ~r3_lattices('#skF_4', '#skF_5', C_400) | ~m1_subset_1(C_400, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5890])).
% 9.46/3.31  tff(c_4, plain, (![A_1, B_2, C_3]: (r1_orders_2(A_1, B_2, C_3) | ~r3_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.46/3.31  tff(c_5897, plain, (![C_400]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_400)) | ~m1_subset_1(k4_lattice3('#skF_4', C_400), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', '#skF_5', C_400) | ~m1_subset_1(C_400, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_5895, c_4])).
% 9.46/3.31  tff(c_5907, plain, (![C_400]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_400)) | ~m1_subset_1(k4_lattice3('#skF_4', C_400), u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', '#skF_5', C_400) | ~m1_subset_1(C_400, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5702, c_5713, c_5510, c_5897])).
% 9.46/3.31  tff(c_6077, plain, (![C_413]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', C_413)) | ~m1_subset_1(k4_lattice3('#skF_4', C_413), u1_struct_0(k3_lattice3('#skF_4'))) | ~r3_lattices('#skF_4', '#skF_5', C_413) | ~m1_subset_1(C_413, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_5838, c_5907])).
% 9.46/3.31  tff(c_6085, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_50)) | ~r3_lattices('#skF_4', '#skF_5', B_50) | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_6077])).
% 9.46/3.31  tff(c_6094, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_50)) | ~r3_lattices('#skF_4', '#skF_5', B_50) | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6085])).
% 9.46/3.31  tff(c_6095, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', k4_lattice3('#skF_4', B_50)) | ~r3_lattices('#skF_4', '#skF_5', B_50) | ~m1_subset_1(B_50, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_6094])).
% 9.46/3.31  tff(c_10606, plain, (![B_589]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_589, '#skF_5')) | ~r3_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_589, '#skF_5')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_589, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_589, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7108, c_6095])).
% 9.46/3.31  tff(c_38, plain, (![A_36, C_44, B_43]: (~r1_orders_2(A_36, C_44, '#skF_2'(A_36, B_43, C_44)) | r1_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.46/3.31  tff(c_10609, plain, (![B_589]: (~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_589, '#skF_5')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_589, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_589, '#skF_5'))), inference(resolution, [status(thm)], [c_10606, c_38])).
% 9.46/3.31  tff(c_10613, plain, (![B_590]: (~r3_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_590, '#skF_5')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_590, '#skF_5'), u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_590, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5713, c_5510, c_10609])).
% 9.46/3.31  tff(c_10618, plain, (![B_591]: (~r3_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_591, '#skF_5')) | r1_lattice3(k3_lattice3('#skF_4'), B_591, '#skF_5'))), inference(resolution, [status(thm)], [c_7067, c_10613])).
% 9.46/3.31  tff(c_10622, plain, (![B_456]: (~r1_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_456, '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_456, '#skF_5'))), inference(resolution, [status(thm)], [c_7097, c_10618])).
% 9.46/3.31  tff(c_10636, plain, (![B_597]: (~r1_lattices('#skF_4', '#skF_5', '#skF_2'(k3_lattice3('#skF_4'), B_597, '#skF_5')) | r1_lattice3(k3_lattice3('#skF_4'), B_597, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10622])).
% 9.46/3.31  tff(c_10640, plain, (![B_43]: (~r3_lattice3('#skF_4', '#skF_5', B_43) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | r1_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(resolution, [status(thm)], [c_9862, c_10636])).
% 9.46/3.31  tff(c_10644, plain, (![B_598]: (~r3_lattice3('#skF_4', '#skF_5', B_598) | r1_lattice3(k3_lattice3('#skF_4'), B_598, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10640])).
% 9.46/3.31  tff(c_5470, plain, (~r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_86])).
% 9.46/3.31  tff(c_5488, plain, (~r1_lattice3(k3_lattice3('#skF_4'), '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_5470])).
% 9.46/3.31  tff(c_10647, plain, (~r3_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_10644, c_5488])).
% 9.46/3.31  tff(c_10651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5469, c_10647])).
% 9.46/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.46/3.31  
% 9.46/3.31  Inference rules
% 9.46/3.31  ----------------------
% 9.46/3.31  #Ref     : 0
% 9.46/3.31  #Sup     : 2280
% 9.46/3.31  #Fact    : 0
% 9.46/3.31  #Define  : 0
% 9.46/3.31  #Split   : 26
% 9.46/3.31  #Chain   : 0
% 9.46/3.31  #Close   : 0
% 9.46/3.31  
% 9.46/3.31  Ordering : KBO
% 9.46/3.31  
% 9.46/3.31  Simplification rules
% 9.46/3.31  ----------------------
% 9.46/3.31  #Subsume      : 570
% 9.46/3.31  #Demod        : 2048
% 9.46/3.31  #Tautology    : 264
% 9.46/3.31  #SimpNegUnit  : 927
% 9.46/3.31  #BackRed      : 2
% 9.46/3.31  
% 9.46/3.31  #Partial instantiations: 0
% 9.46/3.31  #Strategies tried      : 1
% 9.46/3.31  
% 9.46/3.31  Timing (in seconds)
% 9.46/3.31  ----------------------
% 9.46/3.31  Preprocessing        : 0.40
% 9.46/3.31  Parsing              : 0.23
% 9.46/3.31  CNF conversion       : 0.03
% 9.46/3.31  Main loop            : 2.05
% 9.46/3.31  Inferencing          : 0.68
% 9.46/3.31  Reduction            : 0.65
% 9.46/3.31  Demodulation         : 0.42
% 9.46/3.31  BG Simplification    : 0.08
% 9.46/3.31  Subsumption          : 0.52
% 9.46/3.31  Abstraction          : 0.12
% 9.46/3.31  MUC search           : 0.00
% 9.46/3.31  Cooper               : 0.00
% 9.46/3.32  Total                : 2.53
% 9.46/3.32  Index Insertion      : 0.00
% 9.46/3.32  Index Deletion       : 0.00
% 9.46/3.32  Index Matching       : 0.00
% 9.46/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
