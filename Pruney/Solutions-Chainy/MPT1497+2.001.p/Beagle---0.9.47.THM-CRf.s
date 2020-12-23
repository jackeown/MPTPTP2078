%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:43 EST 2020

% Result     : Theorem 8.38s
% Output     : CNFRefutation 8.50s
% Verified   : 
% Statistics : Number of formulae       :  248 (1649 expanded)
%              Number of leaves         :   47 ( 606 expanded)
%              Depth                    :   32
%              Number of atoms          :  785 (6242 expanded)
%              Number of equality atoms :   24 ( 226 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_orders_2 > r3_lattices > r2_lattice3 > r1_orders_2 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_orders_2 > v5_lattices > v4_orders_2 > v4_lattices > v3_orders_2 > v2_struct_0 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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
           => ( r4_lattice3(B,C,A)
            <=> r2_lattice3(k3_lattice3(B),A,k4_lattice3(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_lattice3)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k4_lattice3(A,B),u1_struct_0(k3_lattice3(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_lattice3)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattice3)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattice3)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_86,plain,
    ( r4_lattice3('#skF_4','#skF_5','#skF_3')
    | r2_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_92,plain,(
    r2_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ r2_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5'))
    | ~ r4_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_101,plain,(
    ~ r4_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80])).

tff(c_74,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_76,plain,(
    v10_lattices('#skF_4') ),
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
    r2_lattice3(k3_lattice3('#skF_4'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_92])).

tff(c_30,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | r4_lattice3(A_8,B_20,C_26)
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
      | r4_lattice3(A_96,B_97,C_98)
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
      | r4_lattice3(A_125,B_126,C_127)
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_195,c_32])).

tff(c_327,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | ~ v10_lattices('#skF_4')
      | r4_lattice3('#skF_4','#skF_5',C_127)
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_315])).

tff(c_335,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | r4_lattice3('#skF_4','#skF_5',C_127)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_327])).

tff(c_337,plain,(
    ! [C_128] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_128)) = '#skF_1'('#skF_4','#skF_5',C_128)
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
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
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_54])).

tff(c_355,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_346])).

tff(c_356,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_355])).

tff(c_28,plain,(
    ! [A_8,B_20,C_26] :
      ( r2_hidden('#skF_1'(A_8,B_20,C_26),C_26)
      | r4_lattice3(A_8,B_20,C_26)
      | ~ m1_subset_1(B_20,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_231,plain,(
    ! [A_104,D_105,C_106,B_107] :
      ( r1_orders_2(A_104,D_105,C_106)
      | ~ r2_hidden(D_105,B_107)
      | ~ m1_subset_1(D_105,u1_struct_0(A_104))
      | ~ r2_lattice3(A_104,B_107,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4201,plain,(
    ! [A_279,C_277,A_278,B_280,C_281] :
      ( r1_orders_2(A_278,'#skF_1'(A_279,B_280,C_277),C_281)
      | ~ m1_subset_1('#skF_1'(A_279,B_280,C_277),u1_struct_0(A_278))
      | ~ r2_lattice3(A_278,C_277,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(A_278))
      | ~ l1_orders_2(A_278)
      | r4_lattice3(A_279,B_280,C_277)
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l3_lattices(A_279)
      | v2_struct_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_4203,plain,(
    ! [C_128,C_281] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_1'('#skF_4','#skF_5',C_128),C_281)
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_128,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(resolution,[status(thm)],[c_356,c_4201])).

tff(c_4208,plain,(
    ! [C_128,C_281] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_1'('#skF_4','#skF_5',C_128),C_281)
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_128,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_128),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_833,c_4203])).

tff(c_4225,plain,(
    ! [C_287,C_288] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_1'('#skF_4','#skF_5',C_287),C_288)
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_287,C_288)
      | ~ m1_subset_1(C_288,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_287),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_287) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4208])).

tff(c_336,plain,(
    ! [C_127] :
      ( k4_lattice3('#skF_4','#skF_1'('#skF_4','#skF_5',C_127)) = '#skF_1'('#skF_4','#skF_5',C_127)
      | r4_lattice3('#skF_4','#skF_5',C_127) ) ),
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

tff(c_918,plain,(
    ! [B_156] :
      ( r3_orders_2(k3_lattice3('#skF_4'),B_156,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_156,'#skF_5')
      | ~ m1_subset_1(B_156,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_940,plain,(
    ! [B_50] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_918])).

tff(c_955,plain,(
    ! [B_50] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_940])).

tff(c_957,plain,(
    ! [B_157] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_157),'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_157),'#skF_5')
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_955])).

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

tff(c_657,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_4',B_145,'#skF_5')
      | ~ r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_145),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_636])).

tff(c_669,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_4',B_145,'#skF_5')
      | ~ r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_145),'#skF_5')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_657])).

tff(c_670,plain,(
    ! [B_145] :
      ( r3_lattices('#skF_4',B_145,'#skF_5')
      | ~ r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_145),'#skF_5')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_669])).

tff(c_1041,plain,(
    ! [B_160] :
      ( r3_lattices('#skF_4',B_160,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_160),'#skF_5')
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_957,c_670])).

tff(c_1047,plain,(
    ! [C_127] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_127),'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),'#skF_1'('#skF_4','#skF_5',C_127),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_127),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1041])).

tff(c_4229,plain,(
    ! [C_287] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_287),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_287,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_287),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_287) ) ),
    inference(resolution,[status(thm)],[c_4225,c_1047])).

tff(c_4300,plain,(
    ! [C_290] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_290),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_290,'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_290),u1_struct_0('#skF_4'))
      | r4_lattice3('#skF_4','#skF_5',C_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_4229])).

tff(c_4304,plain,(
    ! [C_26] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_26),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_26)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_4300])).

tff(c_4307,plain,(
    ! [C_26] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_26),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_26)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4304])).

tff(c_4309,plain,(
    ! [C_291] :
      ( r3_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_291),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_291,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_291) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4307])).

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

tff(c_4311,plain,(
    ! [C_291] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_291),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_291),u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_291,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_291) ) ),
    inference(resolution,[status(thm)],[c_4309,c_22])).

tff(c_4314,plain,(
    ! [C_291] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_291),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_291),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_291,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_497,c_486,c_74,c_72,c_4311])).

tff(c_4316,plain,(
    ! [C_292] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_292),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5',C_292),u1_struct_0('#skF_4'))
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_292,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_292) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4314])).

tff(c_4320,plain,(
    ! [C_26] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_26),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_26)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_4316])).

tff(c_4323,plain,(
    ! [C_26] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_26),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_26,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_26)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4320])).

tff(c_4325,plain,(
    ! [C_293] :
      ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5',C_293),'#skF_5')
      | ~ r2_lattice3(k3_lattice3('#skF_4'),C_293,'#skF_5')
      | r4_lattice3('#skF_4','#skF_5',C_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4323])).

tff(c_4328,plain,
    ( r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_3'),'#skF_5')
    | r4_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_4325])).

tff(c_4331,plain,(
    r1_lattices('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_4328])).

tff(c_26,plain,(
    ! [A_8,B_20,C_26] :
      ( ~ r1_lattices(A_8,'#skF_1'(A_8,B_20,C_26),B_20)
      | r4_lattice3(A_8,B_20,C_26)
      | ~ m1_subset_1(B_20,u1_struct_0(A_8))
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4334,plain,
    ( r4_lattice3('#skF_4','#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4331,c_26])).

tff(c_4337,plain,
    ( r4_lattice3('#skF_4','#skF_5','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4334])).

tff(c_4339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_101,c_4337])).

tff(c_4340,plain,(
    r4_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4351,plain,(
    ! [A_301,B_302] :
      ( k4_lattice3(A_301,B_302) = B_302
      | ~ m1_subset_1(B_302,u1_struct_0(A_301))
      | ~ l3_lattices(A_301)
      | ~ v10_lattices(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4354,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_4351])).

tff(c_4357,plain,
    ( k4_lattice3('#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4354])).

tff(c_4358,plain,(
    k4_lattice3('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4357])).

tff(c_4387,plain,(
    ! [A_316,B_317] :
      ( m1_subset_1(k4_lattice3(A_316,B_317),u1_struct_0(k3_lattice3(A_316)))
      | ~ m1_subset_1(B_317,u1_struct_0(A_316))
      | ~ l3_lattices(A_316)
      | ~ v10_lattices(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4396,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4358,c_4387])).

tff(c_4400,plain,
    ( m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_4396])).

tff(c_4401,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4400])).

tff(c_4488,plain,(
    ! [A_338,B_339,C_340] :
      ( r3_orders_2(A_338,B_339,C_340)
      | ~ r1_orders_2(A_338,B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ m1_subset_1(B_339,u1_struct_0(A_338))
      | ~ l1_orders_2(A_338)
      | ~ v3_orders_2(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4502,plain,(
    ! [B_339] :
      ( r3_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ m1_subset_1(B_339,u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4401,c_4488])).

tff(c_4534,plain,(
    ~ v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4502])).

tff(c_4537,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4534])).

tff(c_4540,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4537])).

tff(c_4542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4540])).

tff(c_4543,plain,(
    ! [B_339] :
      ( ~ l1_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ m1_subset_1(B_339,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_4502])).

tff(c_4545,plain,(
    ~ l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4543])).

tff(c_4548,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_4545])).

tff(c_4551,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4548])).

tff(c_4553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4551])).

tff(c_4555,plain,(
    l1_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4543])).

tff(c_42,plain,(
    ! [A_36,B_43,C_44] :
      ( m1_subset_1('#skF_2'(A_36,B_43,C_44),u1_struct_0(A_36))
      | r2_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4366,plain,(
    ! [A_308,B_309,C_310] :
      ( m1_subset_1('#skF_2'(A_308,B_309,C_310),u1_struct_0(A_308))
      | r2_lattice3(A_308,B_309,C_310)
      | ~ m1_subset_1(C_310,u1_struct_0(A_308))
      | ~ l1_orders_2(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( k5_lattice3(A_33,B_35) = B_35
      | ~ m1_subset_1(B_35,u1_struct_0(k3_lattice3(A_33)))
      | ~ l3_lattices(A_33)
      | ~ v10_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6359,plain,(
    ! [A_431,B_432,C_433] :
      ( k5_lattice3(A_431,'#skF_2'(k3_lattice3(A_431),B_432,C_433)) = '#skF_2'(k3_lattice3(A_431),B_432,C_433)
      | ~ l3_lattices(A_431)
      | ~ v10_lattices(A_431)
      | v2_struct_0(A_431)
      | r2_lattice3(k3_lattice3(A_431),B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0(k3_lattice3(A_431)))
      | ~ l1_orders_2(k3_lattice3(A_431)) ) ),
    inference(resolution,[status(thm)],[c_4366,c_34])).

tff(c_6372,plain,(
    ! [B_432] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_432,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_432,'#skF_5')
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_432,'#skF_5')
      | ~ l1_orders_2(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4401,c_6359])).

tff(c_6400,plain,(
    ! [B_432] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_432,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_432,'#skF_5')
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_432,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_76,c_74,c_6372])).

tff(c_6410,plain,(
    ! [B_434] :
      ( k5_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5')
      | r2_lattice3(k3_lattice3('#skF_4'),B_434,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6400])).

tff(c_56,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k5_lattice3(A_51,B_52),u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,u1_struct_0(k3_lattice3(A_51)))
      | ~ l3_lattices(A_51)
      | ~ v10_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6416,plain,(
    ! [B_434] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_434,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6410,c_56])).

tff(c_6422,plain,(
    ! [B_434] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_434,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_434,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6416])).

tff(c_6425,plain,(
    ! [B_435] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_435,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_435,'#skF_5'),u1_struct_0(k3_lattice3('#skF_4')))
      | r2_lattice3(k3_lattice3('#skF_4'),B_435,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6422])).

tff(c_6429,plain,(
    ! [B_43] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_6425])).

tff(c_6432,plain,(
    ! [B_43] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_4401,c_6429])).

tff(c_40,plain,(
    ! [A_36,B_43,C_44] :
      ( r2_hidden('#skF_2'(A_36,B_43,C_44),B_43)
      | r2_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4556,plain,(
    ! [A_343,D_344,B_345,C_346] :
      ( r1_lattices(A_343,D_344,B_345)
      | ~ r2_hidden(D_344,C_346)
      | ~ m1_subset_1(D_344,u1_struct_0(A_343))
      | ~ r4_lattice3(A_343,B_345,C_346)
      | ~ m1_subset_1(B_345,u1_struct_0(A_343))
      | ~ l3_lattices(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9170,plain,(
    ! [A_532,B_533,C_536,A_534,B_535] :
      ( r1_lattices(A_532,'#skF_2'(A_534,B_533,C_536),B_535)
      | ~ m1_subset_1('#skF_2'(A_534,B_533,C_536),u1_struct_0(A_532))
      | ~ r4_lattice3(A_532,B_535,B_533)
      | ~ m1_subset_1(B_535,u1_struct_0(A_532))
      | ~ l3_lattices(A_532)
      | v2_struct_0(A_532)
      | r2_lattice3(A_534,B_533,C_536)
      | ~ m1_subset_1(C_536,u1_struct_0(A_534))
      | ~ l1_orders_2(A_534) ) ),
    inference(resolution,[status(thm)],[c_40,c_4556])).

tff(c_9174,plain,(
    ! [B_43,B_535] :
      ( r1_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),B_535)
      | ~ r4_lattice3('#skF_4',B_535,B_43)
      | ~ m1_subset_1(B_535,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6432,c_9170])).

tff(c_9183,plain,(
    ! [B_43,B_535] :
      ( r1_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),B_535)
      | ~ r4_lattice3('#skF_4',B_535,B_43)
      | ~ m1_subset_1(B_535,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_4401,c_74,c_9174])).

tff(c_9184,plain,(
    ! [B_43,B_535] :
      ( r1_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_43,'#skF_5'),B_535)
      | ~ r4_lattice3('#skF_4',B_535,B_43)
      | ~ m1_subset_1(B_535,u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9183])).

tff(c_6441,plain,(
    ! [B_437] :
      ( m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_437,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_4401,c_6429])).

tff(c_4856,plain,(
    ! [A_366,B_367,C_368] :
      ( r3_lattices(A_366,B_367,C_368)
      | ~ r1_lattices(A_366,B_367,C_368)
      | ~ m1_subset_1(C_368,u1_struct_0(A_366))
      | ~ m1_subset_1(B_367,u1_struct_0(A_366))
      | ~ l3_lattices(A_366)
      | ~ v9_lattices(A_366)
      | ~ v8_lattices(A_366)
      | ~ v6_lattices(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4872,plain,(
    ! [B_367] :
      ( r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_4856])).

tff(c_4889,plain,(
    ! [B_367] :
      ( r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4872])).

tff(c_4890,plain,(
    ! [B_367] :
      ( r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4'))
      | ~ v9_lattices('#skF_4')
      | ~ v8_lattices('#skF_4')
      | ~ v6_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4889])).

tff(c_4891,plain,(
    ~ v6_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4890])).

tff(c_4894,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_4891])).

tff(c_4897,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4894])).

tff(c_4899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4897])).

tff(c_4900,plain,(
    ! [B_367] :
      ( ~ v8_lattices('#skF_4')
      | ~ v9_lattices('#skF_4')
      | r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_4890])).

tff(c_4956,plain,(
    ~ v9_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4900])).

tff(c_4959,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_4956])).

tff(c_4962,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4959])).

tff(c_4964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4962])).

tff(c_4965,plain,(
    ! [B_367] :
      ( ~ v8_lattices('#skF_4')
      | r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_4900])).

tff(c_4967,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4965])).

tff(c_4970,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_4967])).

tff(c_4973,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4970])).

tff(c_4975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4973])).

tff(c_4976,plain,(
    ! [B_367] :
      ( r3_lattices('#skF_4',B_367,'#skF_5')
      | ~ r1_lattices('#skF_4',B_367,'#skF_5')
      | ~ m1_subset_1(B_367,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_4965])).

tff(c_6462,plain,(
    ! [B_437] :
      ( r3_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5'),'#skF_5')
      | ~ r1_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5'),'#skF_5')
      | r2_lattice3(k3_lattice3('#skF_4'),B_437,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6441,c_4976])).

tff(c_6457,plain,(
    ! [B_437] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5')
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_437,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6441,c_32])).

tff(c_6479,plain,(
    ! [B_437] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_437,'#skF_5')
      | v2_struct_0('#skF_4')
      | r2_lattice3(k3_lattice3('#skF_4'),B_437,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6457])).

tff(c_6481,plain,(
    ! [B_438] :
      ( k4_lattice3('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_438,'#skF_5')) = '#skF_2'(k3_lattice3('#skF_4'),B_438,'#skF_5')
      | r2_lattice3(k3_lattice3('#skF_4'),B_438,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6479])).

tff(c_4554,plain,(
    ! [B_339] :
      ( v2_struct_0(k3_lattice3('#skF_4'))
      | r3_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ r1_orders_2(k3_lattice3('#skF_4'),B_339,'#skF_5')
      | ~ m1_subset_1(B_339,u1_struct_0(k3_lattice3('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_4543])).

tff(c_4563,plain,(
    v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4554])).

tff(c_4566,plain,
    ( ~ l3_lattices('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4563,c_66])).

tff(c_4569,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4566])).

tff(c_4571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4569])).

tff(c_4573,plain,(
    ~ v2_struct_0(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4554])).

tff(c_4544,plain,(
    v3_orders_2(k3_lattice3('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4502])).

tff(c_5114,plain,(
    ! [A_377,B_378,C_379] :
      ( r3_orders_2(k3_lattice3(A_377),k4_lattice3(A_377,B_378),k4_lattice3(A_377,C_379))
      | ~ r3_lattices(A_377,B_378,C_379)
      | ~ m1_subset_1(C_379,u1_struct_0(A_377))
      | ~ m1_subset_1(B_378,u1_struct_0(A_377))
      | ~ l3_lattices(A_377)
      | ~ v10_lattices(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_5143,plain,(
    ! [B_378] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_378),'#skF_5')
      | ~ r3_lattices('#skF_4',B_378,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4358,c_5114])).

tff(c_5162,plain,(
    ! [B_378] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_378),'#skF_5')
      | ~ r3_lattices('#skF_4',B_378,'#skF_5')
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_5143])).

tff(c_5194,plain,(
    ! [B_381] :
      ( r3_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_381),'#skF_5')
      | ~ r3_lattices('#skF_4',B_381,'#skF_5')
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5162])).

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

tff(c_5199,plain,(
    ! [B_381] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_381),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ m1_subset_1(k4_lattice3('#skF_4',B_381),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ v3_orders_2(k3_lattice3('#skF_4'))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4',B_381,'#skF_5')
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5194,c_4])).

tff(c_5216,plain,(
    ! [B_381] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_381),'#skF_5')
      | ~ m1_subset_1(k4_lattice3('#skF_4',B_381),u1_struct_0(k3_lattice3('#skF_4')))
      | v2_struct_0(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4',B_381,'#skF_5')
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_4555,c_4401,c_5199])).

tff(c_5300,plain,(
    ! [B_386] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_386),'#skF_5')
      | ~ m1_subset_1(k4_lattice3('#skF_4',B_386),u1_struct_0(k3_lattice3('#skF_4')))
      | ~ r3_lattices('#skF_4',B_386,'#skF_5')
      | ~ m1_subset_1(B_386,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4573,c_5216])).

tff(c_5314,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ r3_lattices('#skF_4',B_50,'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | ~ v10_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_5300])).

tff(c_5323,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ r3_lattices('#skF_4',B_50,'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5314])).

tff(c_5324,plain,(
    ! [B_50] :
      ( r1_orders_2(k3_lattice3('#skF_4'),k4_lattice3('#skF_4',B_50),'#skF_5')
      | ~ r3_lattices('#skF_4',B_50,'#skF_5')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5323])).

tff(c_9517,plain,(
    ! [B_566] :
      ( r1_orders_2(k3_lattice3('#skF_4'),'#skF_2'(k3_lattice3('#skF_4'),B_566,'#skF_5'),'#skF_5')
      | ~ r3_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_566,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_566,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_566,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6481,c_5324])).

tff(c_38,plain,(
    ! [A_36,B_43,C_44] :
      ( ~ r1_orders_2(A_36,'#skF_2'(A_36,B_43,C_44),C_44)
      | r2_lattice3(A_36,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_9520,plain,(
    ! [B_566] :
      ( ~ m1_subset_1('#skF_5',u1_struct_0(k3_lattice3('#skF_4')))
      | ~ l1_orders_2(k3_lattice3('#skF_4'))
      | ~ r3_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_566,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_566,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_566,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9517,c_38])).

tff(c_9524,plain,(
    ! [B_567] :
      ( ~ r3_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_567,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k3_lattice3('#skF_4'),B_567,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_567,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_4401,c_9520])).

tff(c_9624,plain,(
    ! [B_571] :
      ( ~ r3_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_571,'#skF_5'),'#skF_5')
      | r2_lattice3(k3_lattice3('#skF_4'),B_571,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6432,c_9524])).

tff(c_9629,plain,(
    ! [B_572] :
      ( ~ r1_lattices('#skF_4','#skF_2'(k3_lattice3('#skF_4'),B_572,'#skF_5'),'#skF_5')
      | r2_lattice3(k3_lattice3('#skF_4'),B_572,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6462,c_9624])).

tff(c_9633,plain,(
    ! [B_43] :
      ( ~ r4_lattice3('#skF_4','#skF_5',B_43)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | r2_lattice3(k3_lattice3('#skF_4'),B_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9184,c_9629])).

tff(c_9637,plain,(
    ! [B_573] :
      ( ~ r4_lattice3('#skF_4','#skF_5',B_573)
      | r2_lattice3(k3_lattice3('#skF_4'),B_573,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9633])).

tff(c_4341,plain,(
    ~ r2_lattice3(k3_lattice3('#skF_4'),'#skF_3',k4_lattice3('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4359,plain,(
    ~ r2_lattice3(k3_lattice3('#skF_4'),'#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4358,c_4341])).

tff(c_9643,plain,(
    ~ r4_lattice3('#skF_4','#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_9637,c_4359])).

tff(c_9648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_9643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:02:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.38/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.50/3.01  
% 8.50/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.50/3.02  %$ r4_lattice3 > r3_orders_2 > r3_lattices > r2_lattice3 > r1_orders_2 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_orders_2 > v5_lattices > v4_orders_2 > v4_lattices > v3_orders_2 > v2_struct_0 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 8.50/3.02  
% 8.50/3.02  %Foreground sorts:
% 8.50/3.02  
% 8.50/3.02  
% 8.50/3.02  %Background operators:
% 8.50/3.02  
% 8.50/3.02  
% 8.50/3.02  %Foreground operators:
% 8.50/3.02  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.50/3.02  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 8.50/3.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.50/3.02  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 8.50/3.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.50/3.02  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.50/3.02  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 8.50/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.50/3.02  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 8.50/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.50/3.02  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.50/3.02  tff(k5_lattice3, type, k5_lattice3: ($i * $i) > $i).
% 8.50/3.02  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 8.50/3.02  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.50/3.02  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 8.50/3.02  tff('#skF_5', type, '#skF_5': $i).
% 8.50/3.02  tff(v4_lattices, type, v4_lattices: $i > $o).
% 8.50/3.02  tff(v6_lattices, type, v6_lattices: $i > $o).
% 8.50/3.02  tff(v9_lattices, type, v9_lattices: $i > $o).
% 8.50/3.02  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 8.50/3.02  tff('#skF_3', type, '#skF_3': $i).
% 8.50/3.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.50/3.02  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.50/3.02  tff(v5_lattices, type, v5_lattices: $i > $o).
% 8.50/3.02  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.50/3.02  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.50/3.02  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.50/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.50/3.02  tff('#skF_4', type, '#skF_4': $i).
% 8.50/3.02  tff(v8_lattices, type, v8_lattices: $i > $o).
% 8.50/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.50/3.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.50/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.50/3.02  tff(v7_lattices, type, v7_lattices: $i > $o).
% 8.50/3.02  
% 8.50/3.05  tff(f_226, negated_conjecture, ~(![A, B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (r4_lattice3(B, C, A) <=> r2_lattice3(k3_lattice3(B), A, k4_lattice3(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_lattice3)).
% 8.50/3.05  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattice3)).
% 8.50/3.05  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 8.50/3.05  tff(f_62, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 8.50/3.05  tff(f_81, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 8.50/3.05  tff(f_165, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k4_lattice3(A, B), u1_struct_0(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattice3)).
% 8.50/3.05  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & l1_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattice3)).
% 8.50/3.05  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((~v2_struct_0(k3_lattice3(A)) & v1_orders_2(k3_lattice3(A))) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_lattice3)).
% 8.50/3.05  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 8.50/3.05  tff(f_137, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 8.50/3.05  tff(f_211, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) <=> r3_orders_2(k3_lattice3(A), k4_lattice3(A, B), k4_lattice3(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_lattice3)).
% 8.50/3.05  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k3_lattice3(A))) => (k5_lattice3(A, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_lattice3)).
% 8.50/3.05  tff(f_176, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(k3_lattice3(A)))) => m1_subset_1(k5_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 8.50/3.05  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_86, plain, (r4_lattice3('#skF_4', '#skF_5', '#skF_3') | r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_92, plain, (r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 8.50/3.05  tff(c_80, plain, (~r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5')) | ~r4_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_101, plain, (~r4_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80])).
% 8.50/3.05  tff(c_74, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_72, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_76, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 8.50/3.05  tff(c_102, plain, (![A_74, B_75]: (k4_lattice3(A_74, B_75)=B_75 | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | ~v10_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.50/3.05  tff(c_105, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_102])).
% 8.50/3.05  tff(c_108, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_105])).
% 8.50/3.05  tff(c_109, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_108])).
% 8.50/3.05  tff(c_110, plain, (r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_92])).
% 8.50/3.05  tff(c_30, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | r4_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.05  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.50/3.05  tff(c_431, plain, (![A_133, B_134, C_135]: (r3_lattices(A_133, B_134, C_135) | ~r1_lattices(A_133, B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l3_lattices(A_133) | ~v9_lattices(A_133) | ~v8_lattices(A_133) | ~v6_lattices(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.50/3.05  tff(c_445, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_431])).
% 8.50/3.05  tff(c_454, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_445])).
% 8.50/3.05  tff(c_455, plain, (![B_134]: (r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_454])).
% 8.50/3.05  tff(c_456, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_455])).
% 8.50/3.05  tff(c_459, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_12, c_456])).
% 8.50/3.05  tff(c_462, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_459])).
% 8.50/3.05  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_462])).
% 8.50/3.05  tff(c_466, plain, (v6_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_455])).
% 8.50/3.05  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.50/3.05  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.50/3.05  tff(c_465, plain, (![B_134]: (~v8_lattices('#skF_4') | ~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_455])).
% 8.50/3.05  tff(c_476, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_465])).
% 8.50/3.05  tff(c_479, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_6, c_476])).
% 8.50/3.05  tff(c_482, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_479])).
% 8.50/3.05  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_482])).
% 8.50/3.05  tff(c_485, plain, (![B_134]: (~v8_lattices('#skF_4') | r3_lattices('#skF_4', B_134, '#skF_5') | ~r1_lattices('#skF_4', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_465])).
% 8.50/3.05  tff(c_487, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_485])).
% 8.50/3.05  tff(c_490, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_487])).
% 8.50/3.05  tff(c_493, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_490])).
% 8.50/3.05  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_493])).
% 8.50/3.05  tff(c_497, plain, (v8_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_485])).
% 8.50/3.05  tff(c_486, plain, (v9_lattices('#skF_4')), inference(splitRight, [status(thm)], [c_465])).
% 8.50/3.05  tff(c_117, plain, (![A_81, B_82]: (m1_subset_1(k4_lattice3(A_81, B_82), u1_struct_0(k3_lattice3(A_81))) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.50/3.05  tff(c_126, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_109, c_117])).
% 8.50/3.05  tff(c_130, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_126])).
% 8.50/3.05  tff(c_131, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_130])).
% 8.50/3.05  tff(c_44, plain, (![A_48]: (l1_orders_2(k3_lattice3(A_48)) | ~l3_lattices(A_48) | ~v10_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.50/3.05  tff(c_62, plain, (![A_53]: (v3_orders_2(k3_lattice3(A_53)) | ~l3_lattices(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.50/3.05  tff(c_239, plain, (![A_111, B_112, C_113]: (r3_orders_2(A_111, B_112, C_113) | ~r1_orders_2(A_111, B_112, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.50/3.05  tff(c_254, plain, (![B_112]: (r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_131, c_239])).
% 8.50/3.05  tff(c_420, plain, (~v3_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_254])).
% 8.50/3.05  tff(c_423, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_420])).
% 8.50/3.05  tff(c_426, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_423])).
% 8.50/3.05  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_426])).
% 8.50/3.05  tff(c_429, plain, (![B_112]: (~l1_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_254])).
% 8.50/3.05  tff(c_823, plain, (~l1_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_429])).
% 8.50/3.05  tff(c_826, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_823])).
% 8.50/3.05  tff(c_829, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_826])).
% 8.50/3.05  tff(c_831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_829])).
% 8.50/3.05  tff(c_833, plain, (l1_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_429])).
% 8.50/3.05  tff(c_195, plain, (![A_96, B_97, C_98]: (m1_subset_1('#skF_1'(A_96, B_97, C_98), u1_struct_0(A_96)) | r4_lattice3(A_96, B_97, C_98) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l3_lattices(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.05  tff(c_32, plain, (![A_30, B_32]: (k4_lattice3(A_30, B_32)=B_32 | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.50/3.05  tff(c_315, plain, (![A_125, B_126, C_127]: (k4_lattice3(A_125, '#skF_1'(A_125, B_126, C_127))='#skF_1'(A_125, B_126, C_127) | ~v10_lattices(A_125) | r4_lattice3(A_125, B_126, C_127) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_195, c_32])).
% 8.50/3.05  tff(c_327, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | ~v10_lattices('#skF_4') | r4_lattice3('#skF_4', '#skF_5', C_127) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_315])).
% 8.50/3.05  tff(c_335, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | r4_lattice3('#skF_4', '#skF_5', C_127) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_327])).
% 8.50/3.05  tff(c_337, plain, (![C_128]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_128))='#skF_1'('#skF_4', '#skF_5', C_128) | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(negUnitSimplification, [status(thm)], [c_78, c_335])).
% 8.50/3.05  tff(c_54, plain, (![A_49, B_50]: (m1_subset_1(k4_lattice3(A_49, B_50), u1_struct_0(k3_lattice3(A_49))) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v10_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.50/3.05  tff(c_346, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(superposition, [status(thm), theory('equality')], [c_337, c_54])).
% 8.50/3.05  tff(c_355, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_346])).
% 8.50/3.05  tff(c_356, plain, (![C_128]: (m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(negUnitSimplification, [status(thm)], [c_78, c_355])).
% 8.50/3.05  tff(c_28, plain, (![A_8, B_20, C_26]: (r2_hidden('#skF_1'(A_8, B_20, C_26), C_26) | r4_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.05  tff(c_231, plain, (![A_104, D_105, C_106, B_107]: (r1_orders_2(A_104, D_105, C_106) | ~r2_hidden(D_105, B_107) | ~m1_subset_1(D_105, u1_struct_0(A_104)) | ~r2_lattice3(A_104, B_107, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.50/3.05  tff(c_4201, plain, (![A_279, C_277, A_278, B_280, C_281]: (r1_orders_2(A_278, '#skF_1'(A_279, B_280, C_277), C_281) | ~m1_subset_1('#skF_1'(A_279, B_280, C_277), u1_struct_0(A_278)) | ~r2_lattice3(A_278, C_277, C_281) | ~m1_subset_1(C_281, u1_struct_0(A_278)) | ~l1_orders_2(A_278) | r4_lattice3(A_279, B_280, C_277) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l3_lattices(A_279) | v2_struct_0(A_279))), inference(resolution, [status(thm)], [c_28, c_231])).
% 8.50/3.05  tff(c_4203, plain, (![C_128, C_281]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_1'('#skF_4', '#skF_5', C_128), C_281) | ~r2_lattice3(k3_lattice3('#skF_4'), C_128, C_281) | ~m1_subset_1(C_281, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(resolution, [status(thm)], [c_356, c_4201])).
% 8.50/3.05  tff(c_4208, plain, (![C_128, C_281]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_1'('#skF_4', '#skF_5', C_128), C_281) | ~r2_lattice3(k3_lattice3('#skF_4'), C_128, C_281) | ~m1_subset_1(C_281, u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_128), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_128))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_833, c_4203])).
% 8.50/3.05  tff(c_4225, plain, (![C_287, C_288]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_1'('#skF_4', '#skF_5', C_287), C_288) | ~r2_lattice3(k3_lattice3('#skF_4'), C_287, C_288) | ~m1_subset_1(C_288, u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_287), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_287))), inference(negUnitSimplification, [status(thm)], [c_78, c_4208])).
% 8.50/3.05  tff(c_336, plain, (![C_127]: (k4_lattice3('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127))='#skF_1'('#skF_4', '#skF_5', C_127) | r4_lattice3('#skF_4', '#skF_5', C_127))), inference(negUnitSimplification, [status(thm)], [c_78, c_335])).
% 8.50/3.05  tff(c_832, plain, (![B_112]: (v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_112, '#skF_5') | ~m1_subset_1(B_112, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_429])).
% 8.50/3.05  tff(c_864, plain, (v2_struct_0(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_832])).
% 8.50/3.05  tff(c_66, plain, (![A_53]: (~v2_struct_0(k3_lattice3(A_53)) | ~l3_lattices(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.50/3.05  tff(c_910, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_864, c_66])).
% 8.50/3.05  tff(c_913, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_910])).
% 8.50/3.05  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_913])).
% 8.50/3.05  tff(c_918, plain, (![B_156]: (r3_orders_2(k3_lattice3('#skF_4'), B_156, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_156, '#skF_5') | ~m1_subset_1(B_156, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_832])).
% 8.50/3.05  tff(c_940, plain, (![B_50]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_918])).
% 8.50/3.05  tff(c_955, plain, (![B_50]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_940])).
% 8.50/3.05  tff(c_957, plain, (![B_157]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_157), '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_157), '#skF_5') | ~m1_subset_1(B_157, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_955])).
% 8.50/3.05  tff(c_636, plain, (![A_144, B_145, C_146]: (r3_lattices(A_144, B_145, C_146) | ~r3_orders_2(k3_lattice3(A_144), k4_lattice3(A_144, B_145), k4_lattice3(A_144, C_146)) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l3_lattices(A_144) | ~v10_lattices(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.50/3.05  tff(c_657, plain, (![B_145]: (r3_lattices('#skF_4', B_145, '#skF_5') | ~r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_145), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(B_145, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_636])).
% 8.50/3.05  tff(c_669, plain, (![B_145]: (r3_lattices('#skF_4', B_145, '#skF_5') | ~r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_145), '#skF_5') | ~m1_subset_1(B_145, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_657])).
% 8.50/3.05  tff(c_670, plain, (![B_145]: (r3_lattices('#skF_4', B_145, '#skF_5') | ~r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_145), '#skF_5') | ~m1_subset_1(B_145, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_669])).
% 8.50/3.05  tff(c_1041, plain, (![B_160]: (r3_lattices('#skF_4', B_160, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_160), '#skF_5') | ~m1_subset_1(B_160, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_957, c_670])).
% 8.50/3.05  tff(c_1047, plain, (![C_127]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_127), '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), '#skF_1'('#skF_4', '#skF_5', C_127), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_127), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_127))), inference(superposition, [status(thm), theory('equality')], [c_336, c_1041])).
% 8.50/3.05  tff(c_4229, plain, (![C_287]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_287), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_287, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_287), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_287))), inference(resolution, [status(thm)], [c_4225, c_1047])).
% 8.50/3.05  tff(c_4300, plain, (![C_290]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_290), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_290, '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_290), u1_struct_0('#skF_4')) | r4_lattice3('#skF_4', '#skF_5', C_290))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_4229])).
% 8.50/3.05  tff(c_4304, plain, (![C_26]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_26), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_26) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_4300])).
% 8.50/3.05  tff(c_4307, plain, (![C_26]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_26), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_26) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4304])).
% 8.50/3.05  tff(c_4309, plain, (![C_291]: (r3_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_291), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_291, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_291))), inference(negUnitSimplification, [status(thm)], [c_78, c_4307])).
% 8.50/3.05  tff(c_22, plain, (![A_5, B_6, C_7]: (r1_lattices(A_5, B_6, C_7) | ~r3_lattices(A_5, B_6, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l3_lattices(A_5) | ~v9_lattices(A_5) | ~v8_lattices(A_5) | ~v6_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.50/3.05  tff(c_4311, plain, (![C_291]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_291), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_291), u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4') | ~r2_lattice3(k3_lattice3('#skF_4'), C_291, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_291))), inference(resolution, [status(thm)], [c_4309, c_22])).
% 8.50/3.05  tff(c_4314, plain, (![C_291]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_291), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_291), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r2_lattice3(k3_lattice3('#skF_4'), C_291, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_291))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_497, c_486, c_74, c_72, c_4311])).
% 8.50/3.05  tff(c_4316, plain, (![C_292]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_292), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', C_292), u1_struct_0('#skF_4')) | ~r2_lattice3(k3_lattice3('#skF_4'), C_292, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_292))), inference(negUnitSimplification, [status(thm)], [c_78, c_4314])).
% 8.50/3.05  tff(c_4320, plain, (![C_26]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_26), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_26) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_4316])).
% 8.50/3.05  tff(c_4323, plain, (![C_26]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_26), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_26, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_26) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4320])).
% 8.50/3.05  tff(c_4325, plain, (![C_293]: (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_293), '#skF_5') | ~r2_lattice3(k3_lattice3('#skF_4'), C_293, '#skF_5') | r4_lattice3('#skF_4', '#skF_5', C_293))), inference(negUnitSimplification, [status(thm)], [c_78, c_4323])).
% 8.50/3.05  tff(c_4328, plain, (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_3'), '#skF_5') | r4_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_4325])).
% 8.50/3.05  tff(c_4331, plain, (r1_lattices('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_3'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_101, c_4328])).
% 8.50/3.05  tff(c_26, plain, (![A_8, B_20, C_26]: (~r1_lattices(A_8, '#skF_1'(A_8, B_20, C_26), B_20) | r4_lattice3(A_8, B_20, C_26) | ~m1_subset_1(B_20, u1_struct_0(A_8)) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.05  tff(c_4334, plain, (r4_lattice3('#skF_4', '#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4331, c_26])).
% 8.50/3.05  tff(c_4337, plain, (r4_lattice3('#skF_4', '#skF_5', '#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4334])).
% 8.50/3.05  tff(c_4339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_101, c_4337])).
% 8.50/3.05  tff(c_4340, plain, (r4_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 8.50/3.05  tff(c_4351, plain, (![A_301, B_302]: (k4_lattice3(A_301, B_302)=B_302 | ~m1_subset_1(B_302, u1_struct_0(A_301)) | ~l3_lattices(A_301) | ~v10_lattices(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.50/3.05  tff(c_4354, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_4351])).
% 8.50/3.05  tff(c_4357, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4354])).
% 8.50/3.05  tff(c_4358, plain, (k4_lattice3('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_4357])).
% 8.50/3.05  tff(c_4387, plain, (![A_316, B_317]: (m1_subset_1(k4_lattice3(A_316, B_317), u1_struct_0(k3_lattice3(A_316))) | ~m1_subset_1(B_317, u1_struct_0(A_316)) | ~l3_lattices(A_316) | ~v10_lattices(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.50/3.05  tff(c_4396, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4358, c_4387])).
% 8.50/3.05  tff(c_4400, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_4396])).
% 8.50/3.05  tff(c_4401, plain, (m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_4400])).
% 8.50/3.05  tff(c_4488, plain, (![A_338, B_339, C_340]: (r3_orders_2(A_338, B_339, C_340) | ~r1_orders_2(A_338, B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0(A_338)) | ~m1_subset_1(B_339, u1_struct_0(A_338)) | ~l1_orders_2(A_338) | ~v3_orders_2(A_338) | v2_struct_0(A_338))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.50/3.05  tff(c_4502, plain, (![B_339]: (r3_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~m1_subset_1(B_339, u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_4401, c_4488])).
% 8.50/3.05  tff(c_4534, plain, (~v3_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_4502])).
% 8.50/3.05  tff(c_4537, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_4534])).
% 8.50/3.05  tff(c_4540, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4537])).
% 8.50/3.05  tff(c_4542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4540])).
% 8.50/3.05  tff(c_4543, plain, (![B_339]: (~l1_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~m1_subset_1(B_339, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_4502])).
% 8.50/3.05  tff(c_4545, plain, (~l1_orders_2(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_4543])).
% 8.50/3.05  tff(c_4548, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_4545])).
% 8.50/3.05  tff(c_4551, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4548])).
% 8.50/3.05  tff(c_4553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4551])).
% 8.50/3.05  tff(c_4555, plain, (l1_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_4543])).
% 8.50/3.05  tff(c_42, plain, (![A_36, B_43, C_44]: (m1_subset_1('#skF_2'(A_36, B_43, C_44), u1_struct_0(A_36)) | r2_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.50/3.05  tff(c_4366, plain, (![A_308, B_309, C_310]: (m1_subset_1('#skF_2'(A_308, B_309, C_310), u1_struct_0(A_308)) | r2_lattice3(A_308, B_309, C_310) | ~m1_subset_1(C_310, u1_struct_0(A_308)) | ~l1_orders_2(A_308))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.50/3.05  tff(c_34, plain, (![A_33, B_35]: (k5_lattice3(A_33, B_35)=B_35 | ~m1_subset_1(B_35, u1_struct_0(k3_lattice3(A_33))) | ~l3_lattices(A_33) | ~v10_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.50/3.05  tff(c_6359, plain, (![A_431, B_432, C_433]: (k5_lattice3(A_431, '#skF_2'(k3_lattice3(A_431), B_432, C_433))='#skF_2'(k3_lattice3(A_431), B_432, C_433) | ~l3_lattices(A_431) | ~v10_lattices(A_431) | v2_struct_0(A_431) | r2_lattice3(k3_lattice3(A_431), B_432, C_433) | ~m1_subset_1(C_433, u1_struct_0(k3_lattice3(A_431))) | ~l1_orders_2(k3_lattice3(A_431)))), inference(resolution, [status(thm)], [c_4366, c_34])).
% 8.50/3.05  tff(c_6372, plain, (![B_432]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_432, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_432, '#skF_5') | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_432, '#skF_5') | ~l1_orders_2(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_4401, c_6359])).
% 8.50/3.05  tff(c_6400, plain, (![B_432]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_432, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_432, '#skF_5') | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_432, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_76, c_74, c_6372])).
% 8.50/3.05  tff(c_6410, plain, (![B_434]: (k5_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5') | r2_lattice3(k3_lattice3('#skF_4'), B_434, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6400])).
% 8.50/3.05  tff(c_56, plain, (![A_51, B_52]: (m1_subset_1(k5_lattice3(A_51, B_52), u1_struct_0(A_51)) | ~m1_subset_1(B_52, u1_struct_0(k3_lattice3(A_51))) | ~l3_lattices(A_51) | ~v10_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.50/3.05  tff(c_6416, plain, (![B_434]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_434, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6410, c_56])).
% 8.50/3.05  tff(c_6422, plain, (![B_434]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_434, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_434, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6416])).
% 8.50/3.05  tff(c_6425, plain, (![B_435]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_435, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_435, '#skF_5'), u1_struct_0(k3_lattice3('#skF_4'))) | r2_lattice3(k3_lattice3('#skF_4'), B_435, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6422])).
% 8.50/3.05  tff(c_6429, plain, (![B_43]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_6425])).
% 8.50/3.05  tff(c_6432, plain, (![B_43]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_4401, c_6429])).
% 8.50/3.05  tff(c_40, plain, (![A_36, B_43, C_44]: (r2_hidden('#skF_2'(A_36, B_43, C_44), B_43) | r2_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.50/3.05  tff(c_4556, plain, (![A_343, D_344, B_345, C_346]: (r1_lattices(A_343, D_344, B_345) | ~r2_hidden(D_344, C_346) | ~m1_subset_1(D_344, u1_struct_0(A_343)) | ~r4_lattice3(A_343, B_345, C_346) | ~m1_subset_1(B_345, u1_struct_0(A_343)) | ~l3_lattices(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.05  tff(c_9170, plain, (![A_532, B_533, C_536, A_534, B_535]: (r1_lattices(A_532, '#skF_2'(A_534, B_533, C_536), B_535) | ~m1_subset_1('#skF_2'(A_534, B_533, C_536), u1_struct_0(A_532)) | ~r4_lattice3(A_532, B_535, B_533) | ~m1_subset_1(B_535, u1_struct_0(A_532)) | ~l3_lattices(A_532) | v2_struct_0(A_532) | r2_lattice3(A_534, B_533, C_536) | ~m1_subset_1(C_536, u1_struct_0(A_534)) | ~l1_orders_2(A_534))), inference(resolution, [status(thm)], [c_40, c_4556])).
% 8.50/3.05  tff(c_9174, plain, (![B_43, B_535]: (r1_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), B_535) | ~r4_lattice3('#skF_4', B_535, B_43) | ~m1_subset_1(B_535, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(resolution, [status(thm)], [c_6432, c_9170])).
% 8.50/3.05  tff(c_9183, plain, (![B_43, B_535]: (r1_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), B_535) | ~r4_lattice3('#skF_4', B_535, B_43) | ~m1_subset_1(B_535, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_4401, c_74, c_9174])).
% 8.50/3.05  tff(c_9184, plain, (![B_43, B_535]: (r1_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_43, '#skF_5'), B_535) | ~r4_lattice3('#skF_4', B_535, B_43) | ~m1_subset_1(B_535, u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_9183])).
% 8.50/3.05  tff(c_6441, plain, (![B_437]: (m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_437, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_4401, c_6429])).
% 8.50/3.05  tff(c_4856, plain, (![A_366, B_367, C_368]: (r3_lattices(A_366, B_367, C_368) | ~r1_lattices(A_366, B_367, C_368) | ~m1_subset_1(C_368, u1_struct_0(A_366)) | ~m1_subset_1(B_367, u1_struct_0(A_366)) | ~l3_lattices(A_366) | ~v9_lattices(A_366) | ~v8_lattices(A_366) | ~v6_lattices(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.50/3.05  tff(c_4872, plain, (![B_367]: (r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_4856])).
% 8.50/3.05  tff(c_4889, plain, (![B_367]: (r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4872])).
% 8.50/3.05  tff(c_4890, plain, (![B_367]: (r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')) | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4889])).
% 8.50/3.05  tff(c_4891, plain, (~v6_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_4890])).
% 8.50/3.05  tff(c_4894, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_12, c_4891])).
% 8.50/3.05  tff(c_4897, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4894])).
% 8.50/3.05  tff(c_4899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4897])).
% 8.50/3.05  tff(c_4900, plain, (![B_367]: (~v8_lattices('#skF_4') | ~v9_lattices('#skF_4') | r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_4890])).
% 8.50/3.05  tff(c_4956, plain, (~v9_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_4900])).
% 8.50/3.05  tff(c_4959, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_6, c_4956])).
% 8.50/3.05  tff(c_4962, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4959])).
% 8.50/3.05  tff(c_4964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4962])).
% 8.50/3.05  tff(c_4965, plain, (![B_367]: (~v8_lattices('#skF_4') | r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_4900])).
% 8.50/3.05  tff(c_4967, plain, (~v8_lattices('#skF_4')), inference(splitLeft, [status(thm)], [c_4965])).
% 8.50/3.05  tff(c_4970, plain, (~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | ~l3_lattices('#skF_4')), inference(resolution, [status(thm)], [c_8, c_4967])).
% 8.50/3.05  tff(c_4973, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4970])).
% 8.50/3.05  tff(c_4975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4973])).
% 8.50/3.05  tff(c_4976, plain, (![B_367]: (r3_lattices('#skF_4', B_367, '#skF_5') | ~r1_lattices('#skF_4', B_367, '#skF_5') | ~m1_subset_1(B_367, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_4965])).
% 8.50/3.05  tff(c_6462, plain, (![B_437]: (r3_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5'), '#skF_5') | ~r1_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5'), '#skF_5') | r2_lattice3(k3_lattice3('#skF_4'), B_437, '#skF_5'))), inference(resolution, [status(thm)], [c_6441, c_4976])).
% 8.50/3.05  tff(c_6457, plain, (![B_437]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5') | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_437, '#skF_5'))), inference(resolution, [status(thm)], [c_6441, c_32])).
% 8.50/3.05  tff(c_6479, plain, (![B_437]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_437, '#skF_5') | v2_struct_0('#skF_4') | r2_lattice3(k3_lattice3('#skF_4'), B_437, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6457])).
% 8.50/3.05  tff(c_6481, plain, (![B_438]: (k4_lattice3('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_438, '#skF_5'))='#skF_2'(k3_lattice3('#skF_4'), B_438, '#skF_5') | r2_lattice3(k3_lattice3('#skF_4'), B_438, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6479])).
% 8.50/3.05  tff(c_4554, plain, (![B_339]: (v2_struct_0(k3_lattice3('#skF_4')) | r3_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~r1_orders_2(k3_lattice3('#skF_4'), B_339, '#skF_5') | ~m1_subset_1(B_339, u1_struct_0(k3_lattice3('#skF_4'))))), inference(splitRight, [status(thm)], [c_4543])).
% 8.50/3.05  tff(c_4563, plain, (v2_struct_0(k3_lattice3('#skF_4'))), inference(splitLeft, [status(thm)], [c_4554])).
% 8.50/3.05  tff(c_4566, plain, (~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4563, c_66])).
% 8.50/3.05  tff(c_4569, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4566])).
% 8.50/3.05  tff(c_4571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4569])).
% 8.50/3.05  tff(c_4573, plain, (~v2_struct_0(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_4554])).
% 8.50/3.05  tff(c_4544, plain, (v3_orders_2(k3_lattice3('#skF_4'))), inference(splitRight, [status(thm)], [c_4502])).
% 8.50/3.05  tff(c_5114, plain, (![A_377, B_378, C_379]: (r3_orders_2(k3_lattice3(A_377), k4_lattice3(A_377, B_378), k4_lattice3(A_377, C_379)) | ~r3_lattices(A_377, B_378, C_379) | ~m1_subset_1(C_379, u1_struct_0(A_377)) | ~m1_subset_1(B_378, u1_struct_0(A_377)) | ~l3_lattices(A_377) | ~v10_lattices(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.50/3.05  tff(c_5143, plain, (![B_378]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_378), '#skF_5') | ~r3_lattices('#skF_4', B_378, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(B_378, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4358, c_5114])).
% 8.50/3.05  tff(c_5162, plain, (![B_378]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_378), '#skF_5') | ~r3_lattices('#skF_4', B_378, '#skF_5') | ~m1_subset_1(B_378, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_5143])).
% 8.50/3.05  tff(c_5194, plain, (![B_381]: (r3_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_381), '#skF_5') | ~r3_lattices('#skF_4', B_381, '#skF_5') | ~m1_subset_1(B_381, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5162])).
% 8.50/3.05  tff(c_4, plain, (![A_1, B_2, C_3]: (r1_orders_2(A_1, B_2, C_3) | ~r3_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.50/3.05  tff(c_5199, plain, (![B_381]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_381), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~m1_subset_1(k4_lattice3('#skF_4', B_381), u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~v3_orders_2(k3_lattice3('#skF_4')) | v2_struct_0(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', B_381, '#skF_5') | ~m1_subset_1(B_381, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_5194, c_4])).
% 8.50/3.05  tff(c_5216, plain, (![B_381]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_381), '#skF_5') | ~m1_subset_1(k4_lattice3('#skF_4', B_381), u1_struct_0(k3_lattice3('#skF_4'))) | v2_struct_0(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', B_381, '#skF_5') | ~m1_subset_1(B_381, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_4555, c_4401, c_5199])).
% 8.50/3.05  tff(c_5300, plain, (![B_386]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_386), '#skF_5') | ~m1_subset_1(k4_lattice3('#skF_4', B_386), u1_struct_0(k3_lattice3('#skF_4'))) | ~r3_lattices('#skF_4', B_386, '#skF_5') | ~m1_subset_1(B_386, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_4573, c_5216])).
% 8.50/3.05  tff(c_5314, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~r3_lattices('#skF_4', B_50, '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_5300])).
% 8.50/3.05  tff(c_5323, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~r3_lattices('#skF_4', B_50, '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5314])).
% 8.50/3.05  tff(c_5324, plain, (![B_50]: (r1_orders_2(k3_lattice3('#skF_4'), k4_lattice3('#skF_4', B_50), '#skF_5') | ~r3_lattices('#skF_4', B_50, '#skF_5') | ~m1_subset_1(B_50, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5323])).
% 8.50/3.05  tff(c_9517, plain, (![B_566]: (r1_orders_2(k3_lattice3('#skF_4'), '#skF_2'(k3_lattice3('#skF_4'), B_566, '#skF_5'), '#skF_5') | ~r3_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_566, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_566, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_566, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6481, c_5324])).
% 8.50/3.05  tff(c_38, plain, (![A_36, B_43, C_44]: (~r1_orders_2(A_36, '#skF_2'(A_36, B_43, C_44), C_44) | r2_lattice3(A_36, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.50/3.05  tff(c_9520, plain, (![B_566]: (~m1_subset_1('#skF_5', u1_struct_0(k3_lattice3('#skF_4'))) | ~l1_orders_2(k3_lattice3('#skF_4')) | ~r3_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_566, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_566, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_566, '#skF_5'))), inference(resolution, [status(thm)], [c_9517, c_38])).
% 8.50/3.05  tff(c_9524, plain, (![B_567]: (~r3_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_567, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_2'(k3_lattice3('#skF_4'), B_567, '#skF_5'), u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_567, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_4401, c_9520])).
% 8.50/3.05  tff(c_9624, plain, (![B_571]: (~r3_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_571, '#skF_5'), '#skF_5') | r2_lattice3(k3_lattice3('#skF_4'), B_571, '#skF_5'))), inference(resolution, [status(thm)], [c_6432, c_9524])).
% 8.50/3.05  tff(c_9629, plain, (![B_572]: (~r1_lattices('#skF_4', '#skF_2'(k3_lattice3('#skF_4'), B_572, '#skF_5'), '#skF_5') | r2_lattice3(k3_lattice3('#skF_4'), B_572, '#skF_5'))), inference(resolution, [status(thm)], [c_6462, c_9624])).
% 8.50/3.05  tff(c_9633, plain, (![B_43]: (~r4_lattice3('#skF_4', '#skF_5', B_43) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | r2_lattice3(k3_lattice3('#skF_4'), B_43, '#skF_5'))), inference(resolution, [status(thm)], [c_9184, c_9629])).
% 8.50/3.05  tff(c_9637, plain, (![B_573]: (~r4_lattice3('#skF_4', '#skF_5', B_573) | r2_lattice3(k3_lattice3('#skF_4'), B_573, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9633])).
% 8.50/3.05  tff(c_4341, plain, (~r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', k4_lattice3('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_86])).
% 8.50/3.05  tff(c_4359, plain, (~r2_lattice3(k3_lattice3('#skF_4'), '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4358, c_4341])).
% 8.50/3.05  tff(c_9643, plain, (~r4_lattice3('#skF_4', '#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_9637, c_4359])).
% 8.50/3.05  tff(c_9648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4340, c_9643])).
% 8.50/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.50/3.05  
% 8.50/3.05  Inference rules
% 8.50/3.05  ----------------------
% 8.50/3.05  #Ref     : 0
% 8.50/3.05  #Sup     : 2038
% 8.50/3.05  #Fact    : 0
% 8.50/3.05  #Define  : 0
% 8.50/3.05  #Split   : 27
% 8.50/3.05  #Chain   : 0
% 8.50/3.05  #Close   : 0
% 8.50/3.05  
% 8.50/3.05  Ordering : KBO
% 8.50/3.05  
% 8.50/3.05  Simplification rules
% 8.50/3.05  ----------------------
% 8.50/3.05  #Subsume      : 517
% 8.50/3.05  #Demod        : 1885
% 8.50/3.05  #Tautology    : 244
% 8.50/3.05  #SimpNegUnit  : 849
% 8.50/3.05  #BackRed      : 2
% 8.50/3.05  
% 8.50/3.05  #Partial instantiations: 0
% 8.50/3.05  #Strategies tried      : 1
% 8.50/3.05  
% 8.50/3.05  Timing (in seconds)
% 8.50/3.05  ----------------------
% 8.50/3.05  Preprocessing        : 0.33
% 8.50/3.05  Parsing              : 0.18
% 8.50/3.05  CNF conversion       : 0.03
% 8.50/3.05  Main loop            : 1.85
% 8.50/3.05  Inferencing          : 0.62
% 8.50/3.05  Reduction            : 0.61
% 8.50/3.05  Demodulation         : 0.38
% 8.50/3.05  BG Simplification    : 0.07
% 8.50/3.05  Subsumption          : 0.44
% 8.50/3.05  Abstraction          : 0.11
% 8.50/3.05  MUC search           : 0.00
% 8.50/3.05  Cooper               : 0.00
% 8.50/3.05  Total                : 2.26
% 8.50/3.05  Index Insertion      : 0.00
% 8.50/3.05  Index Deletion       : 0.00
% 8.50/3.05  Index Matching       : 0.00
% 8.50/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
