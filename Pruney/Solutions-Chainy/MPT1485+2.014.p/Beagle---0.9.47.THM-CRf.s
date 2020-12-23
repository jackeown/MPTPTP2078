%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:42 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 778 expanded)
%              Number of leaves         :   31 ( 317 expanded)
%              Depth                    :   16
%              Number of atoms          :  315 (3451 expanded)
%              Number of equality atoms :   34 ( 365 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k12_lattice3(A,B,k13_lattice3(A,B,C)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

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

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_50,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_158,plain,(
    ! [A_128,B_129,C_130] :
      ( k13_lattice3(A_128,B_129,C_130) = k10_lattice3(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v1_lattice3(A_128)
      | ~ v5_orders_2(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_162,plain,(
    ! [B_129] :
      ( k13_lattice3('#skF_3',B_129,'#skF_5') = k10_lattice3('#skF_3',B_129,'#skF_5')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_158])).

tff(c_176,plain,(
    ! [B_131] :
      ( k13_lattice3('#skF_3',B_131,'#skF_5') = k10_lattice3('#skF_3',B_131,'#skF_5')
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_162])).

tff(c_191,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_44,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_211,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_44])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(A_114,B_115,B_115)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [B_115] :
      ( r3_orders_2('#skF_3',B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_67,plain,(
    ! [B_115] :
      ( r3_orders_2('#skF_3',B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_62])).

tff(c_71,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_74])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k13_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_221,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_10])).

tff(c_229,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_221])).

tff(c_81,plain,(
    ! [B_117] :
      ( r3_orders_2('#skF_3',B_117,B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_87,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_468,plain,(
    ! [A_136,B_137,C_138] :
      ( r1_orders_2(A_136,B_137,C_138)
      | ~ r3_orders_2(A_136,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_478,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_468])).

tff(c_499,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_48,c_478])).

tff(c_500,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_499])).

tff(c_709,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_orders_2(A_147,B_148,k10_lattice3(A_147,B_148,C_149))
      | ~ m1_subset_1(k10_lattice3(A_147,B_148,C_149),u1_struct_0(A_147))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v1_lattice3(A_147)
      | ~ v5_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_717,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_229,c_709])).

tff(c_734,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_717])).

tff(c_735,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_734])).

tff(c_30,plain,(
    ! [A_57,B_81,C_93,D_99] :
      ( r1_orders_2(A_57,'#skF_2'(A_57,B_81,C_93,D_99),B_81)
      | k11_lattice3(A_57,B_81,C_93) = D_99
      | ~ r1_orders_2(A_57,D_99,C_93)
      | ~ r1_orders_2(A_57,D_99,B_81)
      | ~ m1_subset_1(D_99,u1_struct_0(A_57))
      | ~ m1_subset_1(C_93,u1_struct_0(A_57))
      | ~ m1_subset_1(B_81,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v2_lattice3(A_57)
      | ~ v5_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1065,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( ~ r1_orders_2(A_157,'#skF_2'(A_157,B_158,C_159,D_160),D_160)
      | k11_lattice3(A_157,B_158,C_159) = D_160
      | ~ r1_orders_2(A_157,D_160,C_159)
      | ~ r1_orders_2(A_157,D_160,B_158)
      | ~ m1_subset_1(D_160,u1_struct_0(A_157))
      | ~ m1_subset_1(C_159,u1_struct_0(A_157))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v2_lattice3(A_157)
      | ~ v5_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3637,plain,(
    ! [A_252,B_253,C_254] :
      ( k11_lattice3(A_252,B_253,C_254) = B_253
      | ~ r1_orders_2(A_252,B_253,C_254)
      | ~ r1_orders_2(A_252,B_253,B_253)
      | ~ m1_subset_1(C_254,u1_struct_0(A_252))
      | ~ m1_subset_1(B_253,u1_struct_0(A_252))
      | ~ l1_orders_2(A_252)
      | ~ v2_lattice3(A_252)
      | ~ v5_orders_2(A_252)
      | v2_struct_0(A_252) ) ),
    inference(resolution,[status(thm)],[c_30,c_1065])).

tff(c_3715,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_735,c_3637])).

tff(c_3882,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_229,c_500,c_3715])).

tff(c_3883,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3882])).

tff(c_88,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k13_lattice3(A_118,B_119,C_120),u1_struct_0(A_118))
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v1_lattice3(A_118)
      | ~ v5_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    ! [B_115] :
      ( r3_orders_2('#skF_3',B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_91,plain,(
    ! [B_119,C_120] :
      ( r3_orders_2('#skF_3',k13_lattice3('#skF_3',B_119,C_120),k13_lattice3('#skF_3',B_119,C_120))
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_79])).

tff(c_96,plain,(
    ! [B_119,C_120] :
      ( r3_orders_2('#skF_3',k13_lattice3('#skF_3',B_119,C_120),k13_lattice3('#skF_3',B_119,C_120))
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_91])).

tff(c_218,plain,
    ( r3_orders_2('#skF_3',k13_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_96])).

tff(c_227,plain,(
    r3_orders_2('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_191,c_218])).

tff(c_472,plain,
    ( r1_orders_2('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_227,c_468])).

tff(c_487,plain,
    ( r1_orders_2('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_229,c_472])).

tff(c_488,plain,(
    r1_orders_2('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_487])).

tff(c_2689,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( r1_orders_2(A_229,B_230,'#skF_1'(A_229,B_230,C_231,D_232))
      | k10_lattice3(A_229,B_230,C_231) = D_232
      | ~ r1_orders_2(A_229,C_231,D_232)
      | ~ r1_orders_2(A_229,B_230,D_232)
      | ~ m1_subset_1(D_232,u1_struct_0(A_229))
      | ~ m1_subset_1(C_231,u1_struct_0(A_229))
      | ~ m1_subset_1(B_230,u1_struct_0(A_229))
      | ~ l1_orders_2(A_229)
      | ~ v1_lattice3(A_229)
      | ~ v5_orders_2(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [A_11,D_53,B_35,C_47] :
      ( ~ r1_orders_2(A_11,D_53,'#skF_1'(A_11,B_35,C_47,D_53))
      | k10_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,C_47,D_53)
      | ~ r1_orders_2(A_11,B_35,D_53)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v1_lattice3(A_11)
      | ~ v5_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4276,plain,(
    ! [A_258,D_259,C_260] :
      ( k10_lattice3(A_258,D_259,C_260) = D_259
      | ~ r1_orders_2(A_258,C_260,D_259)
      | ~ r1_orders_2(A_258,D_259,D_259)
      | ~ m1_subset_1(C_260,u1_struct_0(A_258))
      | ~ m1_subset_1(D_259,u1_struct_0(A_258))
      | ~ l1_orders_2(A_258)
      | ~ v1_lattice3(A_258)
      | ~ v5_orders_2(A_258)
      | v2_struct_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_2689,c_12])).

tff(c_4354,plain,
    ( k10_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_735,c_4276])).

tff(c_4521,plain,
    ( k10_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_229,c_48,c_488,c_4354])).

tff(c_4522,plain,(
    k10_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4521])).

tff(c_164,plain,(
    ! [B_129] :
      ( k13_lattice3('#skF_3',B_129,'#skF_4') = k10_lattice3('#skF_3',B_129,'#skF_4')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_158])).

tff(c_324,plain,(
    ! [B_135] :
      ( k13_lattice3('#skF_3',B_135,'#skF_4') = k10_lattice3('#skF_3',B_135,'#skF_4')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_164])).

tff(c_341,plain,(
    k13_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_324])).

tff(c_4834,plain,(
    k13_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4522,c_341])).

tff(c_100,plain,(
    ! [A_123,B_124,C_125] :
      ( k12_lattice3(A_123,B_124,C_125) = k11_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_5131,plain,(
    ! [A_270,B_271,B_272,C_273] :
      ( k12_lattice3(A_270,B_271,k13_lattice3(A_270,B_272,C_273)) = k11_lattice3(A_270,B_271,k13_lattice3(A_270,B_272,C_273))
      | ~ m1_subset_1(B_271,u1_struct_0(A_270))
      | ~ v2_lattice3(A_270)
      | ~ m1_subset_1(C_273,u1_struct_0(A_270))
      | ~ m1_subset_1(B_272,u1_struct_0(A_270))
      | ~ l1_orders_2(A_270)
      | ~ v1_lattice3(A_270)
      | ~ v5_orders_2(A_270) ) ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_5149,plain,(
    ! [B_272,C_273] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_272,C_273)) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_272,C_273))
      | ~ v2_lattice3('#skF_3')
      | ~ m1_subset_1(C_273,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_272,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_5131])).

tff(c_6535,plain,(
    ! [B_303,C_304] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_303,C_304)) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_303,C_304))
      | ~ m1_subset_1(C_304,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_303,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_52,c_5149])).

tff(c_6643,plain,(
    ! [B_310] :
      ( k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_310,'#skF_4')) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',B_310,'#skF_4'))
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_6535])).

tff(c_6669,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')) = k11_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_229,c_6643])).

tff(c_6695,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3883,c_4834,c_4834,c_6669])).

tff(c_6697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_6695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.81  
% 7.93/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.81  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.93/2.81  
% 7.93/2.81  %Foreground sorts:
% 7.93/2.81  
% 7.93/2.81  
% 7.93/2.81  %Background operators:
% 7.93/2.81  
% 7.93/2.81  
% 7.93/2.81  %Foreground operators:
% 7.93/2.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.93/2.81  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 7.93/2.81  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.93/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/2.81  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 7.93/2.81  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.93/2.81  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 7.93/2.81  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 7.93/2.81  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 7.93/2.81  tff('#skF_5', type, '#skF_5': $i).
% 7.93/2.81  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 7.93/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.93/2.81  tff('#skF_3', type, '#skF_3': $i).
% 7.93/2.81  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.93/2.81  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.93/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.93/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/2.81  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 7.93/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.93/2.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.93/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.93/2.81  
% 8.22/2.83  tff(f_181, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 8.22/2.83  tff(f_162, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 8.22/2.83  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 8.22/2.83  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 8.22/2.83  tff(f_72, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 8.22/2.83  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 8.22/2.83  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 8.22/2.83  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 8.22/2.83  tff(f_150, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 8.22/2.83  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_50, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_158, plain, (![A_128, B_129, C_130]: (k13_lattice3(A_128, B_129, C_130)=k10_lattice3(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v1_lattice3(A_128) | ~v5_orders_2(A_128))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.22/2.83  tff(c_162, plain, (![B_129]: (k13_lattice3('#skF_3', B_129, '#skF_5')=k10_lattice3('#skF_3', B_129, '#skF_5') | ~m1_subset_1(B_129, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_158])).
% 8.22/2.83  tff(c_176, plain, (![B_131]: (k13_lattice3('#skF_3', B_131, '#skF_5')=k10_lattice3('#skF_3', B_131, '#skF_5') | ~m1_subset_1(B_131, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_162])).
% 8.22/2.83  tff(c_191, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_176])).
% 8.22/2.83  tff(c_44, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_211, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_44])).
% 8.22/2.83  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_60, plain, (![A_114, B_115, C_116]: (r3_orders_2(A_114, B_115, B_115) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/2.83  tff(c_62, plain, (![B_115]: (r3_orders_2('#skF_3', B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_60])).
% 8.22/2.83  tff(c_67, plain, (![B_115]: (r3_orders_2('#skF_3', B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_62])).
% 8.22/2.83  tff(c_71, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_67])).
% 8.22/2.83  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.22/2.83  tff(c_74, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_71, c_8])).
% 8.22/2.83  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_74])).
% 8.22/2.83  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 8.22/2.83  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.22/2.83  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k13_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.22/2.83  tff(c_221, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_10])).
% 8.22/2.83  tff(c_229, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_221])).
% 8.22/2.83  tff(c_81, plain, (![B_117]: (r3_orders_2('#skF_3', B_117, B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_67])).
% 8.22/2.83  tff(c_87, plain, (r3_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_81])).
% 8.22/2.83  tff(c_468, plain, (![A_136, B_137, C_138]: (r1_orders_2(A_136, B_137, C_138) | ~r3_orders_2(A_136, B_137, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.22/2.83  tff(c_478, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_87, c_468])).
% 8.22/2.83  tff(c_499, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_48, c_478])).
% 8.22/2.83  tff(c_500, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_499])).
% 8.22/2.83  tff(c_709, plain, (![A_147, B_148, C_149]: (r1_orders_2(A_147, B_148, k10_lattice3(A_147, B_148, C_149)) | ~m1_subset_1(k10_lattice3(A_147, B_148, C_149), u1_struct_0(A_147)) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v1_lattice3(A_147) | ~v5_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.22/2.83  tff(c_717, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_229, c_709])).
% 8.22/2.83  tff(c_734, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_717])).
% 8.22/2.83  tff(c_735, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_734])).
% 8.22/2.83  tff(c_30, plain, (![A_57, B_81, C_93, D_99]: (r1_orders_2(A_57, '#skF_2'(A_57, B_81, C_93, D_99), B_81) | k11_lattice3(A_57, B_81, C_93)=D_99 | ~r1_orders_2(A_57, D_99, C_93) | ~r1_orders_2(A_57, D_99, B_81) | ~m1_subset_1(D_99, u1_struct_0(A_57)) | ~m1_subset_1(C_93, u1_struct_0(A_57)) | ~m1_subset_1(B_81, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v2_lattice3(A_57) | ~v5_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.22/2.83  tff(c_1065, plain, (![A_157, B_158, C_159, D_160]: (~r1_orders_2(A_157, '#skF_2'(A_157, B_158, C_159, D_160), D_160) | k11_lattice3(A_157, B_158, C_159)=D_160 | ~r1_orders_2(A_157, D_160, C_159) | ~r1_orders_2(A_157, D_160, B_158) | ~m1_subset_1(D_160, u1_struct_0(A_157)) | ~m1_subset_1(C_159, u1_struct_0(A_157)) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v2_lattice3(A_157) | ~v5_orders_2(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.22/2.83  tff(c_3637, plain, (![A_252, B_253, C_254]: (k11_lattice3(A_252, B_253, C_254)=B_253 | ~r1_orders_2(A_252, B_253, C_254) | ~r1_orders_2(A_252, B_253, B_253) | ~m1_subset_1(C_254, u1_struct_0(A_252)) | ~m1_subset_1(B_253, u1_struct_0(A_252)) | ~l1_orders_2(A_252) | ~v2_lattice3(A_252) | ~v5_orders_2(A_252) | v2_struct_0(A_252))), inference(resolution, [status(thm)], [c_30, c_1065])).
% 8.22/2.83  tff(c_3715, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_735, c_3637])).
% 8.22/2.83  tff(c_3882, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_229, c_500, c_3715])).
% 8.22/2.83  tff(c_3883, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80, c_3882])).
% 8.22/2.83  tff(c_88, plain, (![A_118, B_119, C_120]: (m1_subset_1(k13_lattice3(A_118, B_119, C_120), u1_struct_0(A_118)) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v1_lattice3(A_118) | ~v5_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.22/2.83  tff(c_79, plain, (![B_115]: (r3_orders_2('#skF_3', B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_67])).
% 8.22/2.83  tff(c_91, plain, (![B_119, C_120]: (r3_orders_2('#skF_3', k13_lattice3('#skF_3', B_119, C_120), k13_lattice3('#skF_3', B_119, C_120)) | ~m1_subset_1(C_120, u1_struct_0('#skF_3')) | ~m1_subset_1(B_119, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_88, c_79])).
% 8.22/2.83  tff(c_96, plain, (![B_119, C_120]: (r3_orders_2('#skF_3', k13_lattice3('#skF_3', B_119, C_120), k13_lattice3('#skF_3', B_119, C_120)) | ~m1_subset_1(C_120, u1_struct_0('#skF_3')) | ~m1_subset_1(B_119, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_91])).
% 8.22/2.83  tff(c_218, plain, (r3_orders_2('#skF_3', k13_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_96])).
% 8.22/2.83  tff(c_227, plain, (r3_orders_2('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_191, c_218])).
% 8.22/2.83  tff(c_472, plain, (r1_orders_2('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_227, c_468])).
% 8.22/2.83  tff(c_487, plain, (r1_orders_2('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_229, c_472])).
% 8.22/2.83  tff(c_488, plain, (r1_orders_2('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_487])).
% 8.22/2.83  tff(c_2689, plain, (![A_229, B_230, C_231, D_232]: (r1_orders_2(A_229, B_230, '#skF_1'(A_229, B_230, C_231, D_232)) | k10_lattice3(A_229, B_230, C_231)=D_232 | ~r1_orders_2(A_229, C_231, D_232) | ~r1_orders_2(A_229, B_230, D_232) | ~m1_subset_1(D_232, u1_struct_0(A_229)) | ~m1_subset_1(C_231, u1_struct_0(A_229)) | ~m1_subset_1(B_230, u1_struct_0(A_229)) | ~l1_orders_2(A_229) | ~v1_lattice3(A_229) | ~v5_orders_2(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.22/2.83  tff(c_12, plain, (![A_11, D_53, B_35, C_47]: (~r1_orders_2(A_11, D_53, '#skF_1'(A_11, B_35, C_47, D_53)) | k10_lattice3(A_11, B_35, C_47)=D_53 | ~r1_orders_2(A_11, C_47, D_53) | ~r1_orders_2(A_11, B_35, D_53) | ~m1_subset_1(D_53, u1_struct_0(A_11)) | ~m1_subset_1(C_47, u1_struct_0(A_11)) | ~m1_subset_1(B_35, u1_struct_0(A_11)) | ~l1_orders_2(A_11) | ~v1_lattice3(A_11) | ~v5_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.22/2.83  tff(c_4276, plain, (![A_258, D_259, C_260]: (k10_lattice3(A_258, D_259, C_260)=D_259 | ~r1_orders_2(A_258, C_260, D_259) | ~r1_orders_2(A_258, D_259, D_259) | ~m1_subset_1(C_260, u1_struct_0(A_258)) | ~m1_subset_1(D_259, u1_struct_0(A_258)) | ~l1_orders_2(A_258) | ~v1_lattice3(A_258) | ~v5_orders_2(A_258) | v2_struct_0(A_258))), inference(resolution, [status(thm)], [c_2689, c_12])).
% 8.22/2.83  tff(c_4354, plain, (k10_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_735, c_4276])).
% 8.22/2.83  tff(c_4521, plain, (k10_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_229, c_48, c_488, c_4354])).
% 8.22/2.83  tff(c_4522, plain, (k10_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_4521])).
% 8.22/2.83  tff(c_164, plain, (![B_129]: (k13_lattice3('#skF_3', B_129, '#skF_4')=k10_lattice3('#skF_3', B_129, '#skF_4') | ~m1_subset_1(B_129, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_158])).
% 8.22/2.83  tff(c_324, plain, (![B_135]: (k13_lattice3('#skF_3', B_135, '#skF_4')=k10_lattice3('#skF_3', B_135, '#skF_4') | ~m1_subset_1(B_135, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_164])).
% 8.22/2.83  tff(c_341, plain, (k13_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_229, c_324])).
% 8.22/2.83  tff(c_4834, plain, (k13_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4522, c_341])).
% 8.22/2.83  tff(c_100, plain, (![A_123, B_124, C_125]: (k12_lattice3(A_123, B_124, C_125)=k11_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.22/2.83  tff(c_5131, plain, (![A_270, B_271, B_272, C_273]: (k12_lattice3(A_270, B_271, k13_lattice3(A_270, B_272, C_273))=k11_lattice3(A_270, B_271, k13_lattice3(A_270, B_272, C_273)) | ~m1_subset_1(B_271, u1_struct_0(A_270)) | ~v2_lattice3(A_270) | ~m1_subset_1(C_273, u1_struct_0(A_270)) | ~m1_subset_1(B_272, u1_struct_0(A_270)) | ~l1_orders_2(A_270) | ~v1_lattice3(A_270) | ~v5_orders_2(A_270))), inference(resolution, [status(thm)], [c_10, c_100])).
% 8.22/2.83  tff(c_5149, plain, (![B_272, C_273]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_272, C_273))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_272, C_273)) | ~v2_lattice3('#skF_3') | ~m1_subset_1(C_273, u1_struct_0('#skF_3')) | ~m1_subset_1(B_272, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_5131])).
% 8.22/2.83  tff(c_6535, plain, (![B_303, C_304]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_303, C_304))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_303, C_304)) | ~m1_subset_1(C_304, u1_struct_0('#skF_3')) | ~m1_subset_1(B_303, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_52, c_5149])).
% 8.22/2.83  tff(c_6643, plain, (![B_310]: (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_310, '#skF_4'))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', B_310, '#skF_4')) | ~m1_subset_1(B_310, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_6535])).
% 8.22/2.83  tff(c_6669, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4'))=k11_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_229, c_6643])).
% 8.22/2.83  tff(c_6695, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3883, c_4834, c_4834, c_6669])).
% 8.22/2.83  tff(c_6697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_6695])).
% 8.22/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.83  
% 8.22/2.83  Inference rules
% 8.22/2.83  ----------------------
% 8.22/2.83  #Ref     : 0
% 8.22/2.83  #Sup     : 1340
% 8.22/2.83  #Fact    : 0
% 8.22/2.83  #Define  : 0
% 8.22/2.83  #Split   : 14
% 8.22/2.83  #Chain   : 0
% 8.22/2.83  #Close   : 0
% 8.22/2.83  
% 8.22/2.83  Ordering : KBO
% 8.22/2.83  
% 8.22/2.83  Simplification rules
% 8.22/2.83  ----------------------
% 8.22/2.83  #Subsume      : 48
% 8.22/2.83  #Demod        : 3681
% 8.22/2.83  #Tautology    : 519
% 8.22/2.83  #SimpNegUnit  : 539
% 8.22/2.83  #BackRed      : 107
% 8.22/2.83  
% 8.22/2.83  #Partial instantiations: 0
% 8.22/2.83  #Strategies tried      : 1
% 8.22/2.83  
% 8.22/2.83  Timing (in seconds)
% 8.22/2.83  ----------------------
% 8.22/2.83  Preprocessing        : 0.38
% 8.22/2.83  Parsing              : 0.20
% 8.22/2.83  CNF conversion       : 0.04
% 8.22/2.83  Main loop            : 1.62
% 8.22/2.83  Inferencing          : 0.45
% 8.22/2.83  Reduction            : 0.68
% 8.22/2.83  Demodulation         : 0.52
% 8.22/2.83  BG Simplification    : 0.06
% 8.22/2.83  Subsumption          : 0.33
% 8.22/2.83  Abstraction          : 0.08
% 8.22/2.83  MUC search           : 0.00
% 8.22/2.83  Cooper               : 0.00
% 8.22/2.83  Total                : 2.04
% 8.22/2.83  Index Insertion      : 0.00
% 8.22/2.83  Index Deletion       : 0.00
% 8.22/2.83  Index Matching       : 0.00
% 8.22/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
