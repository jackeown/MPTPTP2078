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
% DateTime   : Thu Dec  3 10:30:56 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 466 expanded)
%              Number of leaves         :   37 ( 171 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 (1950 expanded)
%              Number of equality atoms :    2 (   7 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
              & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_7)).

tff(f_73,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k1_yellow_0(A,C)
            <=> ( r2_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,C,D)
                     => r1_orders_2(A,B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow_0)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

tff(c_54,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_yellow_0(A_19,B_20),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_yellow_0(A_17,B_18),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_107,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(A_114,B_115,C_116)
      | ~ r1_orders_2(A_114,B_115,C_116)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [A_120,B_121,B_122] :
      ( r3_orders_2(A_120,B_121,k1_yellow_0(A_120,B_122))
      | ~ r1_orders_2(A_120,B_121,k1_yellow_0(A_120,B_122))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120)
      | ~ l1_orders_2(A_120) ) ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_50,plain,
    ( ~ r1_orders_2('#skF_4',k2_yellow_0('#skF_4','#skF_6'),k2_yellow_0('#skF_4','#skF_5'))
    | ~ r3_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_68,plain,(
    ~ r3_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_120,plain,
    ( ~ r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_68])).

tff(c_124,plain,
    ( ~ r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66,c_120])).

tff(c_125,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_128,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_128])).

tff(c_134,plain,(
    m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r3_orders_2(A_1,B_2,C_3)
      | ~ r1_orders_2(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,u1_struct_0(A_1))
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_4',B_2,k1_yellow_0('#skF_4','#skF_5'))
      | ~ r1_orders_2('#skF_4',B_2,k1_yellow_0('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_139,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_4',B_2,k1_yellow_0('#skF_4','#skF_5'))
      | ~ r1_orders_2('#skF_4',B_2,k1_yellow_0('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_136])).

tff(c_141,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_6])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_144])).

tff(c_150,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_62,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_56,plain,(
    v3_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_83,plain,(
    ! [A_100,C_101] :
      ( r2_lattice3(A_100,C_101,k1_yellow_0(A_100,C_101))
      | ~ m1_subset_1(k1_yellow_0(A_100,C_101),u1_struct_0(A_100))
      | ~ l1_orders_2(A_100)
      | ~ v3_lattice3(A_100)
      | ~ v5_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_87,plain,(
    ! [A_102,B_103] :
      ( r2_lattice3(A_102,B_103,k1_yellow_0(A_102,B_103))
      | ~ v3_lattice3(A_102)
      | ~ v5_orders_2(A_102)
      | v2_struct_0(A_102)
      | ~ l1_orders_2(A_102) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_46,plain,(
    ! [A_68,B_73,D_76,C_74] :
      ( r2_lattice3(A_68,B_73,D_76)
      | ~ r2_lattice3(A_68,C_74,D_76)
      | ~ m1_subset_1(D_76,u1_struct_0(A_68))
      | ~ r1_tarski(B_73,C_74)
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_167,plain,(
    ! [A_133,B_134,B_135] :
      ( r2_lattice3(A_133,B_134,k1_yellow_0(A_133,B_135))
      | ~ m1_subset_1(k1_yellow_0(A_133,B_135),u1_struct_0(A_133))
      | ~ r1_tarski(B_134,B_135)
      | ~ v3_lattice3(A_133)
      | ~ v5_orders_2(A_133)
      | v2_struct_0(A_133)
      | ~ l1_orders_2(A_133) ) ),
    inference(resolution,[status(thm)],[c_87,c_46])).

tff(c_176,plain,(
    ! [A_17,B_134,B_18] :
      ( r2_lattice3(A_17,B_134,k1_yellow_0(A_17,B_18))
      | ~ r1_tarski(B_134,B_18)
      | ~ v3_lattice3(A_17)
      | ~ v5_orders_2(A_17)
      | v2_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_346,plain,(
    ! [A_245,C_246,D_247] :
      ( r1_orders_2(A_245,k1_yellow_0(A_245,C_246),D_247)
      | ~ r2_lattice3(A_245,C_246,D_247)
      | ~ m1_subset_1(D_247,u1_struct_0(A_245))
      | ~ m1_subset_1(k1_yellow_0(A_245,C_246),u1_struct_0(A_245))
      | ~ l1_orders_2(A_245)
      | ~ v3_lattice3(A_245)
      | ~ v5_orders_2(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_348,plain,(
    ! [D_247] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),D_247)
      | ~ r2_lattice3('#skF_4','#skF_5',D_247)
      | ~ m1_subset_1(D_247,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_346])).

tff(c_353,plain,(
    ! [D_247] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),D_247)
      | ~ r2_lattice3('#skF_4','#skF_5',D_247)
      | ~ m1_subset_1(D_247,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_348])).

tff(c_360,plain,(
    ! [D_252] :
      ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),D_252)
      | ~ r2_lattice3('#skF_4','#skF_5',D_252)
      | ~ m1_subset_1(D_252,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_353])).

tff(c_133,plain,
    ( ~ r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_140,plain,(
    ~ r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_372,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5',k1_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_360,c_140])).

tff(c_373,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_376,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_376])).

tff(c_381,plain,(
    ~ r2_lattice3('#skF_4','#skF_5',k1_yellow_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_403,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ v3_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_381])).

tff(c_414,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_56,c_52,c_403])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_414])).

tff(c_417,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_422,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_417,c_6])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_422])).

tff(c_428,plain,(
    r3_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_467,plain,(
    ! [A_290,B_291,C_292] :
      ( r1_orders_2(A_290,B_291,C_292)
      | ~ r3_orders_2(A_290,B_291,C_292)
      | ~ m1_subset_1(C_292,u1_struct_0(A_290))
      | ~ m1_subset_1(B_291,u1_struct_0(A_290))
      | ~ l1_orders_2(A_290)
      | ~ v3_orders_2(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_469,plain,
    ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_428,c_467])).

tff(c_472,plain,
    ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_469])).

tff(c_481,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_484,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_481])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_484])).

tff(c_489,plain,
    ( ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_496,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_489])).

tff(c_499,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_496])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_499])).

tff(c_504,plain,
    ( r1_orders_2('#skF_4',k1_yellow_0('#skF_4','#skF_5'),k1_yellow_0('#skF_4','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_489])).

tff(c_511,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_514,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_511,c_6])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_514])).

tff(c_520,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_24,plain,(
    ! [A_21,B_23] :
      ( r2_yellow_0(A_21,B_23)
      | ~ l1_orders_2(A_21)
      | ~ v3_lattice3(A_21)
      | ~ v5_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_435,plain,(
    ! [A_272,B_273] :
      ( r1_lattice3(A_272,B_273,k2_yellow_0(A_272,B_273))
      | ~ r2_yellow_0(A_272,B_273)
      | ~ m1_subset_1(k2_yellow_0(A_272,B_273),u1_struct_0(A_272))
      | ~ l1_orders_2(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_439,plain,(
    ! [A_274,B_275] :
      ( r1_lattice3(A_274,B_275,k2_yellow_0(A_274,B_275))
      | ~ r2_yellow_0(A_274,B_275)
      | ~ l1_orders_2(A_274) ) ),
    inference(resolution,[status(thm)],[c_20,c_435])).

tff(c_48,plain,(
    ! [A_68,B_73,D_76,C_74] :
      ( r1_lattice3(A_68,B_73,D_76)
      | ~ r1_lattice3(A_68,C_74,D_76)
      | ~ m1_subset_1(D_76,u1_struct_0(A_68))
      | ~ r1_tarski(B_73,C_74)
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_459,plain,(
    ! [A_284,B_285,B_286] :
      ( r1_lattice3(A_284,B_285,k2_yellow_0(A_284,B_286))
      | ~ m1_subset_1(k2_yellow_0(A_284,B_286),u1_struct_0(A_284))
      | ~ r1_tarski(B_285,B_286)
      | ~ r2_yellow_0(A_284,B_286)
      | ~ l1_orders_2(A_284) ) ),
    inference(resolution,[status(thm)],[c_439,c_48])).

tff(c_462,plain,(
    ! [A_19,B_285,B_20] :
      ( r1_lattice3(A_19,B_285,k2_yellow_0(A_19,B_20))
      | ~ r1_tarski(B_285,B_20)
      | ~ r2_yellow_0(A_19,B_20)
      | ~ l1_orders_2(A_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_459])).

tff(c_581,plain,(
    ! [A_318,D_319,B_320] :
      ( r1_orders_2(A_318,D_319,k2_yellow_0(A_318,B_320))
      | ~ r1_lattice3(A_318,B_320,D_319)
      | ~ m1_subset_1(D_319,u1_struct_0(A_318))
      | ~ r2_yellow_0(A_318,B_320)
      | ~ m1_subset_1(k2_yellow_0(A_318,B_320),u1_struct_0(A_318))
      | ~ l1_orders_2(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_599,plain,(
    ! [A_328,D_329,B_330] :
      ( r1_orders_2(A_328,D_329,k2_yellow_0(A_328,B_330))
      | ~ r1_lattice3(A_328,B_330,D_329)
      | ~ m1_subset_1(D_329,u1_struct_0(A_328))
      | ~ r2_yellow_0(A_328,B_330)
      | ~ l1_orders_2(A_328) ) ),
    inference(resolution,[status(thm)],[c_20,c_581])).

tff(c_427,plain,(
    ~ r1_orders_2('#skF_4',k2_yellow_0('#skF_4','#skF_6'),k2_yellow_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_606,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5',k2_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k2_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ r2_yellow_0('#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_599,c_427])).

tff(c_610,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5',k2_yellow_0('#skF_4','#skF_6'))
    | ~ m1_subset_1(k2_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ r2_yellow_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_606])).

tff(c_611,plain,(
    ~ r2_yellow_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_615,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v3_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_611])).

tff(c_618,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_615])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_618])).

tff(c_621,plain,
    ( ~ m1_subset_1(k2_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ r1_lattice3('#skF_4','#skF_5',k2_yellow_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_623,plain,(
    ~ r1_lattice3('#skF_4','#skF_5',k2_yellow_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_626,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r2_yellow_0('#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_462,c_623])).

tff(c_629,plain,(
    ~ r2_yellow_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_626])).

tff(c_632,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v3_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_629])).

tff(c_635,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_632])).

tff(c_637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_635])).

tff(c_638,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_642,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_638])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.59  
% 3.27/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.59  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.27/1.59  
% 3.27/1.59  %Foreground sorts:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Background operators:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Foreground operators:
% 3.27/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.59  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.27/1.59  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.27/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.59  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.27/1.59  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 3.27/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.59  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.27/1.59  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.27/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.59  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 3.27/1.59  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.27/1.59  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.27/1.59  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.27/1.59  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.27/1.59  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.27/1.59  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.59  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.27/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.59  
% 3.27/1.61  tff(f_173, negated_conjecture, ~(![A]: (((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B, C]: (r1_tarski(B, C) => (r3_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)) & r1_orders_2(A, k2_yellow_0(A, C), k2_yellow_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_waybel_7)).
% 3.27/1.61  tff(f_73, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 3.27/1.61  tff(f_69, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 3.27/1.61  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.27/1.61  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.27/1.61  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k1_yellow_0(A, C)) <=> (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_yellow_0)).
% 3.27/1.61  tff(f_151, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 3.27/1.61  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) & r2_yellow_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_0)).
% 3.27/1.61  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 3.27/1.61  tff(c_54, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k2_yellow_0(A_19, B_20), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.27/1.61  tff(c_60, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k1_yellow_0(A_17, B_18), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.61  tff(c_66, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_107, plain, (![A_114, B_115, C_116]: (r3_orders_2(A_114, B_115, C_116) | ~r1_orders_2(A_114, B_115, C_116) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.27/1.61  tff(c_115, plain, (![A_120, B_121, B_122]: (r3_orders_2(A_120, B_121, k1_yellow_0(A_120, B_122)) | ~r1_orders_2(A_120, B_121, k1_yellow_0(A_120, B_122)) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~v3_orders_2(A_120) | v2_struct_0(A_120) | ~l1_orders_2(A_120))), inference(resolution, [status(thm)], [c_18, c_107])).
% 3.27/1.61  tff(c_50, plain, (~r1_orders_2('#skF_4', k2_yellow_0('#skF_4', '#skF_6'), k2_yellow_0('#skF_4', '#skF_5')) | ~r3_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_68, plain, (~r3_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_120, plain, (~r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_115, c_68])).
% 3.27/1.61  tff(c_124, plain, (~r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66, c_120])).
% 3.27/1.61  tff(c_125, plain, (~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_124])).
% 3.27/1.61  tff(c_128, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_18, c_125])).
% 3.27/1.61  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_128])).
% 3.27/1.61  tff(c_134, plain, (m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_124])).
% 3.27/1.61  tff(c_2, plain, (![A_1, B_2, C_3]: (r3_orders_2(A_1, B_2, C_3) | ~r1_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.27/1.61  tff(c_136, plain, (![B_2]: (r3_orders_2('#skF_4', B_2, k1_yellow_0('#skF_4', '#skF_5')) | ~r1_orders_2('#skF_4', B_2, k1_yellow_0('#skF_4', '#skF_5')) | ~m1_subset_1(B_2, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.27/1.61  tff(c_139, plain, (![B_2]: (r3_orders_2('#skF_4', B_2, k1_yellow_0('#skF_4', '#skF_5')) | ~r1_orders_2('#skF_4', B_2, k1_yellow_0('#skF_4', '#skF_5')) | ~m1_subset_1(B_2, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_136])).
% 3.27/1.61  tff(c_141, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_139])).
% 3.27/1.61  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.61  tff(c_144, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_141, c_6])).
% 3.27/1.61  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_144])).
% 3.27/1.61  tff(c_150, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_139])).
% 3.27/1.61  tff(c_62, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_56, plain, (v3_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.27/1.61  tff(c_83, plain, (![A_100, C_101]: (r2_lattice3(A_100, C_101, k1_yellow_0(A_100, C_101)) | ~m1_subset_1(k1_yellow_0(A_100, C_101), u1_struct_0(A_100)) | ~l1_orders_2(A_100) | ~v3_lattice3(A_100) | ~v5_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.27/1.61  tff(c_87, plain, (![A_102, B_103]: (r2_lattice3(A_102, B_103, k1_yellow_0(A_102, B_103)) | ~v3_lattice3(A_102) | ~v5_orders_2(A_102) | v2_struct_0(A_102) | ~l1_orders_2(A_102))), inference(resolution, [status(thm)], [c_18, c_83])).
% 3.27/1.61  tff(c_46, plain, (![A_68, B_73, D_76, C_74]: (r2_lattice3(A_68, B_73, D_76) | ~r2_lattice3(A_68, C_74, D_76) | ~m1_subset_1(D_76, u1_struct_0(A_68)) | ~r1_tarski(B_73, C_74) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.27/1.61  tff(c_167, plain, (![A_133, B_134, B_135]: (r2_lattice3(A_133, B_134, k1_yellow_0(A_133, B_135)) | ~m1_subset_1(k1_yellow_0(A_133, B_135), u1_struct_0(A_133)) | ~r1_tarski(B_134, B_135) | ~v3_lattice3(A_133) | ~v5_orders_2(A_133) | v2_struct_0(A_133) | ~l1_orders_2(A_133))), inference(resolution, [status(thm)], [c_87, c_46])).
% 3.27/1.61  tff(c_176, plain, (![A_17, B_134, B_18]: (r2_lattice3(A_17, B_134, k1_yellow_0(A_17, B_18)) | ~r1_tarski(B_134, B_18) | ~v3_lattice3(A_17) | ~v5_orders_2(A_17) | v2_struct_0(A_17) | ~l1_orders_2(A_17))), inference(resolution, [status(thm)], [c_18, c_167])).
% 3.27/1.61  tff(c_346, plain, (![A_245, C_246, D_247]: (r1_orders_2(A_245, k1_yellow_0(A_245, C_246), D_247) | ~r2_lattice3(A_245, C_246, D_247) | ~m1_subset_1(D_247, u1_struct_0(A_245)) | ~m1_subset_1(k1_yellow_0(A_245, C_246), u1_struct_0(A_245)) | ~l1_orders_2(A_245) | ~v3_lattice3(A_245) | ~v5_orders_2(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.27/1.61  tff(c_348, plain, (![D_247]: (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), D_247) | ~r2_lattice3('#skF_4', '#skF_5', D_247) | ~m1_subset_1(D_247, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_134, c_346])).
% 3.27/1.61  tff(c_353, plain, (![D_247]: (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), D_247) | ~r2_lattice3('#skF_4', '#skF_5', D_247) | ~m1_subset_1(D_247, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_348])).
% 3.27/1.61  tff(c_360, plain, (![D_252]: (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), D_252) | ~r2_lattice3('#skF_4', '#skF_5', D_252) | ~m1_subset_1(D_252, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_150, c_353])).
% 3.27/1.61  tff(c_133, plain, (~r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_124])).
% 3.27/1.61  tff(c_140, plain, (~r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_133])).
% 3.27/1.61  tff(c_372, plain, (~r2_lattice3('#skF_4', '#skF_5', k1_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_360, c_140])).
% 3.27/1.61  tff(c_373, plain, (~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_372])).
% 3.27/1.61  tff(c_376, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_18, c_373])).
% 3.27/1.61  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_376])).
% 3.27/1.61  tff(c_381, plain, (~r2_lattice3('#skF_4', '#skF_5', k1_yellow_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_372])).
% 3.27/1.61  tff(c_403, plain, (~r1_tarski('#skF_5', '#skF_6') | ~v3_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_176, c_381])).
% 3.27/1.61  tff(c_414, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_56, c_52, c_403])).
% 3.27/1.61  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_414])).
% 3.27/1.61  tff(c_417, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_133])).
% 3.27/1.61  tff(c_422, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_417, c_6])).
% 3.27/1.61  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_422])).
% 3.27/1.61  tff(c_428, plain, (r3_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_467, plain, (![A_290, B_291, C_292]: (r1_orders_2(A_290, B_291, C_292) | ~r3_orders_2(A_290, B_291, C_292) | ~m1_subset_1(C_292, u1_struct_0(A_290)) | ~m1_subset_1(B_291, u1_struct_0(A_290)) | ~l1_orders_2(A_290) | ~v3_orders_2(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.27/1.61  tff(c_469, plain, (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_428, c_467])).
% 3.27/1.61  tff(c_472, plain, (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_469])).
% 3.27/1.61  tff(c_481, plain, (~m1_subset_1(k1_yellow_0('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_472])).
% 3.27/1.61  tff(c_484, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_18, c_481])).
% 3.27/1.61  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_484])).
% 3.27/1.61  tff(c_489, plain, (~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_472])).
% 3.27/1.61  tff(c_496, plain, (~m1_subset_1(k1_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_489])).
% 3.27/1.61  tff(c_499, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_18, c_496])).
% 3.27/1.61  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_499])).
% 3.27/1.61  tff(c_504, plain, (r1_orders_2('#skF_4', k1_yellow_0('#skF_4', '#skF_5'), k1_yellow_0('#skF_4', '#skF_6')) | v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_489])).
% 3.27/1.61  tff(c_511, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_504])).
% 3.27/1.61  tff(c_514, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_511, c_6])).
% 3.27/1.61  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_514])).
% 3.27/1.61  tff(c_520, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_504])).
% 3.27/1.61  tff(c_24, plain, (![A_21, B_23]: (r2_yellow_0(A_21, B_23) | ~l1_orders_2(A_21) | ~v3_lattice3(A_21) | ~v5_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.27/1.61  tff(c_435, plain, (![A_272, B_273]: (r1_lattice3(A_272, B_273, k2_yellow_0(A_272, B_273)) | ~r2_yellow_0(A_272, B_273) | ~m1_subset_1(k2_yellow_0(A_272, B_273), u1_struct_0(A_272)) | ~l1_orders_2(A_272))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.61  tff(c_439, plain, (![A_274, B_275]: (r1_lattice3(A_274, B_275, k2_yellow_0(A_274, B_275)) | ~r2_yellow_0(A_274, B_275) | ~l1_orders_2(A_274))), inference(resolution, [status(thm)], [c_20, c_435])).
% 3.27/1.61  tff(c_48, plain, (![A_68, B_73, D_76, C_74]: (r1_lattice3(A_68, B_73, D_76) | ~r1_lattice3(A_68, C_74, D_76) | ~m1_subset_1(D_76, u1_struct_0(A_68)) | ~r1_tarski(B_73, C_74) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.27/1.61  tff(c_459, plain, (![A_284, B_285, B_286]: (r1_lattice3(A_284, B_285, k2_yellow_0(A_284, B_286)) | ~m1_subset_1(k2_yellow_0(A_284, B_286), u1_struct_0(A_284)) | ~r1_tarski(B_285, B_286) | ~r2_yellow_0(A_284, B_286) | ~l1_orders_2(A_284))), inference(resolution, [status(thm)], [c_439, c_48])).
% 3.27/1.61  tff(c_462, plain, (![A_19, B_285, B_20]: (r1_lattice3(A_19, B_285, k2_yellow_0(A_19, B_20)) | ~r1_tarski(B_285, B_20) | ~r2_yellow_0(A_19, B_20) | ~l1_orders_2(A_19))), inference(resolution, [status(thm)], [c_20, c_459])).
% 3.27/1.61  tff(c_581, plain, (![A_318, D_319, B_320]: (r1_orders_2(A_318, D_319, k2_yellow_0(A_318, B_320)) | ~r1_lattice3(A_318, B_320, D_319) | ~m1_subset_1(D_319, u1_struct_0(A_318)) | ~r2_yellow_0(A_318, B_320) | ~m1_subset_1(k2_yellow_0(A_318, B_320), u1_struct_0(A_318)) | ~l1_orders_2(A_318))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.61  tff(c_599, plain, (![A_328, D_329, B_330]: (r1_orders_2(A_328, D_329, k2_yellow_0(A_328, B_330)) | ~r1_lattice3(A_328, B_330, D_329) | ~m1_subset_1(D_329, u1_struct_0(A_328)) | ~r2_yellow_0(A_328, B_330) | ~l1_orders_2(A_328))), inference(resolution, [status(thm)], [c_20, c_581])).
% 3.27/1.61  tff(c_427, plain, (~r1_orders_2('#skF_4', k2_yellow_0('#skF_4', '#skF_6'), k2_yellow_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_606, plain, (~r1_lattice3('#skF_4', '#skF_5', k2_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k2_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~r2_yellow_0('#skF_4', '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_599, c_427])).
% 3.27/1.61  tff(c_610, plain, (~r1_lattice3('#skF_4', '#skF_5', k2_yellow_0('#skF_4', '#skF_6')) | ~m1_subset_1(k2_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~r2_yellow_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_606])).
% 3.27/1.61  tff(c_611, plain, (~r2_yellow_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_610])).
% 3.27/1.61  tff(c_615, plain, (~l1_orders_2('#skF_4') | ~v3_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_611])).
% 3.27/1.61  tff(c_618, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_615])).
% 3.27/1.61  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_618])).
% 3.27/1.61  tff(c_621, plain, (~m1_subset_1(k2_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_4', '#skF_5', k2_yellow_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_610])).
% 3.27/1.61  tff(c_623, plain, (~r1_lattice3('#skF_4', '#skF_5', k2_yellow_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_621])).
% 3.27/1.61  tff(c_626, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r2_yellow_0('#skF_4', '#skF_6') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_462, c_623])).
% 3.27/1.61  tff(c_629, plain, (~r2_yellow_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_626])).
% 3.27/1.61  tff(c_632, plain, (~l1_orders_2('#skF_4') | ~v3_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_629])).
% 3.27/1.61  tff(c_635, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_632])).
% 3.27/1.61  tff(c_637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_635])).
% 3.27/1.61  tff(c_638, plain, (~m1_subset_1(k2_yellow_0('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_621])).
% 3.27/1.61  tff(c_642, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_20, c_638])).
% 3.27/1.61  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_642])).
% 3.27/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.61  
% 3.27/1.61  Inference rules
% 3.27/1.61  ----------------------
% 3.27/1.61  #Ref     : 0
% 3.27/1.61  #Sup     : 107
% 3.27/1.61  #Fact    : 0
% 3.27/1.61  #Define  : 0
% 3.27/1.61  #Split   : 13
% 3.27/1.61  #Chain   : 0
% 3.27/1.61  #Close   : 0
% 3.27/1.61  
% 3.27/1.61  Ordering : KBO
% 3.27/1.61  
% 3.27/1.61  Simplification rules
% 3.27/1.61  ----------------------
% 3.27/1.61  #Subsume      : 27
% 3.27/1.61  #Demod        : 85
% 3.27/1.61  #Tautology    : 7
% 3.27/1.61  #SimpNegUnit  : 20
% 3.27/1.61  #BackRed      : 0
% 3.27/1.61  
% 3.27/1.61  #Partial instantiations: 0
% 3.27/1.61  #Strategies tried      : 1
% 3.27/1.61  
% 3.27/1.61  Timing (in seconds)
% 3.27/1.61  ----------------------
% 3.27/1.62  Preprocessing        : 0.36
% 3.27/1.62  Parsing              : 0.20
% 3.27/1.62  CNF conversion       : 0.03
% 3.27/1.62  Main loop            : 0.42
% 3.27/1.62  Inferencing          : 0.17
% 3.27/1.62  Reduction            : 0.11
% 3.27/1.62  Demodulation         : 0.07
% 3.27/1.62  BG Simplification    : 0.03
% 3.27/1.62  Subsumption          : 0.09
% 3.27/1.62  Abstraction          : 0.02
% 3.27/1.62  MUC search           : 0.00
% 3.27/1.62  Cooper               : 0.00
% 3.27/1.62  Total                : 0.82
% 3.27/1.62  Index Insertion      : 0.00
% 3.27/1.62  Index Deletion       : 0.00
% 3.27/1.62  Index Matching       : 0.00
% 3.27/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
