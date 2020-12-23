%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 556 expanded)
%              Number of leaves         :   29 ( 217 expanded)
%              Depth                    :   23
%              Number of atoms          :  289 (2499 expanded)
%              Number of equality atoms :   35 ( 231 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_168,negated_conjecture,(
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
               => k13_lattice3(A,k12_lattice3(A,B,C),C) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_52,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_59,plain,(
    ! [A_113,B_114] :
      ( r1_orders_2(A_113,B_114,B_114)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_66,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_61])).

tff(c_70,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_73])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k11_lattice3(A_6,B_7,C_8),u1_struct_0(A_6))
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_orders_2(A_126,k11_lattice3(A_126,B_127,C_128),C_128)
      | ~ m1_subset_1(k11_lattice3(A_126,B_127,C_128),u1_struct_0(A_126))
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v2_lattice3(A_126)
      | ~ v5_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_167,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_orders_2(A_6,k11_lattice3(A_6,B_7,C_8),C_8)
      | ~ v2_lattice3(A_6)
      | ~ v5_orders_2(A_6)
      | v2_struct_0(A_6)
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_88,plain,(
    ! [A_118,B_119,C_120] :
      ( k13_lattice3(A_118,B_119,C_120) = k10_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v1_lattice3(A_118)
      | ~ v5_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_92,plain,(
    ! [B_119] :
      ( k13_lattice3('#skF_3',B_119,'#skF_5') = k10_lattice3('#skF_3',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_102,plain,(
    ! [B_121] :
      ( k13_lattice3('#skF_3',B_121,'#skF_5') = k10_lattice3('#skF_3',B_121,'#skF_5')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_92])).

tff(c_106,plain,(
    ! [B_7,C_8] :
      ( k13_lattice3('#skF_3',k11_lattice3('#skF_3',B_7,C_8),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3',B_7,C_8),'#skF_5')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_415,plain,(
    ! [B_154,C_155] :
      ( k13_lattice3('#skF_3',k11_lattice3('#skF_3',B_154,C_155),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3',B_154,C_155),'#skF_5')
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_106])).

tff(c_428,plain,(
    ! [B_156] :
      ( k13_lattice3('#skF_3',k11_lattice3('#skF_3',B_156,'#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3',B_156,'#skF_5'),'#skF_5')
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_415])).

tff(c_443,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_428])).

tff(c_150,plain,(
    ! [A_123,B_124,C_125] :
      ( k12_lattice3(A_123,B_124,C_125) = k11_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_154,plain,(
    ! [B_124] :
      ( k12_lattice3('#skF_3',B_124,'#skF_5') = k11_lattice3('#skF_3',B_124,'#skF_5')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_168,plain,(
    ! [B_129] :
      ( k12_lattice3('#skF_3',B_129,'#skF_5') = k11_lattice3('#skF_3',B_129,'#skF_5')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_154])).

tff(c_183,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_168])).

tff(c_42,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_188,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_42])).

tff(c_448,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_188])).

tff(c_246,plain,(
    ! [A_134,B_135,C_136] :
      ( r1_orders_2(A_134,k11_lattice3(A_134,B_135,C_136),B_135)
      | ~ m1_subset_1(k11_lattice3(A_134,B_135,C_136),u1_struct_0(A_134))
      | ~ m1_subset_1(C_136,u1_struct_0(A_134))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v2_lattice3(A_134)
      | ~ v5_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_249,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_orders_2(A_6,k11_lattice3(A_6,B_7,C_8),B_7)
      | ~ v2_lattice3(A_6)
      | ~ v5_orders_2(A_6)
      | v2_struct_0(A_6)
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_246])).

tff(c_63,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_69,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_63])).

tff(c_87,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_69])).

tff(c_804,plain,(
    ! [A_223,C_224,B_225,D_226] :
      ( r1_orders_2(A_223,C_224,'#skF_1'(A_223,B_225,C_224,D_226))
      | k10_lattice3(A_223,B_225,C_224) = D_226
      | ~ r1_orders_2(A_223,C_224,D_226)
      | ~ r1_orders_2(A_223,B_225,D_226)
      | ~ m1_subset_1(D_226,u1_struct_0(A_223))
      | ~ m1_subset_1(C_224,u1_struct_0(A_223))
      | ~ m1_subset_1(B_225,u1_struct_0(A_223))
      | ~ l1_orders_2(A_223)
      | ~ v1_lattice3(A_223)
      | ~ v5_orders_2(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_9,D_51,B_33,C_45] :
      ( ~ r1_orders_2(A_9,D_51,'#skF_1'(A_9,B_33,C_45,D_51))
      | k10_lattice3(A_9,B_33,C_45) = D_51
      | ~ r1_orders_2(A_9,C_45,D_51)
      | ~ r1_orders_2(A_9,B_33,D_51)
      | ~ m1_subset_1(D_51,u1_struct_0(A_9))
      | ~ m1_subset_1(C_45,u1_struct_0(A_9))
      | ~ m1_subset_1(B_33,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1404,plain,(
    ! [A_253,B_254,D_255] :
      ( k10_lattice3(A_253,B_254,D_255) = D_255
      | ~ r1_orders_2(A_253,D_255,D_255)
      | ~ r1_orders_2(A_253,B_254,D_255)
      | ~ m1_subset_1(D_255,u1_struct_0(A_253))
      | ~ m1_subset_1(B_254,u1_struct_0(A_253))
      | ~ l1_orders_2(A_253)
      | ~ v1_lattice3(A_253)
      | ~ v5_orders_2(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_804,c_10])).

tff(c_1408,plain,(
    ! [B_254] :
      ( k10_lattice3('#skF_3',B_254,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3',B_254,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_87,c_1404])).

tff(c_1414,plain,(
    ! [B_254] :
      ( k10_lattice3('#skF_3',B_254,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3',B_254,'#skF_4')
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_1408])).

tff(c_1420,plain,(
    ! [B_256] :
      ( k10_lattice3('#skF_3',B_256,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3',B_256,'#skF_4')
      | ~ m1_subset_1(B_256,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1414])).

tff(c_1428,plain,(
    ! [B_7,C_8] :
      ( k10_lattice3('#skF_3',k11_lattice3('#skF_3',B_7,C_8),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3',B_7,C_8),'#skF_4')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_1420])).

tff(c_1694,plain,(
    ! [B_262,C_263] :
      ( k10_lattice3('#skF_3',k11_lattice3('#skF_3',B_262,C_263),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3',B_262,C_263),'#skF_4')
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1428])).

tff(c_1708,plain,(
    ! [C_8] :
      ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4',C_8),'#skF_4') = '#skF_4'
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_249,c_1694])).

tff(c_1719,plain,(
    ! [C_8] :
      ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4',C_8),'#skF_4') = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_50,c_1708])).

tff(c_1802,plain,(
    ! [C_267] :
      ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4',C_267),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1719])).

tff(c_1832,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1802])).

tff(c_22,plain,(
    ! [A_9,B_33,C_45] :
      ( r1_orders_2(A_9,B_33,k10_lattice3(A_9,B_33,C_45))
      | ~ m1_subset_1(k10_lattice3(A_9,B_33,C_45),u1_struct_0(A_9))
      | ~ m1_subset_1(C_45,u1_struct_0(A_9))
      | ~ m1_subset_1(B_33,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1840,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_22])).

tff(c_1847,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_46,c_1832,c_1840])).

tff(c_1848,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1847])).

tff(c_2119,plain,(
    ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1848])).

tff(c_2122,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2119])).

tff(c_2126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2122])).

tff(c_2128,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1848])).

tff(c_81,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1410,plain,(
    ! [B_254] :
      ( k10_lattice3('#skF_3',B_254,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_254,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_1404])).

tff(c_1418,plain,(
    ! [B_254] :
      ( k10_lattice3('#skF_3',B_254,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_254,'#skF_5')
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_44,c_1410])).

tff(c_1419,plain,(
    ! [B_254] :
      ( k10_lattice3('#skF_3',B_254,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_254,'#skF_5')
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1418])).

tff(c_2181,plain,
    ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2128,c_1419])).

tff(c_2271,plain,(
    ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_2181])).

tff(c_2319,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_2271])).

tff(c_2322,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_54,c_50,c_2319])).

tff(c_2324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:55:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.88  
% 4.92/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.88  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.92/1.88  
% 4.92/1.88  %Foreground sorts:
% 4.92/1.88  
% 4.92/1.88  
% 4.92/1.88  %Background operators:
% 4.92/1.88  
% 4.92/1.88  
% 4.92/1.88  %Foreground operators:
% 4.92/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.92/1.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.92/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.88  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 4.92/1.88  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.92/1.88  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 4.92/1.88  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.92/1.88  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 4.92/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.88  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.92/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.92/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.92/1.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.92/1.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.92/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.92/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.88  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.92/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.92/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.88  
% 4.92/1.90  tff(f_168, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 4.92/1.90  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 4.92/1.90  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.92/1.90  tff(f_59, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.92/1.90  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 4.92/1.90  tff(f_149, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 4.92/1.90  tff(f_137, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.92/1.90  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 4.92/1.90  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_52, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_56, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_59, plain, (![A_113, B_114]: (r1_orders_2(A_113, B_114, B_114) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.92/1.90  tff(c_61, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_59])).
% 4.92/1.90  tff(c_66, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_61])).
% 4.92/1.90  tff(c_70, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 4.92/1.90  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.92/1.90  tff(c_73, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4])).
% 4.92/1.90  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_73])).
% 4.92/1.90  tff(c_82, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 4.92/1.90  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_54, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_50, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k11_lattice3(A_6, B_7, C_8), u1_struct_0(A_6)) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.92/1.90  tff(c_164, plain, (![A_126, B_127, C_128]: (r1_orders_2(A_126, k11_lattice3(A_126, B_127, C_128), C_128) | ~m1_subset_1(k11_lattice3(A_126, B_127, C_128), u1_struct_0(A_126)) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v2_lattice3(A_126) | ~v5_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.92/1.90  tff(c_167, plain, (![A_6, B_7, C_8]: (r1_orders_2(A_6, k11_lattice3(A_6, B_7, C_8), C_8) | ~v2_lattice3(A_6) | ~v5_orders_2(A_6) | v2_struct_0(A_6) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(resolution, [status(thm)], [c_8, c_164])).
% 4.92/1.90  tff(c_88, plain, (![A_118, B_119, C_120]: (k13_lattice3(A_118, B_119, C_120)=k10_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v1_lattice3(A_118) | ~v5_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.92/1.90  tff(c_92, plain, (![B_119]: (k13_lattice3('#skF_3', B_119, '#skF_5')=k10_lattice3('#skF_3', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_88])).
% 4.92/1.90  tff(c_102, plain, (![B_121]: (k13_lattice3('#skF_3', B_121, '#skF_5')=k10_lattice3('#skF_3', B_121, '#skF_5') | ~m1_subset_1(B_121, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_92])).
% 4.92/1.90  tff(c_106, plain, (![B_7, C_8]: (k13_lattice3('#skF_3', k11_lattice3('#skF_3', B_7, C_8), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', B_7, C_8), '#skF_5') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')) | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_102])).
% 4.92/1.90  tff(c_415, plain, (![B_154, C_155]: (k13_lattice3('#skF_3', k11_lattice3('#skF_3', B_154, C_155), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', B_154, C_155), '#skF_5') | ~m1_subset_1(C_155, u1_struct_0('#skF_3')) | ~m1_subset_1(B_154, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_106])).
% 4.92/1.90  tff(c_428, plain, (![B_156]: (k13_lattice3('#skF_3', k11_lattice3('#skF_3', B_156, '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', B_156, '#skF_5'), '#skF_5') | ~m1_subset_1(B_156, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_415])).
% 4.92/1.90  tff(c_443, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_46, c_428])).
% 4.92/1.90  tff(c_150, plain, (![A_123, B_124, C_125]: (k12_lattice3(A_123, B_124, C_125)=k11_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.92/1.90  tff(c_154, plain, (![B_124]: (k12_lattice3('#skF_3', B_124, '#skF_5')=k11_lattice3('#skF_3', B_124, '#skF_5') | ~m1_subset_1(B_124, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_150])).
% 4.92/1.90  tff(c_168, plain, (![B_129]: (k12_lattice3('#skF_3', B_129, '#skF_5')=k11_lattice3('#skF_3', B_129, '#skF_5') | ~m1_subset_1(B_129, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_154])).
% 4.92/1.90  tff(c_183, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_168])).
% 4.92/1.90  tff(c_42, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.90  tff(c_188, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_42])).
% 4.92/1.90  tff(c_448, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_188])).
% 4.92/1.90  tff(c_246, plain, (![A_134, B_135, C_136]: (r1_orders_2(A_134, k11_lattice3(A_134, B_135, C_136), B_135) | ~m1_subset_1(k11_lattice3(A_134, B_135, C_136), u1_struct_0(A_134)) | ~m1_subset_1(C_136, u1_struct_0(A_134)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v2_lattice3(A_134) | ~v5_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.92/1.90  tff(c_249, plain, (![A_6, B_7, C_8]: (r1_orders_2(A_6, k11_lattice3(A_6, B_7, C_8), B_7) | ~v2_lattice3(A_6) | ~v5_orders_2(A_6) | v2_struct_0(A_6) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(resolution, [status(thm)], [c_8, c_246])).
% 4.92/1.90  tff(c_63, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_59])).
% 4.92/1.90  tff(c_69, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_63])).
% 4.92/1.90  tff(c_87, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_69])).
% 4.92/1.90  tff(c_804, plain, (![A_223, C_224, B_225, D_226]: (r1_orders_2(A_223, C_224, '#skF_1'(A_223, B_225, C_224, D_226)) | k10_lattice3(A_223, B_225, C_224)=D_226 | ~r1_orders_2(A_223, C_224, D_226) | ~r1_orders_2(A_223, B_225, D_226) | ~m1_subset_1(D_226, u1_struct_0(A_223)) | ~m1_subset_1(C_224, u1_struct_0(A_223)) | ~m1_subset_1(B_225, u1_struct_0(A_223)) | ~l1_orders_2(A_223) | ~v1_lattice3(A_223) | ~v5_orders_2(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.90  tff(c_10, plain, (![A_9, D_51, B_33, C_45]: (~r1_orders_2(A_9, D_51, '#skF_1'(A_9, B_33, C_45, D_51)) | k10_lattice3(A_9, B_33, C_45)=D_51 | ~r1_orders_2(A_9, C_45, D_51) | ~r1_orders_2(A_9, B_33, D_51) | ~m1_subset_1(D_51, u1_struct_0(A_9)) | ~m1_subset_1(C_45, u1_struct_0(A_9)) | ~m1_subset_1(B_33, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.90  tff(c_1404, plain, (![A_253, B_254, D_255]: (k10_lattice3(A_253, B_254, D_255)=D_255 | ~r1_orders_2(A_253, D_255, D_255) | ~r1_orders_2(A_253, B_254, D_255) | ~m1_subset_1(D_255, u1_struct_0(A_253)) | ~m1_subset_1(B_254, u1_struct_0(A_253)) | ~l1_orders_2(A_253) | ~v1_lattice3(A_253) | ~v5_orders_2(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_804, c_10])).
% 4.92/1.90  tff(c_1408, plain, (![B_254]: (k10_lattice3('#skF_3', B_254, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', B_254, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_254, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_1404])).
% 4.92/1.90  tff(c_1414, plain, (![B_254]: (k10_lattice3('#skF_3', B_254, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', B_254, '#skF_4') | ~m1_subset_1(B_254, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_46, c_1408])).
% 4.92/1.90  tff(c_1420, plain, (![B_256]: (k10_lattice3('#skF_3', B_256, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', B_256, '#skF_4') | ~m1_subset_1(B_256, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_1414])).
% 4.92/1.90  tff(c_1428, plain, (![B_7, C_8]: (k10_lattice3('#skF_3', k11_lattice3('#skF_3', B_7, C_8), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', B_7, C_8), '#skF_4') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')) | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1420])).
% 4.92/1.90  tff(c_1694, plain, (![B_262, C_263]: (k10_lattice3('#skF_3', k11_lattice3('#skF_3', B_262, C_263), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', B_262, C_263), '#skF_4') | ~m1_subset_1(C_263, u1_struct_0('#skF_3')) | ~m1_subset_1(B_262, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1428])).
% 4.92/1.90  tff(c_1708, plain, (![C_8]: (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', C_8), '#skF_4')='#skF_4' | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_249, c_1694])).
% 4.92/1.90  tff(c_1719, plain, (![C_8]: (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', C_8), '#skF_4')='#skF_4' | v2_struct_0('#skF_3') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_50, c_1708])).
% 4.92/1.90  tff(c_1802, plain, (![C_267]: (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', C_267), '#skF_4')='#skF_4' | ~m1_subset_1(C_267, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_1719])).
% 4.92/1.90  tff(c_1832, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1802])).
% 4.92/1.90  tff(c_22, plain, (![A_9, B_33, C_45]: (r1_orders_2(A_9, B_33, k10_lattice3(A_9, B_33, C_45)) | ~m1_subset_1(k10_lattice3(A_9, B_33, C_45), u1_struct_0(A_9)) | ~m1_subset_1(C_45, u1_struct_0(A_9)) | ~m1_subset_1(B_33, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.90  tff(c_1840, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1832, c_22])).
% 4.92/1.90  tff(c_1847, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_46, c_46, c_1832, c_1840])).
% 4.92/1.90  tff(c_1848, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_82, c_1847])).
% 4.92/1.90  tff(c_2119, plain, (~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1848])).
% 4.92/1.90  tff(c_2122, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_8, c_2119])).
% 4.92/1.90  tff(c_2126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2122])).
% 4.92/1.90  tff(c_2128, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1848])).
% 4.92/1.90  tff(c_81, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 4.92/1.90  tff(c_1410, plain, (![B_254]: (k10_lattice3('#skF_3', B_254, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_254, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_254, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_1404])).
% 4.92/1.90  tff(c_1418, plain, (![B_254]: (k10_lattice3('#skF_3', B_254, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_254, '#skF_5') | ~m1_subset_1(B_254, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_44, c_1410])).
% 4.92/1.90  tff(c_1419, plain, (![B_254]: (k10_lattice3('#skF_3', B_254, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_254, '#skF_5') | ~m1_subset_1(B_254, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_1418])).
% 4.92/1.90  tff(c_2181, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_2128, c_1419])).
% 4.92/1.90  tff(c_2271, plain, (~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_448, c_2181])).
% 4.92/1.90  tff(c_2319, plain, (~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_167, c_2271])).
% 4.92/1.90  tff(c_2322, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_54, c_50, c_2319])).
% 4.92/1.90  tff(c_2324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2322])).
% 4.92/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.90  
% 4.92/1.90  Inference rules
% 4.92/1.90  ----------------------
% 4.92/1.90  #Ref     : 0
% 4.92/1.90  #Sup     : 476
% 4.92/1.90  #Fact    : 0
% 4.92/1.90  #Define  : 0
% 4.92/1.90  #Split   : 5
% 4.92/1.90  #Chain   : 0
% 4.92/1.90  #Close   : 0
% 4.92/1.90  
% 4.92/1.90  Ordering : KBO
% 4.92/1.90  
% 4.92/1.90  Simplification rules
% 4.92/1.90  ----------------------
% 4.92/1.90  #Subsume      : 15
% 4.92/1.90  #Demod        : 778
% 4.92/1.90  #Tautology    : 199
% 4.92/1.90  #SimpNegUnit  : 111
% 4.92/1.90  #BackRed      : 20
% 4.92/1.90  
% 4.92/1.90  #Partial instantiations: 0
% 4.92/1.90  #Strategies tried      : 1
% 4.92/1.90  
% 4.92/1.90  Timing (in seconds)
% 4.92/1.90  ----------------------
% 4.92/1.91  Preprocessing        : 0.36
% 4.92/1.91  Parsing              : 0.19
% 4.92/1.91  CNF conversion       : 0.03
% 4.92/1.91  Main loop            : 0.77
% 4.92/1.91  Inferencing          : 0.25
% 4.92/1.91  Reduction            : 0.26
% 4.92/1.91  Demodulation         : 0.19
% 4.92/1.91  BG Simplification    : 0.04
% 4.92/1.91  Subsumption          : 0.17
% 4.92/1.91  Abstraction          : 0.05
% 4.92/1.91  MUC search           : 0.00
% 4.92/1.91  Cooper               : 0.00
% 4.92/1.91  Total                : 1.17
% 4.92/1.91  Index Insertion      : 0.00
% 4.92/1.91  Index Deletion       : 0.00
% 4.92/1.91  Index Matching       : 0.00
% 4.92/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
