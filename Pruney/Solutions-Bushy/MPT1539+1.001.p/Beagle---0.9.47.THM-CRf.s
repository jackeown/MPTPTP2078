%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1539+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:01 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 142 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  395 ( 661 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v3_lattice3 > v2_struct_0 > l1_orders_2 > a_2_0_yellow_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_13 > #skF_5 > #skF_10 > #skF_8 > #skF_7 > #skF_9 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(a_2_0_yellow_0,type,(
    a_2_0_yellow_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_orders_2(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( r1_yellow_0(A,B)
            & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r2_lattice3(A,B,C)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_55,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v5_orders_2(B)
        & v3_lattice3(B)
        & l1_orders_2(B) )
     => ( r2_hidden(A,a_2_0_yellow_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r1_lattice3(B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_0)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_0)).

tff(c_64,plain,(
    l1_orders_2('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    v3_lattice3('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_68,plain,(
    v5_orders_2('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_1,B_16] :
      ( m1_subset_1('#skF_1'(A_1,B_16),u1_struct_0(A_1))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_1,B_16] :
      ( r2_lattice3(A_1,B_16,'#skF_1'(A_1,B_16))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_57,B_71,C_78] :
      ( m1_subset_1('#skF_7'(A_57,B_71,C_78),u1_struct_0(A_57))
      | r1_yellow_0(A_57,B_71)
      | ~ r2_lattice3(A_57,B_71,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [A_57,B_71,C_78] :
      ( r2_lattice3(A_57,B_71,'#skF_7'(A_57,B_71,C_78))
      | r1_yellow_0(A_57,B_71)
      | ~ r2_lattice3(A_57,B_71,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [A_1,B_16,D_21] :
      ( r1_orders_2(A_1,'#skF_1'(A_1,B_16),D_21)
      | ~ r2_lattice3(A_1,B_16,D_21)
      | ~ m1_subset_1(D_21,u1_struct_0(A_1))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2994,plain,(
    ! [A_915,C_916,B_917] :
      ( ~ r1_orders_2(A_915,C_916,'#skF_7'(A_915,B_917,C_916))
      | r1_yellow_0(A_915,B_917)
      | ~ r2_lattice3(A_915,B_917,C_916)
      | ~ m1_subset_1(C_916,u1_struct_0(A_915))
      | ~ l1_orders_2(A_915)
      | ~ v5_orders_2(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3438,plain,(
    ! [A_1030,B_1031,B_1032] :
      ( r1_yellow_0(A_1030,B_1031)
      | ~ r2_lattice3(A_1030,B_1031,'#skF_1'(A_1030,B_1032))
      | ~ m1_subset_1('#skF_1'(A_1030,B_1032),u1_struct_0(A_1030))
      | ~ v5_orders_2(A_1030)
      | ~ r2_lattice3(A_1030,B_1032,'#skF_7'(A_1030,B_1031,'#skF_1'(A_1030,B_1032)))
      | ~ m1_subset_1('#skF_7'(A_1030,B_1031,'#skF_1'(A_1030,B_1032)),u1_struct_0(A_1030))
      | ~ v3_lattice3(A_1030)
      | ~ l1_orders_2(A_1030) ) ),
    inference(resolution,[status(thm)],[c_8,c_2994])).

tff(c_3443,plain,(
    ! [A_1033,B_1034] :
      ( ~ m1_subset_1('#skF_7'(A_1033,B_1034,'#skF_1'(A_1033,B_1034)),u1_struct_0(A_1033))
      | ~ v3_lattice3(A_1033)
      | r1_yellow_0(A_1033,B_1034)
      | ~ r2_lattice3(A_1033,B_1034,'#skF_1'(A_1033,B_1034))
      | ~ m1_subset_1('#skF_1'(A_1033,B_1034),u1_struct_0(A_1033))
      | ~ l1_orders_2(A_1033)
      | ~ v5_orders_2(A_1033) ) ),
    inference(resolution,[status(thm)],[c_46,c_3438])).

tff(c_3449,plain,(
    ! [A_1035,B_1036] :
      ( ~ v3_lattice3(A_1035)
      | r1_yellow_0(A_1035,B_1036)
      | ~ r2_lattice3(A_1035,B_1036,'#skF_1'(A_1035,B_1036))
      | ~ m1_subset_1('#skF_1'(A_1035,B_1036),u1_struct_0(A_1035))
      | ~ l1_orders_2(A_1035)
      | ~ v5_orders_2(A_1035) ) ),
    inference(resolution,[status(thm)],[c_48,c_3443])).

tff(c_3453,plain,(
    ! [A_1037,B_1038] :
      ( r1_yellow_0(A_1037,B_1038)
      | ~ m1_subset_1('#skF_1'(A_1037,B_1038),u1_struct_0(A_1037))
      | ~ v5_orders_2(A_1037)
      | ~ v3_lattice3(A_1037)
      | ~ l1_orders_2(A_1037) ) ),
    inference(resolution,[status(thm)],[c_10,c_3449])).

tff(c_3458,plain,(
    ! [A_1039,B_1040] :
      ( r1_yellow_0(A_1039,B_1040)
      | ~ v5_orders_2(A_1039)
      | ~ v3_lattice3(A_1039)
      | ~ l1_orders_2(A_1039) ) ),
    inference(resolution,[status(thm)],[c_12,c_3453])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20,plain,(
    ! [A_27,B_34,C_35] :
      ( m1_subset_1('#skF_4'(A_27,B_34,C_35),u1_struct_0(A_27))
      | r1_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_39,B_46,C_47] :
      ( r2_hidden('#skF_5'(A_39,B_46,C_47),B_46)
      | r2_lattice3(A_39,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_141,B_142,C_143] :
      ( '#skF_6'(A_141,B_142,C_143) = A_141
      | ~ r2_hidden(A_141,a_2_0_yellow_0(B_142,C_143))
      | ~ l1_orders_2(B_142)
      | ~ v3_lattice3(B_142)
      | ~ v5_orders_2(B_142)
      | v2_struct_0(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_375,plain,(
    ! [A_255,B_256,C_257,C_258] :
      ( '#skF_6'('#skF_5'(A_255,a_2_0_yellow_0(B_256,C_257),C_258),B_256,C_257) = '#skF_5'(A_255,a_2_0_yellow_0(B_256,C_257),C_258)
      | ~ l1_orders_2(B_256)
      | ~ v3_lattice3(B_256)
      | ~ v5_orders_2(B_256)
      | v2_struct_0(B_256)
      | r2_lattice3(A_255,a_2_0_yellow_0(B_256,C_257),C_258)
      | ~ m1_subset_1(C_258,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255) ) ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_36,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1('#skF_6'(A_51,B_52,C_53),u1_struct_0(B_52))
      | ~ r2_hidden(A_51,a_2_0_yellow_0(B_52,C_53))
      | ~ l1_orders_2(B_52)
      | ~ v3_lattice3(B_52)
      | ~ v5_orders_2(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1113,plain,(
    ! [A_430,B_431,C_432,C_433] :
      ( m1_subset_1('#skF_5'(A_430,a_2_0_yellow_0(B_431,C_432),C_433),u1_struct_0(B_431))
      | ~ r2_hidden('#skF_5'(A_430,a_2_0_yellow_0(B_431,C_432),C_433),a_2_0_yellow_0(B_431,C_432))
      | ~ l1_orders_2(B_431)
      | ~ v3_lattice3(B_431)
      | ~ v5_orders_2(B_431)
      | v2_struct_0(B_431)
      | ~ l1_orders_2(B_431)
      | ~ v3_lattice3(B_431)
      | ~ v5_orders_2(B_431)
      | v2_struct_0(B_431)
      | r2_lattice3(A_430,a_2_0_yellow_0(B_431,C_432),C_433)
      | ~ m1_subset_1(C_433,u1_struct_0(A_430))
      | ~ l1_orders_2(A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_36])).

tff(c_1123,plain,(
    ! [A_39,B_431,C_432,C_47] :
      ( m1_subset_1('#skF_5'(A_39,a_2_0_yellow_0(B_431,C_432),C_47),u1_struct_0(B_431))
      | ~ l1_orders_2(B_431)
      | ~ v3_lattice3(B_431)
      | ~ v5_orders_2(B_431)
      | v2_struct_0(B_431)
      | r2_lattice3(A_39,a_2_0_yellow_0(B_431,C_432),C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_26,c_1113])).

tff(c_32,plain,(
    ! [B_52,C_53,A_51] :
      ( r1_lattice3(B_52,C_53,'#skF_6'(A_51,B_52,C_53))
      | ~ r2_hidden(A_51,a_2_0_yellow_0(B_52,C_53))
      | ~ l1_orders_2(B_52)
      | ~ v3_lattice3(B_52)
      | ~ v5_orders_2(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1215,plain,(
    ! [B_466,C_467,A_468,C_469] :
      ( r1_lattice3(B_466,C_467,'#skF_5'(A_468,a_2_0_yellow_0(B_466,C_467),C_469))
      | ~ r2_hidden('#skF_5'(A_468,a_2_0_yellow_0(B_466,C_467),C_469),a_2_0_yellow_0(B_466,C_467))
      | ~ l1_orders_2(B_466)
      | ~ v3_lattice3(B_466)
      | ~ v5_orders_2(B_466)
      | v2_struct_0(B_466)
      | ~ l1_orders_2(B_466)
      | ~ v3_lattice3(B_466)
      | ~ v5_orders_2(B_466)
      | v2_struct_0(B_466)
      | r2_lattice3(A_468,a_2_0_yellow_0(B_466,C_467),C_469)
      | ~ m1_subset_1(C_469,u1_struct_0(A_468))
      | ~ l1_orders_2(A_468) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_32])).

tff(c_1226,plain,(
    ! [B_470,C_471,A_472,C_473] :
      ( r1_lattice3(B_470,C_471,'#skF_5'(A_472,a_2_0_yellow_0(B_470,C_471),C_473))
      | ~ l1_orders_2(B_470)
      | ~ v3_lattice3(B_470)
      | ~ v5_orders_2(B_470)
      | v2_struct_0(B_470)
      | r2_lattice3(A_472,a_2_0_yellow_0(B_470,C_471),C_473)
      | ~ m1_subset_1(C_473,u1_struct_0(A_472))
      | ~ l1_orders_2(A_472) ) ),
    inference(resolution,[status(thm)],[c_26,c_1215])).

tff(c_18,plain,(
    ! [A_27,B_34,C_35] :
      ( r2_hidden('#skF_4'(A_27,B_34,C_35),B_34)
      | r1_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_160,C_161,D_162,B_163] :
      ( r1_orders_2(A_160,C_161,D_162)
      | ~ r2_hidden(D_162,B_163)
      | ~ m1_subset_1(D_162,u1_struct_0(A_160))
      | ~ r1_lattice3(A_160,B_163,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_160))
      | ~ l1_orders_2(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_315,plain,(
    ! [C_226,A_228,C_225,A_229,B_227] :
      ( r1_orders_2(A_228,C_226,'#skF_4'(A_229,B_227,C_225))
      | ~ m1_subset_1('#skF_4'(A_229,B_227,C_225),u1_struct_0(A_228))
      | ~ r1_lattice3(A_228,B_227,C_226)
      | ~ m1_subset_1(C_226,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228)
      | r1_lattice3(A_229,B_227,C_225)
      | ~ m1_subset_1(C_225,u1_struct_0(A_229))
      | ~ l1_orders_2(A_229) ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_319,plain,(
    ! [A_230,C_231,B_232,C_233] :
      ( r1_orders_2(A_230,C_231,'#skF_4'(A_230,B_232,C_233))
      | ~ r1_lattice3(A_230,B_232,C_231)
      | ~ m1_subset_1(C_231,u1_struct_0(A_230))
      | r1_lattice3(A_230,B_232,C_233)
      | ~ m1_subset_1(C_233,u1_struct_0(A_230))
      | ~ l1_orders_2(A_230) ) ),
    inference(resolution,[status(thm)],[c_20,c_315])).

tff(c_24,plain,(
    ! [A_39,B_46,C_47] :
      ( ~ r1_orders_2(A_39,'#skF_5'(A_39,B_46,C_47),C_47)
      | r2_lattice3(A_39,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_333,plain,(
    ! [A_230,B_46,B_232,C_233] :
      ( r2_lattice3(A_230,B_46,'#skF_4'(A_230,B_232,C_233))
      | ~ m1_subset_1('#skF_4'(A_230,B_232,C_233),u1_struct_0(A_230))
      | ~ r1_lattice3(A_230,B_232,'#skF_5'(A_230,B_46,'#skF_4'(A_230,B_232,C_233)))
      | ~ m1_subset_1('#skF_5'(A_230,B_46,'#skF_4'(A_230,B_232,C_233)),u1_struct_0(A_230))
      | r1_lattice3(A_230,B_232,C_233)
      | ~ m1_subset_1(C_233,u1_struct_0(A_230))
      | ~ l1_orders_2(A_230) ) ),
    inference(resolution,[status(thm)],[c_319,c_24])).

tff(c_1282,plain,(
    ! [A_482,C_483,C_484] :
      ( ~ m1_subset_1('#skF_5'(A_482,a_2_0_yellow_0(A_482,C_483),'#skF_4'(A_482,C_483,C_484)),u1_struct_0(A_482))
      | r1_lattice3(A_482,C_483,C_484)
      | ~ m1_subset_1(C_484,u1_struct_0(A_482))
      | ~ v3_lattice3(A_482)
      | ~ v5_orders_2(A_482)
      | v2_struct_0(A_482)
      | r2_lattice3(A_482,a_2_0_yellow_0(A_482,C_483),'#skF_4'(A_482,C_483,C_484))
      | ~ m1_subset_1('#skF_4'(A_482,C_483,C_484),u1_struct_0(A_482))
      | ~ l1_orders_2(A_482) ) ),
    inference(resolution,[status(thm)],[c_1226,c_333])).

tff(c_1293,plain,(
    ! [B_485,C_486,C_487] :
      ( r1_lattice3(B_485,C_486,C_487)
      | ~ m1_subset_1(C_487,u1_struct_0(B_485))
      | ~ v3_lattice3(B_485)
      | ~ v5_orders_2(B_485)
      | v2_struct_0(B_485)
      | r2_lattice3(B_485,a_2_0_yellow_0(B_485,C_486),'#skF_4'(B_485,C_486,C_487))
      | ~ m1_subset_1('#skF_4'(B_485,C_486,C_487),u1_struct_0(B_485))
      | ~ l1_orders_2(B_485) ) ),
    inference(resolution,[status(thm)],[c_1123,c_1282])).

tff(c_84,plain,(
    ! [A_138,B_139,D_140] :
      ( r1_orders_2(A_138,'#skF_1'(A_138,B_139),D_140)
      | ~ r2_lattice3(A_138,B_139,D_140)
      | ~ m1_subset_1(D_140,u1_struct_0(A_138))
      | ~ v3_lattice3(A_138)
      | ~ l1_orders_2(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_27,C_35,B_34] :
      ( ~ r1_orders_2(A_27,C_35,'#skF_4'(A_27,B_34,C_35))
      | r1_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [A_138,B_34,B_139] :
      ( r1_lattice3(A_138,B_34,'#skF_1'(A_138,B_139))
      | ~ m1_subset_1('#skF_1'(A_138,B_139),u1_struct_0(A_138))
      | ~ r2_lattice3(A_138,B_139,'#skF_4'(A_138,B_34,'#skF_1'(A_138,B_139)))
      | ~ m1_subset_1('#skF_4'(A_138,B_34,'#skF_1'(A_138,B_139)),u1_struct_0(A_138))
      | ~ v3_lattice3(A_138)
      | ~ l1_orders_2(A_138) ) ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_1346,plain,(
    ! [B_496,C_497] :
      ( r1_lattice3(B_496,C_497,'#skF_1'(B_496,a_2_0_yellow_0(B_496,C_497)))
      | ~ m1_subset_1('#skF_1'(B_496,a_2_0_yellow_0(B_496,C_497)),u1_struct_0(B_496))
      | ~ v3_lattice3(B_496)
      | ~ v5_orders_2(B_496)
      | v2_struct_0(B_496)
      | ~ m1_subset_1('#skF_4'(B_496,C_497,'#skF_1'(B_496,a_2_0_yellow_0(B_496,C_497))),u1_struct_0(B_496))
      | ~ l1_orders_2(B_496) ) ),
    inference(resolution,[status(thm)],[c_1293,c_89])).

tff(c_1357,plain,(
    ! [A_498,B_499] :
      ( ~ v3_lattice3(A_498)
      | ~ v5_orders_2(A_498)
      | v2_struct_0(A_498)
      | r1_lattice3(A_498,B_499,'#skF_1'(A_498,a_2_0_yellow_0(A_498,B_499)))
      | ~ m1_subset_1('#skF_1'(A_498,a_2_0_yellow_0(A_498,B_499)),u1_struct_0(A_498))
      | ~ l1_orders_2(A_498) ) ),
    inference(resolution,[status(thm)],[c_20,c_1346])).

tff(c_1361,plain,(
    ! [A_1,B_499] :
      ( ~ v5_orders_2(A_1)
      | v2_struct_0(A_1)
      | r1_lattice3(A_1,B_499,'#skF_1'(A_1,a_2_0_yellow_0(A_1,B_499)))
      | ~ v3_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_1357])).

tff(c_60,plain,(
    ! [A_82,B_96,C_103] :
      ( m1_subset_1('#skF_9'(A_82,B_96,C_103),u1_struct_0(A_82))
      | r2_yellow_0(A_82,B_96)
      | ~ r1_lattice3(A_82,B_96,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ! [A_82,B_96,C_103] :
      ( r1_lattice3(A_82,B_96,'#skF_9'(A_82,B_96,C_103))
      | r2_yellow_0(A_82,B_96)
      | ~ r1_lattice3(A_82,B_96,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_124,plain,(
    ! [D_164,B_165,C_166] :
      ( r2_hidden(D_164,a_2_0_yellow_0(B_165,C_166))
      | ~ r1_lattice3(B_165,C_166,D_164)
      | ~ m1_subset_1(D_164,u1_struct_0(B_165))
      | ~ l1_orders_2(B_165)
      | ~ v3_lattice3(B_165)
      | ~ v5_orders_2(B_165)
      | v2_struct_0(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_39,D_50,C_47,B_46] :
      ( r1_orders_2(A_39,D_50,C_47)
      | ~ r2_hidden(D_50,B_46)
      | ~ m1_subset_1(D_50,u1_struct_0(A_39))
      | ~ r2_lattice3(A_39,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_405,plain,(
    ! [A_263,D_264,C_266,C_267,B_265] :
      ( r1_orders_2(A_263,D_264,C_266)
      | ~ m1_subset_1(D_264,u1_struct_0(A_263))
      | ~ r2_lattice3(A_263,a_2_0_yellow_0(B_265,C_267),C_266)
      | ~ m1_subset_1(C_266,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263)
      | ~ r1_lattice3(B_265,C_267,D_264)
      | ~ m1_subset_1(D_264,u1_struct_0(B_265))
      | ~ l1_orders_2(B_265)
      | ~ v3_lattice3(B_265)
      | ~ v5_orders_2(B_265)
      | v2_struct_0(B_265) ) ),
    inference(resolution,[status(thm)],[c_124,c_22])).

tff(c_2371,plain,(
    ! [C_727,C_730,B_728,C_732,A_731,B_729] :
      ( r1_orders_2(A_731,'#skF_9'(A_731,B_729,C_732),C_727)
      | ~ r2_lattice3(A_731,a_2_0_yellow_0(B_728,C_730),C_727)
      | ~ m1_subset_1(C_727,u1_struct_0(A_731))
      | ~ r1_lattice3(B_728,C_730,'#skF_9'(A_731,B_729,C_732))
      | ~ m1_subset_1('#skF_9'(A_731,B_729,C_732),u1_struct_0(B_728))
      | ~ l1_orders_2(B_728)
      | ~ v3_lattice3(B_728)
      | ~ v5_orders_2(B_728)
      | v2_struct_0(B_728)
      | r2_yellow_0(A_731,B_729)
      | ~ r1_lattice3(A_731,B_729,C_732)
      | ~ m1_subset_1(C_732,u1_struct_0(A_731))
      | ~ l1_orders_2(A_731)
      | ~ v5_orders_2(A_731) ) ),
    inference(resolution,[status(thm)],[c_60,c_405])).

tff(c_2826,plain,(
    ! [B_820,B_818,C_817,A_821,C_819] :
      ( r1_orders_2(A_821,'#skF_9'(A_821,B_820,C_819),'#skF_1'(A_821,a_2_0_yellow_0(B_818,C_817)))
      | ~ m1_subset_1('#skF_1'(A_821,a_2_0_yellow_0(B_818,C_817)),u1_struct_0(A_821))
      | ~ r1_lattice3(B_818,C_817,'#skF_9'(A_821,B_820,C_819))
      | ~ m1_subset_1('#skF_9'(A_821,B_820,C_819),u1_struct_0(B_818))
      | ~ l1_orders_2(B_818)
      | ~ v3_lattice3(B_818)
      | ~ v5_orders_2(B_818)
      | v2_struct_0(B_818)
      | r2_yellow_0(A_821,B_820)
      | ~ r1_lattice3(A_821,B_820,C_819)
      | ~ m1_subset_1(C_819,u1_struct_0(A_821))
      | ~ v5_orders_2(A_821)
      | ~ v3_lattice3(A_821)
      | ~ l1_orders_2(A_821) ) ),
    inference(resolution,[status(thm)],[c_10,c_2371])).

tff(c_56,plain,(
    ! [A_82,B_96,C_103] :
      ( ~ r1_orders_2(A_82,'#skF_9'(A_82,B_96,C_103),C_103)
      | r2_yellow_0(A_82,B_96)
      | ~ r1_lattice3(A_82,B_96,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2832,plain,(
    ! [B_822,C_823,A_824,B_825] :
      ( ~ r1_lattice3(B_822,C_823,'#skF_9'(A_824,B_825,'#skF_1'(A_824,a_2_0_yellow_0(B_822,C_823))))
      | ~ m1_subset_1('#skF_9'(A_824,B_825,'#skF_1'(A_824,a_2_0_yellow_0(B_822,C_823))),u1_struct_0(B_822))
      | ~ l1_orders_2(B_822)
      | ~ v3_lattice3(B_822)
      | ~ v5_orders_2(B_822)
      | v2_struct_0(B_822)
      | r2_yellow_0(A_824,B_825)
      | ~ r1_lattice3(A_824,B_825,'#skF_1'(A_824,a_2_0_yellow_0(B_822,C_823)))
      | ~ m1_subset_1('#skF_1'(A_824,a_2_0_yellow_0(B_822,C_823)),u1_struct_0(A_824))
      | ~ v5_orders_2(A_824)
      | ~ v3_lattice3(A_824)
      | ~ l1_orders_2(A_824) ) ),
    inference(resolution,[status(thm)],[c_2826,c_56])).

tff(c_2837,plain,(
    ! [A_826,B_827] :
      ( ~ m1_subset_1('#skF_9'(A_826,B_827,'#skF_1'(A_826,a_2_0_yellow_0(A_826,B_827))),u1_struct_0(A_826))
      | v2_struct_0(A_826)
      | ~ v3_lattice3(A_826)
      | r2_yellow_0(A_826,B_827)
      | ~ r1_lattice3(A_826,B_827,'#skF_1'(A_826,a_2_0_yellow_0(A_826,B_827)))
      | ~ m1_subset_1('#skF_1'(A_826,a_2_0_yellow_0(A_826,B_827)),u1_struct_0(A_826))
      | ~ l1_orders_2(A_826)
      | ~ v5_orders_2(A_826) ) ),
    inference(resolution,[status(thm)],[c_58,c_2832])).

tff(c_2843,plain,(
    ! [A_828,B_829] :
      ( v2_struct_0(A_828)
      | ~ v3_lattice3(A_828)
      | r2_yellow_0(A_828,B_829)
      | ~ r1_lattice3(A_828,B_829,'#skF_1'(A_828,a_2_0_yellow_0(A_828,B_829)))
      | ~ m1_subset_1('#skF_1'(A_828,a_2_0_yellow_0(A_828,B_829)),u1_struct_0(A_828))
      | ~ l1_orders_2(A_828)
      | ~ v5_orders_2(A_828) ) ),
    inference(resolution,[status(thm)],[c_60,c_2837])).

tff(c_2880,plain,(
    ! [A_834,B_835] :
      ( r2_yellow_0(A_834,B_835)
      | ~ m1_subset_1('#skF_1'(A_834,a_2_0_yellow_0(A_834,B_835)),u1_struct_0(A_834))
      | ~ v5_orders_2(A_834)
      | v2_struct_0(A_834)
      | ~ v3_lattice3(A_834)
      | ~ l1_orders_2(A_834) ) ),
    inference(resolution,[status(thm)],[c_1361,c_2843])).

tff(c_2886,plain,(
    ! [A_836,B_837] :
      ( r2_yellow_0(A_836,B_837)
      | ~ v5_orders_2(A_836)
      | v2_struct_0(A_836)
      | ~ v3_lattice3(A_836)
      | ~ l1_orders_2(A_836) ) ),
    inference(resolution,[status(thm)],[c_12,c_2880])).

tff(c_62,plain,
    ( ~ r1_yellow_0('#skF_11','#skF_13')
    | ~ r2_yellow_0('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_71,plain,(
    ~ r2_yellow_0('#skF_11','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2889,plain,
    ( ~ v5_orders_2('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ v3_lattice3('#skF_11')
    | ~ l1_orders_2('#skF_11') ),
    inference(resolution,[status(thm)],[c_2886,c_71])).

tff(c_2892,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_68,c_2889])).

tff(c_2894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2892])).

tff(c_2895,plain,(
    ~ r1_yellow_0('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3461,plain,
    ( ~ v5_orders_2('#skF_11')
    | ~ v3_lattice3('#skF_11')
    | ~ l1_orders_2('#skF_11') ),
    inference(resolution,[status(thm)],[c_3458,c_2895])).

tff(c_3465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_68,c_3461])).

%------------------------------------------------------------------------------
