%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1527+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:00 EST 2020

% Result     : Timeout 57.97s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  159 ( 473 expanded)
%              Number of leaves         :   28 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  505 (2181 expanded)
%              Number of equality atoms :    1 (  11 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( ( r2_lattice3(A,B,C)
               => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
              & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
               => r2_lattice3(A,B,C) )
              & ( r1_lattice3(A,B,C)
               => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
              & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
               => r1_lattice3(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

tff(f_47,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_61,axiom,(
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

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_103,plain,(
    ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_24,plain,(
    ! [A_7,B_14,C_15] :
      ( r2_hidden('#skF_3'(A_7,B_14,C_15),B_14)
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_3'(A_7,B_14,C_15),u1_struct_0(A_7))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r1_lattice3('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_202,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_78])).

tff(c_203,plain,(
    r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_309,plain,(
    ! [A_114,C_115,D_116,B_117] :
      ( r1_orders_2(A_114,C_115,D_116)
      | ~ r2_hidden(D_116,B_117)
      | ~ m1_subset_1(D_116,u1_struct_0(A_114))
      | ~ r1_lattice3(A_114,B_117,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2357,plain,(
    ! [A_318,B_317,D_316,A_320,C_319] :
      ( r1_orders_2(A_318,C_319,D_316)
      | ~ m1_subset_1(D_316,u1_struct_0(A_318))
      | ~ r1_lattice3(A_318,k3_xboole_0(A_320,B_317),C_319)
      | ~ m1_subset_1(C_319,u1_struct_0(A_318))
      | ~ l1_orders_2(A_318)
      | ~ r2_hidden(D_316,B_317)
      | ~ r2_hidden(D_316,A_320) ) ),
    inference(resolution,[status(thm)],[c_2,c_309])).

tff(c_30192,plain,(
    ! [A_1488,B_1485,C_1486,A_1484,C_1487,B_1483] :
      ( r1_orders_2(A_1484,C_1486,'#skF_3'(A_1484,B_1483,C_1487))
      | ~ r1_lattice3(A_1484,k3_xboole_0(A_1488,B_1485),C_1486)
      | ~ m1_subset_1(C_1486,u1_struct_0(A_1484))
      | ~ r2_hidden('#skF_3'(A_1484,B_1483,C_1487),B_1485)
      | ~ r2_hidden('#skF_3'(A_1484,B_1483,C_1487),A_1488)
      | r1_lattice3(A_1484,B_1483,C_1487)
      | ~ m1_subset_1(C_1487,u1_struct_0(A_1484))
      | ~ l1_orders_2(A_1484) ) ),
    inference(resolution,[status(thm)],[c_26,c_2357])).

tff(c_30200,plain,(
    ! [B_1483,C_1487] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_1483,C_1487))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1483,C_1487),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1483,C_1487),'#skF_6')
      | r1_lattice3('#skF_5',B_1483,C_1487)
      | ~ m1_subset_1(C_1487,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_203,c_30192])).

tff(c_30204,plain,(
    ! [B_1489,C_1490] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_1489,C_1490))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1489,C_1490),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1489,C_1490),'#skF_6')
      | r1_lattice3('#skF_5',B_1489,C_1490)
      | ~ m1_subset_1(C_1490,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_30200])).

tff(c_30313,plain,(
    ! [B_1489,C_1490] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_1489,C_1490))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1489,C_1490),'#skF_6')
      | r1_lattice3('#skF_5',B_1489,C_1490)
      | ~ m1_subset_1(C_1490,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_1489,C_1490),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_30204])).

tff(c_30336,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_30313])).

tff(c_38,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30339,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30336,c_38])).

tff(c_30342,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_30339])).

tff(c_30345,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_30342])).

tff(c_30349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30345])).

tff(c_30359,plain,(
    ! [B_1505,C_1506] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_1505,C_1506))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1505,C_1506),'#skF_6')
      | r1_lattice3('#skF_5',B_1505,C_1506)
      | ~ m1_subset_1(C_1506,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_1505,C_1506),u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_30313])).

tff(c_30363,plain,(
    ! [B_14,C_15] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_14,C_15))
      | ~ r2_hidden('#skF_3'('#skF_5',B_14,C_15),'#skF_6')
      | r1_lattice3('#skF_5',B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_30359])).

tff(c_30376,plain,(
    ! [B_1509,C_1510] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',B_1509,C_1510))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1509,C_1510),'#skF_6')
      | r1_lattice3('#skF_5',B_1509,C_1510)
      | ~ m1_subset_1(C_1510,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30363])).

tff(c_22,plain,(
    ! [A_7,C_15,B_14] :
      ( ~ r1_orders_2(A_7,C_15,'#skF_3'(A_7,B_14,C_15))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30380,plain,(
    ! [B_1509] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5',B_1509,'#skF_7'),'#skF_6')
      | r1_lattice3('#skF_5',B_1509,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30376,c_22])).

tff(c_30384,plain,(
    ! [B_1511] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_1511,'#skF_7'),'#skF_6')
      | r1_lattice3('#skF_5',B_1511,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_30380])).

tff(c_30444,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_30384])).

tff(c_30492,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_30444])).

tff(c_30494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_30492])).

tff(c_30495,plain,
    ( r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_30508,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30495])).

tff(c_34,plain,(
    ! [A_19,B_26,C_27] :
      ( m1_subset_1('#skF_4'(A_19,B_26,C_27),u1_struct_0(A_19))
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_4'(A_65,B_66,C_67),B_66)
      | r2_lattice3(A_65,B_66,C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    ! [A_65,A_1,B_2,C_67] :
      ( r2_hidden('#skF_4'(A_65,k3_xboole_0(A_1,B_2),C_67),A_1)
      | r2_lattice3(A_65,k3_xboole_0(A_1,B_2),C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65) ) ),
    inference(resolution,[status(thm)],[c_159,c_6])).

tff(c_30675,plain,(
    ! [A_1561,D_1562,C_1563,B_1564] :
      ( r1_orders_2(A_1561,D_1562,C_1563)
      | ~ r2_hidden(D_1562,B_1564)
      | ~ m1_subset_1(D_1562,u1_struct_0(A_1561))
      | ~ r2_lattice3(A_1561,B_1564,C_1563)
      | ~ m1_subset_1(C_1563,u1_struct_0(A_1561))
      | ~ l1_orders_2(A_1561) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67653,plain,(
    ! [A_3151,B_3152,A_3149,A_3153,C_3150,C_3154] :
      ( r1_orders_2(A_3149,'#skF_4'(A_3151,k3_xboole_0(A_3153,B_3152),C_3150),C_3154)
      | ~ m1_subset_1('#skF_4'(A_3151,k3_xboole_0(A_3153,B_3152),C_3150),u1_struct_0(A_3149))
      | ~ r2_lattice3(A_3149,A_3153,C_3154)
      | ~ m1_subset_1(C_3154,u1_struct_0(A_3149))
      | ~ l1_orders_2(A_3149)
      | r2_lattice3(A_3151,k3_xboole_0(A_3153,B_3152),C_3150)
      | ~ m1_subset_1(C_3150,u1_struct_0(A_3151))
      | ~ l1_orders_2(A_3151) ) ),
    inference(resolution,[status(thm)],[c_168,c_30675])).

tff(c_67667,plain,(
    ! [A_3155,C_3157,B_3159,C_3156,A_3158] :
      ( r1_orders_2(A_3158,'#skF_4'(A_3158,k3_xboole_0(A_3155,B_3159),C_3157),C_3156)
      | ~ r2_lattice3(A_3158,A_3155,C_3156)
      | ~ m1_subset_1(C_3156,u1_struct_0(A_3158))
      | r2_lattice3(A_3158,k3_xboole_0(A_3155,B_3159),C_3157)
      | ~ m1_subset_1(C_3157,u1_struct_0(A_3158))
      | ~ l1_orders_2(A_3158) ) ),
    inference(resolution,[status(thm)],[c_34,c_67653])).

tff(c_30,plain,(
    ! [A_19,B_26,C_27] :
      ( ~ r1_orders_2(A_19,'#skF_4'(A_19,B_26,C_27),C_27)
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67690,plain,(
    ! [A_3160,A_3161,C_3162,B_3163] :
      ( ~ r2_lattice3(A_3160,A_3161,C_3162)
      | r2_lattice3(A_3160,k3_xboole_0(A_3161,B_3163),C_3162)
      | ~ m1_subset_1(C_3162,u1_struct_0(A_3160))
      | ~ l1_orders_2(A_3160) ) ),
    inference(resolution,[status(thm)],[c_67667,c_30])).

tff(c_30496,plain,(
    ~ r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_72,plain,
    ( ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30645,plain,
    ( ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r1_lattice3('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30508,c_72])).

tff(c_30646,plain,(
    ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_30496,c_103,c_30645])).

tff(c_67719,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_67690,c_30646])).

tff(c_67751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_30508,c_67719])).

tff(c_67753,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_30495])).

tff(c_32,plain,(
    ! [A_19,B_26,C_27] :
      ( r2_hidden('#skF_4'(A_19,B_26,C_27),B_26)
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67752,plain,(
    r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_30495])).

tff(c_67837,plain,(
    ! [A_3199,D_3200,C_3201,B_3202] :
      ( r1_orders_2(A_3199,D_3200,C_3201)
      | ~ r2_hidden(D_3200,B_3202)
      | ~ m1_subset_1(D_3200,u1_struct_0(A_3199))
      | ~ r2_lattice3(A_3199,B_3202,C_3201)
      | ~ m1_subset_1(C_3201,u1_struct_0(A_3199))
      | ~ l1_orders_2(A_3199) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69899,plain,(
    ! [B_3407,A_3409,C_3406,D_3405,A_3408] :
      ( r1_orders_2(A_3409,D_3405,C_3406)
      | ~ m1_subset_1(D_3405,u1_struct_0(A_3409))
      | ~ r2_lattice3(A_3409,k3_xboole_0(A_3408,B_3407),C_3406)
      | ~ m1_subset_1(C_3406,u1_struct_0(A_3409))
      | ~ l1_orders_2(A_3409)
      | ~ r2_hidden(D_3405,B_3407)
      | ~ r2_hidden(D_3405,A_3408) ) ),
    inference(resolution,[status(thm)],[c_2,c_67837])).

tff(c_97812,plain,(
    ! [C_4571,B_4566,C_4567,A_4569,A_4570,B_4568] :
      ( r1_orders_2(A_4570,'#skF_3'(A_4570,B_4568,C_4571),C_4567)
      | ~ r2_lattice3(A_4570,k3_xboole_0(A_4569,B_4566),C_4567)
      | ~ m1_subset_1(C_4567,u1_struct_0(A_4570))
      | ~ r2_hidden('#skF_3'(A_4570,B_4568,C_4571),B_4566)
      | ~ r2_hidden('#skF_3'(A_4570,B_4568,C_4571),A_4569)
      | r1_lattice3(A_4570,B_4568,C_4571)
      | ~ m1_subset_1(C_4571,u1_struct_0(A_4570))
      | ~ l1_orders_2(A_4570) ) ),
    inference(resolution,[status(thm)],[c_26,c_69899])).

tff(c_97820,plain,(
    ! [B_4568,C_4571] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_4568,C_4571),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_4568,C_4571),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_4568,C_4571),'#skF_6')
      | r1_lattice3('#skF_5',B_4568,C_4571)
      | ~ m1_subset_1(C_4571,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_67752,c_97812])).

tff(c_97897,plain,(
    ! [B_4576,C_4577] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_4576,C_4577),'#skF_7')
      | ~ r2_hidden('#skF_3'('#skF_5',B_4576,C_4577),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_4576,C_4577),'#skF_6')
      | r1_lattice3('#skF_5',B_4576,C_4577)
      | ~ m1_subset_1(C_4577,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_97820])).

tff(c_98006,plain,(
    ! [B_4576,C_4577] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_4576,C_4577),'#skF_7')
      | ~ r2_hidden('#skF_3'('#skF_5',B_4576,C_4577),'#skF_6')
      | r1_lattice3('#skF_5',B_4576,C_4577)
      | ~ m1_subset_1(C_4577,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_4576,C_4577),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_97897])).

tff(c_98015,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_98006])).

tff(c_98018,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_98015,c_38])).

tff(c_98021,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_98018])).

tff(c_98024,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_98021])).

tff(c_98028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_98024])).

tff(c_98030,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_98006])).

tff(c_98032,plain,(
    ! [C_4586,B_4590,A_4587,C_4588,B_4585,A_4589] :
      ( r1_orders_2(A_4589,'#skF_4'(A_4589,B_4590,C_4588),C_4586)
      | ~ r2_lattice3(A_4589,k3_xboole_0(A_4587,B_4585),C_4586)
      | ~ m1_subset_1(C_4586,u1_struct_0(A_4589))
      | ~ r2_hidden('#skF_4'(A_4589,B_4590,C_4588),B_4585)
      | ~ r2_hidden('#skF_4'(A_4589,B_4590,C_4588),A_4587)
      | r2_lattice3(A_4589,B_4590,C_4588)
      | ~ m1_subset_1(C_4588,u1_struct_0(A_4589))
      | ~ l1_orders_2(A_4589) ) ),
    inference(resolution,[status(thm)],[c_34,c_69899])).

tff(c_98040,plain,(
    ! [B_4590,C_4588] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_4590,C_4588),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_4590,C_4588),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_4590,C_4588),'#skF_6')
      | r2_lattice3('#skF_5',B_4590,C_4588)
      | ~ m1_subset_1(C_4588,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_67752,c_98032])).

tff(c_98176,plain,(
    ! [B_4597,C_4598] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_4597,C_4598),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_4597,C_4598),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_4597,C_4598),'#skF_6')
      | r2_lattice3('#skF_5',B_4597,C_4598)
      | ~ m1_subset_1(C_4598,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_98040])).

tff(c_98239,plain,(
    ! [B_4597,C_4598] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_4597,C_4598),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_4597,C_4598),'#skF_6')
      | r2_lattice3('#skF_5',B_4597,C_4598)
      | ~ m1_subset_1(C_4598,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_4597,C_4598),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_98176])).

tff(c_98335,plain,(
    ! [B_4608,C_4609] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_4608,C_4609),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_4608,C_4609),'#skF_6')
      | r2_lattice3('#skF_5',B_4608,C_4609)
      | ~ m1_subset_1(C_4609,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_4608,C_4609),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98030,c_98239])).

tff(c_98339,plain,(
    ! [B_26,C_27] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_26,C_27),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_26,C_27),'#skF_6')
      | r2_lattice3('#skF_5',B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_98335])).

tff(c_98343,plain,(
    ! [B_4610,C_4611] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_4610,C_4611),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_4610,C_4611),'#skF_6')
      | r2_lattice3('#skF_5',B_4610,C_4611)
      | ~ m1_subset_1(C_4611,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_98339])).

tff(c_98347,plain,(
    ! [B_4610] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_5',B_4610,'#skF_7'),'#skF_6')
      | r2_lattice3('#skF_5',B_4610,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_98343,c_30])).

tff(c_98351,plain,(
    ! [B_4612] :
      ( ~ r2_hidden('#skF_4'('#skF_5',B_4612,'#skF_7'),'#skF_6')
      | r2_lattice3('#skF_5',B_4612,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_98347])).

tff(c_98411,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_98351])).

tff(c_98459,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_98411])).

tff(c_98461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67753,c_98459])).

tff(c_98463,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_98519,plain,(
    ! [A_4628,B_4629,C_4630] :
      ( r2_hidden('#skF_3'(A_4628,B_4629,C_4630),B_4629)
      | r1_lattice3(A_4628,B_4629,C_4630)
      | ~ m1_subset_1(C_4630,u1_struct_0(A_4628))
      | ~ l1_orders_2(A_4628) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98528,plain,(
    ! [A_4628,A_1,B_2,C_4630] :
      ( r2_hidden('#skF_3'(A_4628,k3_xboole_0(A_1,B_2),C_4630),A_1)
      | r1_lattice3(A_4628,k3_xboole_0(A_1,B_2),C_4630)
      | ~ m1_subset_1(C_4630,u1_struct_0(A_4628))
      | ~ l1_orders_2(A_4628) ) ),
    inference(resolution,[status(thm)],[c_98519,c_6])).

tff(c_98740,plain,(
    ! [A_4685,C_4686,D_4687,B_4688] :
      ( r1_orders_2(A_4685,C_4686,D_4687)
      | ~ r2_hidden(D_4687,B_4688)
      | ~ m1_subset_1(D_4687,u1_struct_0(A_4685))
      | ~ r1_lattice3(A_4685,B_4688,C_4686)
      | ~ m1_subset_1(C_4686,u1_struct_0(A_4685))
      | ~ l1_orders_2(A_4685) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134839,plain,(
    ! [B_6238,C_6237,A_6236,A_6239,C_6240,A_6235] :
      ( r1_orders_2(A_6235,C_6240,'#skF_3'(A_6236,k3_xboole_0(A_6239,B_6238),C_6237))
      | ~ m1_subset_1('#skF_3'(A_6236,k3_xboole_0(A_6239,B_6238),C_6237),u1_struct_0(A_6235))
      | ~ r1_lattice3(A_6235,A_6239,C_6240)
      | ~ m1_subset_1(C_6240,u1_struct_0(A_6235))
      | ~ l1_orders_2(A_6235)
      | r1_lattice3(A_6236,k3_xboole_0(A_6239,B_6238),C_6237)
      | ~ m1_subset_1(C_6237,u1_struct_0(A_6236))
      | ~ l1_orders_2(A_6236) ) ),
    inference(resolution,[status(thm)],[c_98528,c_98740])).

tff(c_136429,plain,(
    ! [A_6318,C_6316,B_6317,A_6320,C_6319] :
      ( r1_orders_2(A_6318,C_6316,'#skF_3'(A_6318,k3_xboole_0(A_6320,B_6317),C_6319))
      | ~ r1_lattice3(A_6318,A_6320,C_6316)
      | ~ m1_subset_1(C_6316,u1_struct_0(A_6318))
      | r1_lattice3(A_6318,k3_xboole_0(A_6320,B_6317),C_6319)
      | ~ m1_subset_1(C_6319,u1_struct_0(A_6318))
      | ~ l1_orders_2(A_6318) ) ),
    inference(resolution,[status(thm)],[c_26,c_134839])).

tff(c_136452,plain,(
    ! [A_6321,A_6322,C_6323,B_6324] :
      ( ~ r1_lattice3(A_6321,A_6322,C_6323)
      | r1_lattice3(A_6321,k3_xboole_0(A_6322,B_6324),C_6323)
      | ~ m1_subset_1(C_6323,u1_struct_0(A_6321))
      | ~ l1_orders_2(A_6321) ) ),
    inference(resolution,[status(thm)],[c_136429,c_22])).

tff(c_98462,plain,
    ( ~ r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_98578,plain,(
    ~ r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_98462])).

tff(c_136473,plain,
    ( ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_136452,c_98578])).

tff(c_136499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_98463,c_136473])).

tff(c_136501,plain,(
    r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_98462])).

tff(c_48,plain,
    ( ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136503,plain,
    ( ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98463,c_136501,c_48])).

tff(c_136504,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_136503])).

tff(c_136665,plain,(
    ! [A_6360,C_6361,D_6362,B_6363] :
      ( r1_orders_2(A_6360,C_6361,D_6362)
      | ~ r2_hidden(D_6362,B_6363)
      | ~ m1_subset_1(D_6362,u1_struct_0(A_6360))
      | ~ r1_lattice3(A_6360,B_6363,C_6361)
      | ~ m1_subset_1(C_6361,u1_struct_0(A_6360))
      | ~ l1_orders_2(A_6360) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138102,plain,(
    ! [D_6492,A_6496,A_6494,B_6495,C_6493] :
      ( r1_orders_2(A_6494,C_6493,D_6492)
      | ~ m1_subset_1(D_6492,u1_struct_0(A_6494))
      | ~ r1_lattice3(A_6494,k3_xboole_0(A_6496,B_6495),C_6493)
      | ~ m1_subset_1(C_6493,u1_struct_0(A_6494))
      | ~ l1_orders_2(A_6494)
      | ~ r2_hidden(D_6492,B_6495)
      | ~ r2_hidden(D_6492,A_6496) ) ),
    inference(resolution,[status(thm)],[c_2,c_136665])).

tff(c_169751,plain,(
    ! [B_7749,C_7747,C_7746,A_7748,A_7751,B_7750] :
      ( r1_orders_2(A_7748,C_7746,'#skF_4'(A_7748,B_7749,C_7747))
      | ~ r1_lattice3(A_7748,k3_xboole_0(A_7751,B_7750),C_7746)
      | ~ m1_subset_1(C_7746,u1_struct_0(A_7748))
      | ~ r2_hidden('#skF_4'(A_7748,B_7749,C_7747),B_7750)
      | ~ r2_hidden('#skF_4'(A_7748,B_7749,C_7747),A_7751)
      | r2_lattice3(A_7748,B_7749,C_7747)
      | ~ m1_subset_1(C_7747,u1_struct_0(A_7748))
      | ~ l1_orders_2(A_7748) ) ),
    inference(resolution,[status(thm)],[c_34,c_138102])).

tff(c_169761,plain,(
    ! [B_7749,C_7747] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_4'('#skF_5',B_7749,C_7747))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7749,C_7747),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7749,C_7747),'#skF_6')
      | r2_lattice3('#skF_5',B_7749,C_7747)
      | ~ m1_subset_1(C_7747,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_136501,c_169751])).

tff(c_169991,plain,(
    ! [B_7757,C_7758] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_4'('#skF_5',B_7757,C_7758))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7757,C_7758),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7757,C_7758),'#skF_6')
      | r2_lattice3('#skF_5',B_7757,C_7758)
      | ~ m1_subset_1(C_7758,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_169761])).

tff(c_170100,plain,(
    ! [B_7757,C_7758] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_4'('#skF_5',B_7757,C_7758))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7757,C_7758),'#skF_6')
      | r2_lattice3('#skF_5',B_7757,C_7758)
      | ~ m1_subset_1(C_7758,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_7757,C_7758),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_169991])).

tff(c_170452,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_170100])).

tff(c_170455,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_170452,c_38])).

tff(c_170458,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_170455])).

tff(c_170461,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_170458])).

tff(c_170465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_170461])).

tff(c_170467,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_170100])).

tff(c_136500,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_98462])).

tff(c_136505,plain,(
    r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_136504,c_136500])).

tff(c_136539,plain,(
    ! [A_6334,D_6335,C_6336,B_6337] :
      ( r1_orders_2(A_6334,D_6335,C_6336)
      | ~ r2_hidden(D_6335,B_6337)
      | ~ m1_subset_1(D_6335,u1_struct_0(A_6334))
      | ~ r2_lattice3(A_6334,B_6337,C_6336)
      | ~ m1_subset_1(C_6336,u1_struct_0(A_6334))
      | ~ l1_orders_2(A_6334) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138283,plain,(
    ! [D_6515,A_6518,A_6517,C_6519,B_6516] :
      ( r1_orders_2(A_6518,D_6515,C_6519)
      | ~ m1_subset_1(D_6515,u1_struct_0(A_6518))
      | ~ r2_lattice3(A_6518,k3_xboole_0(A_6517,B_6516),C_6519)
      | ~ m1_subset_1(C_6519,u1_struct_0(A_6518))
      | ~ l1_orders_2(A_6518)
      | ~ r2_hidden(D_6515,B_6516)
      | ~ r2_hidden(D_6515,A_6517) ) ),
    inference(resolution,[status(thm)],[c_2,c_136539])).

tff(c_168599,plain,(
    ! [C_7702,A_7700,B_7705,A_7703,C_7701,B_7704] :
      ( r1_orders_2(A_7703,'#skF_4'(A_7703,B_7704,C_7701),C_7702)
      | ~ r2_lattice3(A_7703,k3_xboole_0(A_7700,B_7705),C_7702)
      | ~ m1_subset_1(C_7702,u1_struct_0(A_7703))
      | ~ r2_hidden('#skF_4'(A_7703,B_7704,C_7701),B_7705)
      | ~ r2_hidden('#skF_4'(A_7703,B_7704,C_7701),A_7700)
      | r2_lattice3(A_7703,B_7704,C_7701)
      | ~ m1_subset_1(C_7701,u1_struct_0(A_7703))
      | ~ l1_orders_2(A_7703) ) ),
    inference(resolution,[status(thm)],[c_34,c_138283])).

tff(c_168609,plain,(
    ! [B_7704,C_7701] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_7704,C_7701),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7704,C_7701),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7704,C_7701),'#skF_6')
      | r2_lattice3('#skF_5',B_7704,C_7701)
      | ~ m1_subset_1(C_7701,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_136505,c_168599])).

tff(c_168816,plain,(
    ! [B_7710,C_7711] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_7710,C_7711),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_7710,C_7711),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'('#skF_5',B_7710,C_7711),'#skF_6')
      | r2_lattice3('#skF_5',B_7710,C_7711)
      | ~ m1_subset_1(C_7711,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_168609])).

tff(c_168925,plain,(
    ! [B_7710,C_7711] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_7710,C_7711),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_7710,C_7711),'#skF_6')
      | r2_lattice3('#skF_5',B_7710,C_7711)
      | ~ m1_subset_1(C_7711,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_7710,C_7711),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_168816])).

tff(c_176401,plain,(
    ! [B_8020,C_8021] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_8020,C_8021),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_8020,C_8021),'#skF_6')
      | r2_lattice3('#skF_5',B_8020,C_8021)
      | ~ m1_subset_1(C_8021,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_8020,C_8021),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170467,c_168925])).

tff(c_176405,plain,(
    ! [B_26,C_27] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_26,C_27),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_26,C_27),'#skF_6')
      | r2_lattice3('#skF_5',B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_176401])).

tff(c_176409,plain,(
    ! [B_8022,C_8023] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_8022,C_8023),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_5',B_8022,C_8023),'#skF_6')
      | r2_lattice3('#skF_5',B_8022,C_8023)
      | ~ m1_subset_1(C_8023,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_176405])).

tff(c_176413,plain,(
    ! [B_8022] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_5',B_8022,'#skF_7'),'#skF_6')
      | r2_lattice3('#skF_5',B_8022,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_176409,c_30])).

tff(c_176417,plain,(
    ! [B_8024] :
      ( ~ r2_hidden('#skF_4'('#skF_5',B_8024,'#skF_7'),'#skF_6')
      | r2_lattice3('#skF_5',B_8024,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_176413])).

tff(c_176477,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_176417])).

tff(c_176525,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_176477])).

tff(c_176527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136504,c_176525])).

tff(c_176529,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_136503])).

tff(c_98487,plain,(
    ! [A_4622,B_4623,C_4624] :
      ( r2_hidden('#skF_4'(A_4622,B_4623,C_4624),B_4623)
      | r2_lattice3(A_4622,B_4623,C_4624)
      | ~ m1_subset_1(C_4624,u1_struct_0(A_4622))
      | ~ l1_orders_2(A_4622) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_176635,plain,(
    ! [A_8044,A_8045,B_8046,C_8047] :
      ( r2_hidden('#skF_4'(A_8044,k3_xboole_0(A_8045,B_8046),C_8047),A_8045)
      | r2_lattice3(A_8044,k3_xboole_0(A_8045,B_8046),C_8047)
      | ~ m1_subset_1(C_8047,u1_struct_0(A_8044))
      | ~ l1_orders_2(A_8044) ) ),
    inference(resolution,[status(thm)],[c_98487,c_6])).

tff(c_28,plain,(
    ! [A_19,D_30,C_27,B_26] :
      ( r1_orders_2(A_19,D_30,C_27)
      | ~ r2_hidden(D_30,B_26)
      | ~ m1_subset_1(D_30,u1_struct_0(A_19))
      | ~ r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_213762,plain,(
    ! [A_9461,A_9457,B_9459,C_9460,A_9458,C_9462] :
      ( r1_orders_2(A_9461,'#skF_4'(A_9457,k3_xboole_0(A_9458,B_9459),C_9462),C_9460)
      | ~ m1_subset_1('#skF_4'(A_9457,k3_xboole_0(A_9458,B_9459),C_9462),u1_struct_0(A_9461))
      | ~ r2_lattice3(A_9461,A_9458,C_9460)
      | ~ m1_subset_1(C_9460,u1_struct_0(A_9461))
      | ~ l1_orders_2(A_9461)
      | r2_lattice3(A_9457,k3_xboole_0(A_9458,B_9459),C_9462)
      | ~ m1_subset_1(C_9462,u1_struct_0(A_9457))
      | ~ l1_orders_2(A_9457) ) ),
    inference(resolution,[status(thm)],[c_176635,c_28])).

tff(c_228401,plain,(
    ! [C_10010,B_10007,A_10011,C_10008,A_10009] :
      ( r1_orders_2(A_10009,'#skF_4'(A_10009,k3_xboole_0(A_10011,B_10007),C_10008),C_10010)
      | ~ r2_lattice3(A_10009,A_10011,C_10010)
      | ~ m1_subset_1(C_10010,u1_struct_0(A_10009))
      | r2_lattice3(A_10009,k3_xboole_0(A_10011,B_10007),C_10008)
      | ~ m1_subset_1(C_10008,u1_struct_0(A_10009))
      | ~ l1_orders_2(A_10009) ) ),
    inference(resolution,[status(thm)],[c_34,c_213762])).

tff(c_228432,plain,(
    ! [A_10012,A_10013,C_10014,B_10015] :
      ( ~ r2_lattice3(A_10012,A_10013,C_10014)
      | r2_lattice3(A_10012,k3_xboole_0(A_10013,B_10015),C_10014)
      | ~ m1_subset_1(C_10014,u1_struct_0(A_10012))
      | ~ l1_orders_2(A_10012) ) ),
    inference(resolution,[status(thm)],[c_228401,c_30])).

tff(c_176528,plain,(
    ~ r2_lattice3('#skF_5',k3_xboole_0('#skF_6',u1_struct_0('#skF_5')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_136503])).

tff(c_228461,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_228432,c_176528])).

tff(c_228499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_176529,c_228461])).

%------------------------------------------------------------------------------
