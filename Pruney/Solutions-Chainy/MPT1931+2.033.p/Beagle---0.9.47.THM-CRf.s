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
% DateTime   : Thu Dec  3 10:30:50 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 177 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_53,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_72,B_76,C_78] :
      ( r2_waybel_0(A_72,B_76,C_78)
      | r1_waybel_0(A_72,B_76,k6_subset_1(u1_struct_0(A_72),C_78))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_946,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_waybel_0(A_174,B_175,C_176)
      | r1_waybel_0(A_174,B_175,k4_xboole_0(u1_struct_0(A_174),C_176))
      | ~ l1_waybel_0(B_175,A_174)
      | v2_struct_0(B_175)
      | ~ l1_struct_0(A_174)
      | v2_struct_0(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_2409,plain,(
    ! [A_279,B_280] :
      ( r2_waybel_0(A_279,B_280,k1_xboole_0)
      | r1_waybel_0(A_279,B_280,u1_struct_0(A_279))
      | ~ l1_waybel_0(B_280,A_279)
      | v2_struct_0(B_280)
      | ~ l1_struct_0(A_279)
      | v2_struct_0(A_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_946])).

tff(c_44,plain,(
    ~ r1_waybel_0('#skF_7','#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2415,plain,
    ( r2_waybel_0('#skF_7','#skF_8',k1_xboole_0)
    | ~ l1_waybel_0('#skF_8','#skF_7')
    | v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2409,c_44])).

tff(c_2419,plain,
    ( r2_waybel_0('#skF_7','#skF_8',k1_xboole_0)
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_2415])).

tff(c_2420,plain,(
    r2_waybel_0('#skF_7','#skF_8',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_2419])).

tff(c_26,plain,(
    ! [A_15] : m1_subset_1('#skF_4'(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1668,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( r2_hidden(k2_waybel_0(A_222,B_223,'#skF_6'(A_222,B_223,C_224,D_225)),C_224)
      | ~ m1_subset_1(D_225,u1_struct_0(B_223))
      | ~ r2_waybel_0(A_222,B_223,C_224)
      | ~ l1_waybel_0(B_223,A_222)
      | v2_struct_0(B_223)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,(
    ! [D_91,A_92,B_93] :
      ( r2_hidden(D_91,A_92)
      | ~ r2_hidden(D_91,k4_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_8,A_92,B_93] :
      ( r2_hidden('#skF_3'(A_8,k4_xboole_0(A_92,B_93)),A_92)
      | ~ r2_hidden(A_8,k4_xboole_0(A_92,B_93)) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_83,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_3'(A_89,B_90),B_90)
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_105,A_106,B_107] :
      ( ~ r2_hidden('#skF_3'(A_105,k4_xboole_0(A_106,B_107)),B_107)
      | ~ r2_hidden(A_105,k4_xboole_0(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_206,plain,(
    ! [A_111,A_112] : ~ r2_hidden(A_111,k4_xboole_0(A_112,A_112)) ),
    inference(resolution,[status(thm)],[c_101,c_155])).

tff(c_230,plain,(
    ! [A_111] : ~ r2_hidden(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_206])).

tff(c_2867,plain,(
    ! [D_305,B_306,A_307] :
      ( ~ m1_subset_1(D_305,u1_struct_0(B_306))
      | ~ r2_waybel_0(A_307,B_306,k1_xboole_0)
      | ~ l1_waybel_0(B_306,A_307)
      | v2_struct_0(B_306)
      | ~ l1_struct_0(A_307)
      | v2_struct_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_1668,c_230])).

tff(c_2877,plain,(
    ! [A_308,B_309] :
      ( ~ r2_waybel_0(A_308,B_309,k1_xboole_0)
      | ~ l1_waybel_0(B_309,A_308)
      | v2_struct_0(B_309)
      | ~ l1_struct_0(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_26,c_2867])).

tff(c_2880,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2420,c_2877])).

tff(c_2883,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_2880])).

tff(c_2885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_2883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  
% 4.74/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8
% 4.74/1.92  
% 4.74/1.92  %Foreground sorts:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Background operators:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Foreground operators:
% 4.74/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.74/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.74/1.92  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 4.74/1.92  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.92  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.74/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.92  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 4.74/1.92  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.74/1.92  tff('#skF_7', type, '#skF_7': $i).
% 4.74/1.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.74/1.92  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 4.74/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.74/1.92  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.74/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.74/1.92  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.74/1.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.74/1.92  tff('#skF_8', type, '#skF_8': $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.92  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.74/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.92  
% 4.74/1.94  tff(f_114, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 4.74/1.94  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.74/1.94  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.74/1.94  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 4.74/1.94  tff(f_53, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.74/1.94  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 4.74/1.94  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 4.74/1.94  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.74/1.94  tff(c_56, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.94  tff(c_52, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.94  tff(c_54, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.94  tff(c_46, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.94  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.94  tff(c_28, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.94  tff(c_42, plain, (![A_72, B_76, C_78]: (r2_waybel_0(A_72, B_76, C_78) | r1_waybel_0(A_72, B_76, k6_subset_1(u1_struct_0(A_72), C_78)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.74/1.94  tff(c_946, plain, (![A_174, B_175, C_176]: (r2_waybel_0(A_174, B_175, C_176) | r1_waybel_0(A_174, B_175, k4_xboole_0(u1_struct_0(A_174), C_176)) | ~l1_waybel_0(B_175, A_174) | v2_struct_0(B_175) | ~l1_struct_0(A_174) | v2_struct_0(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42])).
% 4.74/1.94  tff(c_2409, plain, (![A_279, B_280]: (r2_waybel_0(A_279, B_280, k1_xboole_0) | r1_waybel_0(A_279, B_280, u1_struct_0(A_279)) | ~l1_waybel_0(B_280, A_279) | v2_struct_0(B_280) | ~l1_struct_0(A_279) | v2_struct_0(A_279))), inference(superposition, [status(thm), theory('equality')], [c_20, c_946])).
% 4.74/1.94  tff(c_44, plain, (~r1_waybel_0('#skF_7', '#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.94  tff(c_2415, plain, (r2_waybel_0('#skF_7', '#skF_8', k1_xboole_0) | ~l1_waybel_0('#skF_8', '#skF_7') | v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2409, c_44])).
% 4.74/1.94  tff(c_2419, plain, (r2_waybel_0('#skF_7', '#skF_8', k1_xboole_0) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_2415])).
% 4.74/1.94  tff(c_2420, plain, (r2_waybel_0('#skF_7', '#skF_8', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_2419])).
% 4.74/1.94  tff(c_26, plain, (![A_15]: (m1_subset_1('#skF_4'(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.94  tff(c_1668, plain, (![A_222, B_223, C_224, D_225]: (r2_hidden(k2_waybel_0(A_222, B_223, '#skF_6'(A_222, B_223, C_224, D_225)), C_224) | ~m1_subset_1(D_225, u1_struct_0(B_223)) | ~r2_waybel_0(A_222, B_223, C_224) | ~l1_waybel_0(B_223, A_222) | v2_struct_0(B_223) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.74/1.94  tff(c_24, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.74/1.94  tff(c_93, plain, (![D_91, A_92, B_93]: (r2_hidden(D_91, A_92) | ~r2_hidden(D_91, k4_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/1.94  tff(c_101, plain, (![A_8, A_92, B_93]: (r2_hidden('#skF_3'(A_8, k4_xboole_0(A_92, B_93)), A_92) | ~r2_hidden(A_8, k4_xboole_0(A_92, B_93)))), inference(resolution, [status(thm)], [c_24, c_93])).
% 4.74/1.94  tff(c_83, plain, (![A_89, B_90]: (r2_hidden('#skF_3'(A_89, B_90), B_90) | ~r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.74/1.94  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/1.94  tff(c_155, plain, (![A_105, A_106, B_107]: (~r2_hidden('#skF_3'(A_105, k4_xboole_0(A_106, B_107)), B_107) | ~r2_hidden(A_105, k4_xboole_0(A_106, B_107)))), inference(resolution, [status(thm)], [c_83, c_4])).
% 4.74/1.94  tff(c_206, plain, (![A_111, A_112]: (~r2_hidden(A_111, k4_xboole_0(A_112, A_112)))), inference(resolution, [status(thm)], [c_101, c_155])).
% 4.74/1.94  tff(c_230, plain, (![A_111]: (~r2_hidden(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_206])).
% 4.74/1.94  tff(c_2867, plain, (![D_305, B_306, A_307]: (~m1_subset_1(D_305, u1_struct_0(B_306)) | ~r2_waybel_0(A_307, B_306, k1_xboole_0) | ~l1_waybel_0(B_306, A_307) | v2_struct_0(B_306) | ~l1_struct_0(A_307) | v2_struct_0(A_307))), inference(resolution, [status(thm)], [c_1668, c_230])).
% 4.74/1.94  tff(c_2877, plain, (![A_308, B_309]: (~r2_waybel_0(A_308, B_309, k1_xboole_0) | ~l1_waybel_0(B_309, A_308) | v2_struct_0(B_309) | ~l1_struct_0(A_308) | v2_struct_0(A_308))), inference(resolution, [status(thm)], [c_26, c_2867])).
% 4.74/1.94  tff(c_2880, plain, (~l1_waybel_0('#skF_8', '#skF_7') | v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2420, c_2877])).
% 4.74/1.94  tff(c_2883, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_2880])).
% 4.74/1.94  tff(c_2885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_2883])).
% 4.74/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.94  
% 4.74/1.94  Inference rules
% 4.74/1.94  ----------------------
% 4.74/1.94  #Ref     : 0
% 4.74/1.94  #Sup     : 626
% 4.74/1.94  #Fact    : 0
% 4.74/1.94  #Define  : 0
% 4.74/1.94  #Split   : 0
% 4.74/1.94  #Chain   : 0
% 4.74/1.94  #Close   : 0
% 4.74/1.94  
% 4.74/1.94  Ordering : KBO
% 4.74/1.94  
% 4.74/1.94  Simplification rules
% 4.74/1.94  ----------------------
% 4.74/1.94  #Subsume      : 254
% 4.74/1.94  #Demod        : 448
% 4.74/1.94  #Tautology    : 190
% 4.74/1.94  #SimpNegUnit  : 29
% 4.74/1.94  #BackRed      : 8
% 4.74/1.94  
% 4.74/1.94  #Partial instantiations: 0
% 4.74/1.94  #Strategies tried      : 1
% 4.74/1.94  
% 4.74/1.94  Timing (in seconds)
% 4.74/1.94  ----------------------
% 4.74/1.94  Preprocessing        : 0.44
% 4.74/1.94  Parsing              : 0.23
% 4.74/1.94  CNF conversion       : 0.04
% 4.74/1.94  Main loop            : 0.80
% 4.74/1.94  Inferencing          : 0.30
% 4.74/1.94  Reduction            : 0.25
% 4.74/1.94  Demodulation         : 0.18
% 4.74/1.94  BG Simplification    : 0.03
% 4.74/1.94  Subsumption          : 0.16
% 4.74/1.94  Abstraction          : 0.05
% 4.74/1.94  MUC search           : 0.00
% 4.74/1.94  Cooper               : 0.00
% 4.74/1.94  Total                : 1.28
% 4.74/1.94  Index Insertion      : 0.00
% 4.74/1.94  Index Deletion       : 0.00
% 4.74/1.94  Index Matching       : 0.00
% 4.74/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
