%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:49 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 175 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_100,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_2'(A_87,B_88),B_88)
      | r1_xboole_0(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_91,A_92] :
      ( ~ v1_xboole_0(B_91)
      | r1_xboole_0(A_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = A_95
      | ~ v1_xboole_0(B_96) ) ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_96,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_20,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_69,B_73,C_75] :
      ( r2_waybel_0(A_69,B_73,C_75)
      | r1_waybel_0(A_69,B_73,k6_subset_1(u1_struct_0(A_69),C_75))
      | ~ l1_waybel_0(B_73,A_69)
      | v2_struct_0(B_73)
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_152,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_waybel_0(A_109,B_110,C_111)
      | r1_waybel_0(A_109,B_110,k4_xboole_0(u1_struct_0(A_109),C_111))
      | ~ l1_waybel_0(B_110,A_109)
      | v2_struct_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_347,plain,(
    ! [A_165,B_166] :
      ( r2_waybel_0(A_165,B_166,k1_xboole_0)
      | r1_waybel_0(A_165,B_166,u1_struct_0(A_165))
      | ~ l1_waybel_0(B_166,A_165)
      | v2_struct_0(B_166)
      | ~ l1_struct_0(A_165)
      | v2_struct_0(A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_152])).

tff(c_36,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_350,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_347,c_36])).

tff(c_353,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_350])).

tff(c_354,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_353])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1('#skF_3'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_332,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( r2_hidden(k2_waybel_0(A_161,B_162,'#skF_5'(A_161,B_162,C_163,D_164)),C_163)
      | ~ m1_subset_1(D_164,u1_struct_0(B_162))
      | ~ r2_waybel_0(A_161,B_162,C_163)
      | ~ l1_waybel_0(B_162,A_161)
      | v2_struct_0(B_162)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_360,plain,(
    ! [C_169,D_170,B_171,A_172] :
      ( ~ v1_xboole_0(C_169)
      | ~ m1_subset_1(D_170,u1_struct_0(B_171))
      | ~ r2_waybel_0(A_172,B_171,C_169)
      | ~ l1_waybel_0(B_171,A_172)
      | v2_struct_0(B_171)
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_332,c_2])).

tff(c_370,plain,(
    ! [C_173,A_174,B_175] :
      ( ~ v1_xboole_0(C_173)
      | ~ r2_waybel_0(A_174,B_175,C_173)
      | ~ l1_waybel_0(B_175,A_174)
      | v2_struct_0(B_175)
      | ~ l1_struct_0(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_373,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_354,c_370])).

tff(c_376,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_6,c_373])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2
% 2.46/1.34  
% 2.46/1.34  %Foreground sorts:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Background operators:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Foreground operators:
% 2.46/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.34  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.46/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.34  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.46/1.34  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.46/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.46/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.46/1.34  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.46/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.46/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.46/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.46/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.34  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.46/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.46/1.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.46/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.34  
% 2.65/1.35  tff(f_118, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.65/1.35  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.65/1.35  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.65/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.65/1.35  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.65/1.35  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.65/1.35  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.65/1.35  tff(f_57, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.65/1.35  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.65/1.35  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.65/1.35  tff(c_44, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.65/1.35  tff(c_46, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.65/1.35  tff(c_38, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.65/1.35  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.35  tff(c_73, plain, (![A_87, B_88]: (r2_hidden('#skF_2'(A_87, B_88), B_88) | r1_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.65/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.35  tff(c_83, plain, (![B_91, A_92]: (~v1_xboole_0(B_91) | r1_xboole_0(A_92, B_91))), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.65/1.35  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.35  tff(c_93, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=A_95 | ~v1_xboole_0(B_96))), inference(resolution, [status(thm)], [c_83, c_14])).
% 2.65/1.35  tff(c_96, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=A_95)), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.65/1.35  tff(c_20, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.35  tff(c_34, plain, (![A_69, B_73, C_75]: (r2_waybel_0(A_69, B_73, C_75) | r1_waybel_0(A_69, B_73, k6_subset_1(u1_struct_0(A_69), C_75)) | ~l1_waybel_0(B_73, A_69) | v2_struct_0(B_73) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.35  tff(c_152, plain, (![A_109, B_110, C_111]: (r2_waybel_0(A_109, B_110, C_111) | r1_waybel_0(A_109, B_110, k4_xboole_0(u1_struct_0(A_109), C_111)) | ~l1_waybel_0(B_110, A_109) | v2_struct_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34])).
% 2.65/1.35  tff(c_347, plain, (![A_165, B_166]: (r2_waybel_0(A_165, B_166, k1_xboole_0) | r1_waybel_0(A_165, B_166, u1_struct_0(A_165)) | ~l1_waybel_0(B_166, A_165) | v2_struct_0(B_166) | ~l1_struct_0(A_165) | v2_struct_0(A_165))), inference(superposition, [status(thm), theory('equality')], [c_96, c_152])).
% 2.65/1.35  tff(c_36, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.65/1.35  tff(c_350, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_347, c_36])).
% 2.65/1.35  tff(c_353, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_350])).
% 2.65/1.35  tff(c_354, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_353])).
% 2.65/1.35  tff(c_18, plain, (![A_12]: (m1_subset_1('#skF_3'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.35  tff(c_332, plain, (![A_161, B_162, C_163, D_164]: (r2_hidden(k2_waybel_0(A_161, B_162, '#skF_5'(A_161, B_162, C_163, D_164)), C_163) | ~m1_subset_1(D_164, u1_struct_0(B_162)) | ~r2_waybel_0(A_161, B_162, C_163) | ~l1_waybel_0(B_162, A_161) | v2_struct_0(B_162) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.35  tff(c_360, plain, (![C_169, D_170, B_171, A_172]: (~v1_xboole_0(C_169) | ~m1_subset_1(D_170, u1_struct_0(B_171)) | ~r2_waybel_0(A_172, B_171, C_169) | ~l1_waybel_0(B_171, A_172) | v2_struct_0(B_171) | ~l1_struct_0(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_332, c_2])).
% 2.65/1.35  tff(c_370, plain, (![C_173, A_174, B_175]: (~v1_xboole_0(C_173) | ~r2_waybel_0(A_174, B_175, C_173) | ~l1_waybel_0(B_175, A_174) | v2_struct_0(B_175) | ~l1_struct_0(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_18, c_360])).
% 2.65/1.35  tff(c_373, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_354, c_370])).
% 2.65/1.35  tff(c_376, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_6, c_373])).
% 2.65/1.35  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_376])).
% 2.65/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  Inference rules
% 2.65/1.35  ----------------------
% 2.65/1.35  #Ref     : 0
% 2.65/1.35  #Sup     : 71
% 2.65/1.35  #Fact    : 0
% 2.65/1.35  #Define  : 0
% 2.65/1.35  #Split   : 0
% 2.65/1.35  #Chain   : 0
% 2.65/1.35  #Close   : 0
% 2.65/1.35  
% 2.65/1.35  Ordering : KBO
% 2.65/1.35  
% 2.65/1.35  Simplification rules
% 2.65/1.35  ----------------------
% 2.65/1.35  #Subsume      : 12
% 2.65/1.35  #Demod        : 21
% 2.65/1.35  #Tautology    : 26
% 2.65/1.35  #SimpNegUnit  : 2
% 2.65/1.35  #BackRed      : 0
% 2.65/1.35  
% 2.65/1.35  #Partial instantiations: 0
% 2.65/1.35  #Strategies tried      : 1
% 2.65/1.35  
% 2.65/1.35  Timing (in seconds)
% 2.65/1.35  ----------------------
% 2.65/1.35  Preprocessing        : 0.31
% 2.65/1.35  Parsing              : 0.16
% 2.65/1.35  CNF conversion       : 0.03
% 2.65/1.35  Main loop            : 0.24
% 2.65/1.35  Inferencing          : 0.10
% 2.65/1.35  Reduction            : 0.06
% 2.65/1.35  Demodulation         : 0.04
% 2.65/1.35  BG Simplification    : 0.02
% 2.65/1.35  Subsumption          : 0.05
% 2.65/1.35  Abstraction          : 0.01
% 2.65/1.35  MUC search           : 0.00
% 2.65/1.35  Cooper               : 0.00
% 2.65/1.35  Total                : 0.58
% 2.65/1.35  Index Insertion      : 0.00
% 2.65/1.35  Index Deletion       : 0.00
% 2.65/1.35  Index Matching       : 0.00
% 2.65/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
