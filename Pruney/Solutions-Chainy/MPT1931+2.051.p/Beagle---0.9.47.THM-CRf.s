%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 178 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
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

tff(f_52,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),B_89)
      | r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [B_102,A_103] :
      ( ~ r1_tarski(B_102,'#skF_1'(A_103,B_102))
      | r1_xboole_0(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_72,c_18])).

tff(c_116,plain,(
    ! [A_104] : r1_xboole_0(A_104,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_104] : k4_xboole_0(A_104,k1_xboole_0) = A_104 ),
    inference(resolution,[status(thm)],[c_116,c_10])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [A_68,B_72,C_74] :
      ( r2_waybel_0(A_68,B_72,C_74)
      | r1_waybel_0(A_68,B_72,k6_subset_1(u1_struct_0(A_68),C_74))
      | ~ l1_waybel_0(B_72,A_68)
      | v2_struct_0(B_72)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_154,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_waybel_0(A_108,B_109,C_110)
      | r1_waybel_0(A_108,B_109,k4_xboole_0(u1_struct_0(A_108),C_110))
      | ~ l1_waybel_0(B_109,A_108)
      | v2_struct_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_273,plain,(
    ! [A_152,B_153] :
      ( r2_waybel_0(A_152,B_153,k1_xboole_0)
      | r1_waybel_0(A_152,B_153,u1_struct_0(A_152))
      | ~ l1_waybel_0(B_153,A_152)
      | v2_struct_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_154])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_279,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_273,c_34])).

tff(c_283,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_279])).

tff(c_284,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_283])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1('#skF_2'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_285,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( r2_hidden(k2_waybel_0(A_154,B_155,'#skF_4'(A_154,B_155,C_156,D_157)),C_156)
      | ~ m1_subset_1(D_157,u1_struct_0(B_155))
      | ~ r2_waybel_0(A_154,B_155,C_156)
      | ~ l1_waybel_0(B_155,A_154)
      | v2_struct_0(B_155)
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_306,plain,(
    ! [C_162,A_163,B_164,D_165] :
      ( ~ r1_tarski(C_162,k2_waybel_0(A_163,B_164,'#skF_4'(A_163,B_164,C_162,D_165)))
      | ~ m1_subset_1(D_165,u1_struct_0(B_164))
      | ~ r2_waybel_0(A_163,B_164,C_162)
      | ~ l1_waybel_0(B_164,A_163)
      | v2_struct_0(B_164)
      | ~ l1_struct_0(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_285,c_18])).

tff(c_312,plain,(
    ! [D_166,B_167,A_168] :
      ( ~ m1_subset_1(D_166,u1_struct_0(B_167))
      | ~ r2_waybel_0(A_168,B_167,k1_xboole_0)
      | ~ l1_waybel_0(B_167,A_168)
      | v2_struct_0(B_167)
      | ~ l1_struct_0(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_8,c_306])).

tff(c_322,plain,(
    ! [A_169,B_170] :
      ( ~ r2_waybel_0(A_169,B_170,k1_xboole_0)
      | ~ l1_waybel_0(B_170,A_169)
      | v2_struct_0(B_170)
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_14,c_312])).

tff(c_325,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_284,c_322])).

tff(c_328,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.54/1.33  
% 2.54/1.33  %Foreground sorts:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Background operators:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Foreground operators:
% 2.54/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.33  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.54/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.54/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.33  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.54/1.33  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.54/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.33  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.54/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.54/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.54/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.54/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.34  
% 2.54/1.35  tff(f_118, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.54/1.35  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.54/1.35  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.54/1.35  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.54/1.35  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.54/1.35  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.54/1.35  tff(f_52, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.54/1.35  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.54/1.35  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.35  tff(c_42, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.35  tff(c_44, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.35  tff(c_36, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.35  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.35  tff(c_72, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), B_89) | r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.35  tff(c_18, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.35  tff(c_110, plain, (![B_102, A_103]: (~r1_tarski(B_102, '#skF_1'(A_103, B_102)) | r1_xboole_0(A_103, B_102))), inference(resolution, [status(thm)], [c_72, c_18])).
% 2.54/1.35  tff(c_116, plain, (![A_104]: (r1_xboole_0(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.54/1.35  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.35  tff(c_123, plain, (![A_104]: (k4_xboole_0(A_104, k1_xboole_0)=A_104)), inference(resolution, [status(thm)], [c_116, c_10])).
% 2.54/1.35  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.35  tff(c_32, plain, (![A_68, B_72, C_74]: (r2_waybel_0(A_68, B_72, C_74) | r1_waybel_0(A_68, B_72, k6_subset_1(u1_struct_0(A_68), C_74)) | ~l1_waybel_0(B_72, A_68) | v2_struct_0(B_72) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.35  tff(c_154, plain, (![A_108, B_109, C_110]: (r2_waybel_0(A_108, B_109, C_110) | r1_waybel_0(A_108, B_109, k4_xboole_0(u1_struct_0(A_108), C_110)) | ~l1_waybel_0(B_109, A_108) | v2_struct_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.54/1.35  tff(c_273, plain, (![A_152, B_153]: (r2_waybel_0(A_152, B_153, k1_xboole_0) | r1_waybel_0(A_152, B_153, u1_struct_0(A_152)) | ~l1_waybel_0(B_153, A_152) | v2_struct_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(superposition, [status(thm), theory('equality')], [c_123, c_154])).
% 2.54/1.35  tff(c_34, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.35  tff(c_279, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_273, c_34])).
% 2.54/1.35  tff(c_283, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_279])).
% 2.54/1.35  tff(c_284, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_283])).
% 2.54/1.35  tff(c_14, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.35  tff(c_285, plain, (![A_154, B_155, C_156, D_157]: (r2_hidden(k2_waybel_0(A_154, B_155, '#skF_4'(A_154, B_155, C_156, D_157)), C_156) | ~m1_subset_1(D_157, u1_struct_0(B_155)) | ~r2_waybel_0(A_154, B_155, C_156) | ~l1_waybel_0(B_155, A_154) | v2_struct_0(B_155) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.35  tff(c_306, plain, (![C_162, A_163, B_164, D_165]: (~r1_tarski(C_162, k2_waybel_0(A_163, B_164, '#skF_4'(A_163, B_164, C_162, D_165))) | ~m1_subset_1(D_165, u1_struct_0(B_164)) | ~r2_waybel_0(A_163, B_164, C_162) | ~l1_waybel_0(B_164, A_163) | v2_struct_0(B_164) | ~l1_struct_0(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_285, c_18])).
% 2.54/1.35  tff(c_312, plain, (![D_166, B_167, A_168]: (~m1_subset_1(D_166, u1_struct_0(B_167)) | ~r2_waybel_0(A_168, B_167, k1_xboole_0) | ~l1_waybel_0(B_167, A_168) | v2_struct_0(B_167) | ~l1_struct_0(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_8, c_306])).
% 2.54/1.35  tff(c_322, plain, (![A_169, B_170]: (~r2_waybel_0(A_169, B_170, k1_xboole_0) | ~l1_waybel_0(B_170, A_169) | v2_struct_0(B_170) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_14, c_312])).
% 2.54/1.35  tff(c_325, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_284, c_322])).
% 2.54/1.35  tff(c_328, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_325])).
% 2.54/1.35  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_328])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 59
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 0
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 10
% 2.54/1.35  #Demod        : 16
% 2.54/1.35  #Tautology    : 21
% 2.54/1.35  #SimpNegUnit  : 2
% 2.54/1.35  #BackRed      : 0
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.54/1.35  Preprocessing        : 0.32
% 2.54/1.35  Parsing              : 0.16
% 2.54/1.35  CNF conversion       : 0.03
% 2.54/1.35  Main loop            : 0.26
% 2.54/1.35  Inferencing          : 0.11
% 2.54/1.35  Reduction            : 0.07
% 2.54/1.35  Demodulation         : 0.05
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.05
% 2.54/1.35  Abstraction          : 0.02
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.62
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
