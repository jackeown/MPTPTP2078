%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   74 (  94 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 ( 251 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_2_2_yellow_6,type,(
    o_2_2_yellow_6: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

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

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [B_89,A_90] :
      ( ~ r1_xboole_0(B_89,A_90)
      | ~ r1_tarski(B_89,A_90)
      | v1_xboole_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_91,B_92] :
      ( ~ r1_tarski(k4_xboole_0(A_91,B_92),B_92)
      | v1_xboole_0(k4_xboole_0(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_83,plain,(
    ! [A_93] : v1_xboole_0(k4_xboole_0(A_93,A_93)) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | B_86 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_89,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_65])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_67,B_71,C_73] :
      ( r1_waybel_0(A_67,B_71,C_73)
      | r2_waybel_0(A_67,B_71,k6_subset_1(u1_struct_0(A_67),C_73))
      | ~ l1_waybel_0(B_71,A_67)
      | v2_struct_0(B_71)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_121,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_waybel_0(A_98,B_99,C_100)
      | r2_waybel_0(A_98,B_99,k4_xboole_0(u1_struct_0(A_98),C_100))
      | ~ l1_waybel_0(B_99,A_98)
      | v2_struct_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_126,plain,(
    ! [A_101,B_102] :
      ( r1_waybel_0(A_101,B_102,u1_struct_0(A_101))
      | r2_waybel_0(A_101,B_102,k1_xboole_0)
      | ~ l1_waybel_0(B_102,A_101)
      | v2_struct_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_121])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_129,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_34])).

tff(c_132,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_129])).

tff(c_133,plain,(
    r2_waybel_0('#skF_3','#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_132])).

tff(c_32,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(o_2_2_yellow_6(A_74,B_75),u1_struct_0(B_75))
      | ~ l1_waybel_0(B_75,A_74)
      | ~ v7_waybel_0(B_75)
      | ~ v4_orders_2(B_75)
      | v2_struct_0(B_75)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_151,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( r2_hidden(k2_waybel_0(A_119,B_120,'#skF_2'(A_119,B_120,C_121,D_122)),C_121)
      | ~ m1_subset_1(D_122,u1_struct_0(B_120))
      | ~ r2_waybel_0(A_119,B_120,C_121)
      | ~ l1_waybel_0(B_120,A_119)
      | v2_struct_0(B_120)
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [C_123,A_124,B_125,D_126] :
      ( ~ r1_tarski(C_123,k2_waybel_0(A_124,B_125,'#skF_2'(A_124,B_125,C_123,D_126)))
      | ~ m1_subset_1(D_126,u1_struct_0(B_125))
      | ~ r2_waybel_0(A_124,B_125,C_123)
      | ~ l1_waybel_0(B_125,A_124)
      | v2_struct_0(B_125)
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_151,c_16])).

tff(c_162,plain,(
    ! [D_127,B_128,A_129] :
      ( ~ m1_subset_1(D_127,u1_struct_0(B_128))
      | ~ r2_waybel_0(A_129,B_128,k1_xboole_0)
      | ~ l1_waybel_0(B_128,A_129)
      | v2_struct_0(B_128)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_205,plain,(
    ! [A_142,B_143,A_144] :
      ( ~ r2_waybel_0(A_142,B_143,k1_xboole_0)
      | ~ l1_waybel_0(B_143,A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142)
      | ~ l1_waybel_0(B_143,A_144)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_210,plain,(
    ! [A_144] :
      ( ~ l1_waybel_0('#skF_4','#skF_3')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_144)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_133,c_205])).

tff(c_217,plain,(
    ! [A_144] :
      ( v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_144)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_44,c_36,c_210])).

tff(c_219,plain,(
    ! [A_145] :
      ( ~ l1_waybel_0('#skF_4',A_145)
      | ~ l1_struct_0(A_145)
      | v2_struct_0(A_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_46,c_217])).

tff(c_222,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_225,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.35  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.33/1.35  
% 2.33/1.35  %Foreground sorts:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Background operators:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Foreground operators:
% 2.33/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.35  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.33/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.35  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.33/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.35  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.33/1.35  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.33/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.35  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.33/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.33/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.33/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.33/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.35  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.33/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.35  
% 2.33/1.36  tff(f_130, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.33/1.36  tff(f_30, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.33/1.36  tff(f_40, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.33/1.36  tff(f_38, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.33/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.33/1.36  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.33/1.36  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.33/1.36  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 2.33/1.36  tff(f_112, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.33/1.36  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.33/1.36  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.33/1.36  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.33/1.36  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_44, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_36, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_40, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_38, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.33/1.36  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.36  tff(c_72, plain, (![B_89, A_90]: (~r1_xboole_0(B_89, A_90) | ~r1_tarski(B_89, A_90) | v1_xboole_0(B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.36  tff(c_77, plain, (![A_91, B_92]: (~r1_tarski(k4_xboole_0(A_91, B_92), B_92) | v1_xboole_0(k4_xboole_0(A_91, B_92)))), inference(resolution, [status(thm)], [c_10, c_72])).
% 2.33/1.36  tff(c_83, plain, (![A_93]: (v1_xboole_0(k4_xboole_0(A_93, A_93)))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.33/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.33/1.36  tff(c_62, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | B_86=A_87 | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.36  tff(c_65, plain, (![A_87]: (k1_xboole_0=A_87 | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_2, c_62])).
% 2.33/1.36  tff(c_89, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_65])).
% 2.33/1.36  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.36  tff(c_30, plain, (![A_67, B_71, C_73]: (r1_waybel_0(A_67, B_71, C_73) | r2_waybel_0(A_67, B_71, k6_subset_1(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.33/1.36  tff(c_121, plain, (![A_98, B_99, C_100]: (r1_waybel_0(A_98, B_99, C_100) | r2_waybel_0(A_98, B_99, k4_xboole_0(u1_struct_0(A_98), C_100)) | ~l1_waybel_0(B_99, A_98) | v2_struct_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 2.33/1.36  tff(c_126, plain, (![A_101, B_102]: (r1_waybel_0(A_101, B_102, u1_struct_0(A_101)) | r2_waybel_0(A_101, B_102, k1_xboole_0) | ~l1_waybel_0(B_102, A_101) | v2_struct_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_89, c_121])).
% 2.33/1.36  tff(c_34, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.33/1.36  tff(c_129, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_126, c_34])).
% 2.33/1.36  tff(c_132, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_129])).
% 2.33/1.36  tff(c_133, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_132])).
% 2.33/1.36  tff(c_32, plain, (![A_74, B_75]: (m1_subset_1(o_2_2_yellow_6(A_74, B_75), u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_74) | ~v7_waybel_0(B_75) | ~v4_orders_2(B_75) | v2_struct_0(B_75) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.33/1.36  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.33/1.36  tff(c_151, plain, (![A_119, B_120, C_121, D_122]: (r2_hidden(k2_waybel_0(A_119, B_120, '#skF_2'(A_119, B_120, C_121, D_122)), C_121) | ~m1_subset_1(D_122, u1_struct_0(B_120)) | ~r2_waybel_0(A_119, B_120, C_121) | ~l1_waybel_0(B_120, A_119) | v2_struct_0(B_120) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.36  tff(c_16, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.36  tff(c_156, plain, (![C_123, A_124, B_125, D_126]: (~r1_tarski(C_123, k2_waybel_0(A_124, B_125, '#skF_2'(A_124, B_125, C_123, D_126))) | ~m1_subset_1(D_126, u1_struct_0(B_125)) | ~r2_waybel_0(A_124, B_125, C_123) | ~l1_waybel_0(B_125, A_124) | v2_struct_0(B_125) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_151, c_16])).
% 2.33/1.36  tff(c_162, plain, (![D_127, B_128, A_129]: (~m1_subset_1(D_127, u1_struct_0(B_128)) | ~r2_waybel_0(A_129, B_128, k1_xboole_0) | ~l1_waybel_0(B_128, A_129) | v2_struct_0(B_128) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_4, c_156])).
% 2.33/1.36  tff(c_205, plain, (![A_142, B_143, A_144]: (~r2_waybel_0(A_142, B_143, k1_xboole_0) | ~l1_waybel_0(B_143, A_142) | ~l1_struct_0(A_142) | v2_struct_0(A_142) | ~l1_waybel_0(B_143, A_144) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_32, c_162])).
% 2.33/1.36  tff(c_210, plain, (![A_144]: (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_144) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_133, c_205])).
% 2.33/1.36  tff(c_217, plain, (![A_144]: (v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_144) | v2_struct_0('#skF_4') | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_44, c_36, c_210])).
% 2.33/1.36  tff(c_219, plain, (![A_145]: (~l1_waybel_0('#skF_4', A_145) | ~l1_struct_0(A_145) | v2_struct_0(A_145))), inference(negUnitSimplification, [status(thm)], [c_42, c_46, c_217])).
% 2.33/1.36  tff(c_222, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_219])).
% 2.33/1.36  tff(c_225, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_222])).
% 2.33/1.36  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_225])).
% 2.33/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.36  
% 2.33/1.36  Inference rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Ref     : 0
% 2.33/1.36  #Sup     : 32
% 2.33/1.36  #Fact    : 0
% 2.33/1.36  #Define  : 0
% 2.33/1.36  #Split   : 0
% 2.33/1.36  #Chain   : 0
% 2.33/1.36  #Close   : 0
% 2.33/1.36  
% 2.33/1.36  Ordering : KBO
% 2.33/1.36  
% 2.33/1.36  Simplification rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Subsume      : 6
% 2.33/1.36  #Demod        : 22
% 2.33/1.36  #Tautology    : 11
% 2.33/1.36  #SimpNegUnit  : 8
% 2.33/1.36  #BackRed      : 1
% 2.33/1.36  
% 2.33/1.36  #Partial instantiations: 0
% 2.33/1.36  #Strategies tried      : 1
% 2.33/1.36  
% 2.33/1.36  Timing (in seconds)
% 2.33/1.36  ----------------------
% 2.33/1.37  Preprocessing        : 0.34
% 2.33/1.37  Parsing              : 0.18
% 2.33/1.37  CNF conversion       : 0.03
% 2.33/1.37  Main loop            : 0.21
% 2.33/1.37  Inferencing          : 0.09
% 2.33/1.37  Reduction            : 0.06
% 2.33/1.37  Demodulation         : 0.04
% 2.33/1.37  BG Simplification    : 0.01
% 2.33/1.37  Subsumption          : 0.03
% 2.33/1.37  Abstraction          : 0.01
% 2.33/1.37  MUC search           : 0.00
% 2.33/1.37  Cooper               : 0.00
% 2.33/1.37  Total                : 0.58
% 2.33/1.37  Index Insertion      : 0.00
% 2.33/1.37  Index Deletion       : 0.00
% 2.33/1.37  Index Matching       : 0.00
% 2.33/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
