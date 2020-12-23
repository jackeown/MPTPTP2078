%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 136 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 ( 382 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_53,A_54] :
      ( ~ r1_tarski(B_53,A_54)
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [A_57] :
      ( ~ r1_tarski(A_57,'#skF_1'(A_57))
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_179,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_182,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_179])).

tff(c_185,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_182])).

tff(c_186,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,k3_tarski(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_162,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_3'(A_74),B_75)
      | ~ r1_tarski(A_74,B_75)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | ~ r1_tarski(A_79,B_78)
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_205,plain,(
    ! [B_80,A_81] :
      ( ~ v1_xboole_0(k3_tarski(B_80))
      | k1_xboole_0 = A_81
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_207,plain,(
    ! [A_81] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = A_81
      | ~ r2_hidden(A_81,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_205])).

tff(c_210,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ r2_hidden(A_82,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_207])).

tff(c_226,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_232,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_226])).

tff(c_239,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_243,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_239])).

tff(c_313,plain,(
    ! [D_86,A_87,B_88] :
      ( m2_orders_2(D_86,A_87,B_88)
      | ~ r2_hidden(D_86,k4_orders_2(A_87,B_88))
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_318,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_243,c_313])).

tff(c_334,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_318])).

tff(c_335,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_334])).

tff(c_579,plain,(
    ! [B_109,A_110,C_111] :
      ( r2_hidden(k1_funct_1(B_109,u1_struct_0(A_110)),C_111)
      | ~ m2_orders_2(C_111,A_110,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1561,plain,(
    ! [C_165,A_166,B_167] :
      ( ~ v1_xboole_0(C_165)
      | ~ m2_orders_2(C_165,A_166,B_167)
      | ~ m1_orders_1(B_167,k1_orders_1(u1_struct_0(A_166)))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166)
      | ~ v4_orders_2(A_166)
      | ~ v3_orders_2(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_579,c_2])).

tff(c_1567,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_335,c_1561])).

tff(c_1578,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_80,c_1567])).

tff(c_1580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.49  
% 3.36/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.49  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2
% 3.36/1.49  
% 3.36/1.49  %Foreground sorts:
% 3.36/1.49  
% 3.36/1.49  
% 3.36/1.49  %Background operators:
% 3.36/1.49  
% 3.36/1.49  
% 3.36/1.49  %Foreground operators:
% 3.36/1.49  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 3.36/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.36/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.49  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.36/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.36/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.49  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.36/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.36/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.36/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.36/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.36/1.49  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.36/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.49  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.36/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.49  
% 3.36/1.51  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 3.36/1.51  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.36/1.51  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.36/1.51  tff(f_95, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 3.36/1.51  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.36/1.51  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.36/1.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.36/1.51  tff(f_79, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 3.36/1.51  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 3.36/1.51  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_46, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_44, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_42, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_40, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_38, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.36/1.51  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.36/1.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.51  tff(c_60, plain, (![B_53, A_54]: (~r1_tarski(B_53, A_54) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.51/1.51  tff(c_75, plain, (![A_57]: (~r1_tarski(A_57, '#skF_1'(A_57)) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_4, c_60])).
% 3.51/1.51  tff(c_80, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_75])).
% 3.51/1.51  tff(c_179, plain, (![A_76, B_77]: (~v1_xboole_0(k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.51/1.51  tff(c_182, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_179])).
% 3.51/1.51  tff(c_185, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_182])).
% 3.51/1.51  tff(c_186, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_48, c_185])).
% 3.51/1.51  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.51/1.51  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k3_tarski(B_14)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.51/1.51  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.51/1.51  tff(c_152, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.51/1.51  tff(c_162, plain, (![A_74, B_75]: (r2_hidden('#skF_3'(A_74), B_75) | ~r1_tarski(A_74, B_75) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_12, c_152])).
% 3.51/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.51  tff(c_187, plain, (![B_78, A_79]: (~v1_xboole_0(B_78) | ~r1_tarski(A_79, B_78) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_162, c_2])).
% 3.51/1.51  tff(c_205, plain, (![B_80, A_81]: (~v1_xboole_0(k3_tarski(B_80)) | k1_xboole_0=A_81 | ~r2_hidden(A_81, B_80))), inference(resolution, [status(thm)], [c_16, c_187])).
% 3.51/1.51  tff(c_207, plain, (![A_81]: (~v1_xboole_0(k1_xboole_0) | k1_xboole_0=A_81 | ~r2_hidden(A_81, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_205])).
% 3.51/1.51  tff(c_210, plain, (![A_82]: (k1_xboole_0=A_82 | ~r2_hidden(A_82, k4_orders_2('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_207])).
% 3.51/1.51  tff(c_226, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_210])).
% 3.51/1.51  tff(c_232, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_186, c_226])).
% 3.51/1.51  tff(c_239, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 3.51/1.51  tff(c_243, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_186, c_239])).
% 3.51/1.51  tff(c_313, plain, (![D_86, A_87, B_88]: (m2_orders_2(D_86, A_87, B_88) | ~r2_hidden(D_86, k4_orders_2(A_87, B_88)) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.51/1.51  tff(c_318, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_243, c_313])).
% 3.51/1.51  tff(c_334, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_318])).
% 3.51/1.51  tff(c_335, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_48, c_334])).
% 3.51/1.51  tff(c_579, plain, (![B_109, A_110, C_111]: (r2_hidden(k1_funct_1(B_109, u1_struct_0(A_110)), C_111) | ~m2_orders_2(C_111, A_110, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.51/1.51  tff(c_1561, plain, (![C_165, A_166, B_167]: (~v1_xboole_0(C_165) | ~m2_orders_2(C_165, A_166, B_167) | ~m1_orders_1(B_167, k1_orders_1(u1_struct_0(A_166))) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166) | ~v4_orders_2(A_166) | ~v3_orders_2(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_579, c_2])).
% 3.51/1.51  tff(c_1567, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_335, c_1561])).
% 3.51/1.51  tff(c_1578, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_80, c_1567])).
% 3.51/1.51  tff(c_1580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1578])).
% 3.51/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.51  
% 3.51/1.51  Inference rules
% 3.51/1.51  ----------------------
% 3.51/1.51  #Ref     : 0
% 3.51/1.51  #Sup     : 315
% 3.51/1.51  #Fact    : 0
% 3.51/1.51  #Define  : 0
% 3.51/1.51  #Split   : 1
% 3.51/1.51  #Chain   : 0
% 3.51/1.51  #Close   : 0
% 3.51/1.51  
% 3.51/1.51  Ordering : KBO
% 3.51/1.51  
% 3.51/1.51  Simplification rules
% 3.51/1.51  ----------------------
% 3.51/1.51  #Subsume      : 94
% 3.51/1.51  #Demod        : 141
% 3.51/1.51  #Tautology    : 108
% 3.51/1.51  #SimpNegUnit  : 50
% 3.51/1.51  #BackRed      : 13
% 3.51/1.51  
% 3.51/1.51  #Partial instantiations: 0
% 3.51/1.51  #Strategies tried      : 1
% 3.51/1.51  
% 3.51/1.51  Timing (in seconds)
% 3.51/1.51  ----------------------
% 3.51/1.51  Preprocessing        : 0.31
% 3.51/1.51  Parsing              : 0.17
% 3.51/1.51  CNF conversion       : 0.03
% 3.51/1.51  Main loop            : 0.46
% 3.51/1.51  Inferencing          : 0.17
% 3.51/1.51  Reduction            : 0.14
% 3.51/1.51  Demodulation         : 0.09
% 3.51/1.51  BG Simplification    : 0.02
% 3.51/1.51  Subsumption          : 0.10
% 3.51/1.51  Abstraction          : 0.02
% 3.51/1.51  MUC search           : 0.00
% 3.51/1.51  Cooper               : 0.00
% 3.51/1.51  Total                : 0.80
% 3.51/1.51  Index Insertion      : 0.00
% 3.51/1.51  Index Deletion       : 0.00
% 3.51/1.51  Index Matching       : 0.00
% 3.51/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
