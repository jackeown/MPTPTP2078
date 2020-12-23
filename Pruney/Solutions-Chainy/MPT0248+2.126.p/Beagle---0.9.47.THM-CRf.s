%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 256 expanded)
%              Number of equality atoms :   55 ( 204 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_76,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_99,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109,plain,(
    ! [A_63,B_64] : r1_tarski(A_63,k2_xboole_0(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_109])).

tff(c_494,plain,(
    ! [B_112,A_113] :
      ( k1_tarski(B_112) = A_113
      | k1_xboole_0 = A_113
      | ~ r1_tarski(A_113,k1_tarski(B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_497,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_112,c_494])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_99,c_497])).

tff(c_510,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_543,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_78])).

tff(c_509,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_526,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_80])).

tff(c_719,plain,(
    ! [D_130,B_131,A_132] :
      ( ~ r2_hidden(D_130,B_131)
      | r2_hidden(D_130,k2_xboole_0(A_132,B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_740,plain,(
    ! [D_130] :
      ( ~ r2_hidden(D_130,'#skF_8')
      | r2_hidden(D_130,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_719])).

tff(c_46,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1014,plain,(
    ! [D_172,B_173,A_174] :
      ( D_172 = B_173
      | D_172 = A_174
      | ~ r2_hidden(D_172,k2_tarski(A_174,B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1038,plain,(
    ! [D_175,A_176] :
      ( D_175 = A_176
      | D_175 = A_176
      | ~ r2_hidden(D_175,k1_tarski(A_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1014])).

tff(c_1092,plain,(
    ! [D_179] :
      ( D_179 = '#skF_6'
      | D_179 = '#skF_6'
      | ~ r2_hidden(D_179,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_1038])).

tff(c_1117,plain,(
    ! [D_180] :
      ( D_180 = '#skF_6'
      | ~ r2_hidden(D_180,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_740,c_1092])).

tff(c_1125,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_1117])).

tff(c_1130,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_1125])).

tff(c_1134,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_20])).

tff(c_1137,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_1134])).

tff(c_1144,plain,(
    ! [A_181,B_182,C_183] :
      ( r1_tarski(k2_tarski(A_181,B_182),C_183)
      | ~ r2_hidden(B_182,C_183)
      | ~ r2_hidden(A_181,C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1426,plain,(
    ! [A_189,C_190] :
      ( r1_tarski(k1_tarski(A_189),C_190)
      | ~ r2_hidden(A_189,C_190)
      | ~ r2_hidden(A_189,C_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1144])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1448,plain,(
    ! [A_191,C_192] :
      ( k2_xboole_0(k1_tarski(A_191),C_192) = C_192
      | ~ r2_hidden(A_191,C_192) ) ),
    inference(resolution,[status(thm)],[c_1426,c_22])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1557,plain,(
    ! [A_193,C_194] :
      ( r1_tarski(k1_tarski(A_193),C_194)
      | ~ r2_hidden(A_193,C_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_26])).

tff(c_1588,plain,(
    ! [C_199] :
      ( r1_tarski('#skF_7',C_199)
      | ~ r2_hidden('#skF_6',C_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_1557])).

tff(c_1653,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1137,c_1588])).

tff(c_1679,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1653,c_22])).

tff(c_1680,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_526])).

tff(c_1682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_1680])).

tff(c_1683,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1684,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_24,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1689,plain,(
    ! [A_11] : r1_tarski('#skF_7',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1684,c_24])).

tff(c_1770,plain,(
    ! [A_217,B_218] :
      ( k2_xboole_0(A_217,B_218) = B_218
      | ~ r1_tarski(A_217,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1786,plain,(
    ! [A_11] : k2_xboole_0('#skF_7',A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_1689,c_1770])).

tff(c_1787,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_80])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1683,c_1787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n025.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 09:52:50 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 3.33/1.54  
% 3.33/1.54  %Foreground sorts:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Background operators:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Foreground operators:
% 3.33/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.33/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.33/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.33/1.54  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.54  
% 3.33/1.56  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.33/1.56  tff(f_50, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.33/1.56  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.33/1.56  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.33/1.56  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.33/1.56  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.33/1.56  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.33/1.56  tff(f_87, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.33/1.56  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.33/1.56  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.33/1.56  tff(c_76, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.33/1.56  tff(c_83, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_76])).
% 3.33/1.56  tff(c_74, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.33/1.56  tff(c_99, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 3.33/1.56  tff(c_80, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.33/1.56  tff(c_109, plain, (![A_63, B_64]: (r1_tarski(A_63, k2_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.56  tff(c_112, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_109])).
% 3.33/1.56  tff(c_494, plain, (![B_112, A_113]: (k1_tarski(B_112)=A_113 | k1_xboole_0=A_113 | ~r1_tarski(A_113, k1_tarski(B_112)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.33/1.56  tff(c_497, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_112, c_494])).
% 3.33/1.56  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_99, c_497])).
% 3.33/1.56  tff(c_510, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 3.33/1.56  tff(c_78, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.33/1.56  tff(c_543, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_78])).
% 3.33/1.56  tff(c_509, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 3.33/1.56  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.33/1.56  tff(c_526, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_80])).
% 3.33/1.56  tff(c_719, plain, (![D_130, B_131, A_132]: (~r2_hidden(D_130, B_131) | r2_hidden(D_130, k2_xboole_0(A_132, B_131)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.56  tff(c_740, plain, (![D_130]: (~r2_hidden(D_130, '#skF_8') | r2_hidden(D_130, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_719])).
% 3.33/1.56  tff(c_46, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.56  tff(c_1014, plain, (![D_172, B_173, A_174]: (D_172=B_173 | D_172=A_174 | ~r2_hidden(D_172, k2_tarski(A_174, B_173)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.33/1.56  tff(c_1038, plain, (![D_175, A_176]: (D_175=A_176 | D_175=A_176 | ~r2_hidden(D_175, k1_tarski(A_176)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1014])).
% 3.33/1.56  tff(c_1092, plain, (![D_179]: (D_179='#skF_6' | D_179='#skF_6' | ~r2_hidden(D_179, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_510, c_1038])).
% 3.33/1.56  tff(c_1117, plain, (![D_180]: (D_180='#skF_6' | ~r2_hidden(D_180, '#skF_8'))), inference(resolution, [status(thm)], [c_740, c_1092])).
% 3.33/1.56  tff(c_1125, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_1117])).
% 3.33/1.56  tff(c_1130, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_509, c_1125])).
% 3.33/1.56  tff(c_1134, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1130, c_20])).
% 3.33/1.56  tff(c_1137, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_509, c_1134])).
% 3.33/1.56  tff(c_1144, plain, (![A_181, B_182, C_183]: (r1_tarski(k2_tarski(A_181, B_182), C_183) | ~r2_hidden(B_182, C_183) | ~r2_hidden(A_181, C_183))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.33/1.56  tff(c_1426, plain, (![A_189, C_190]: (r1_tarski(k1_tarski(A_189), C_190) | ~r2_hidden(A_189, C_190) | ~r2_hidden(A_189, C_190))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1144])).
% 3.33/1.56  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.56  tff(c_1448, plain, (![A_191, C_192]: (k2_xboole_0(k1_tarski(A_191), C_192)=C_192 | ~r2_hidden(A_191, C_192))), inference(resolution, [status(thm)], [c_1426, c_22])).
% 3.33/1.56  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.56  tff(c_1557, plain, (![A_193, C_194]: (r1_tarski(k1_tarski(A_193), C_194) | ~r2_hidden(A_193, C_194))), inference(superposition, [status(thm), theory('equality')], [c_1448, c_26])).
% 3.33/1.56  tff(c_1588, plain, (![C_199]: (r1_tarski('#skF_7', C_199) | ~r2_hidden('#skF_6', C_199))), inference(superposition, [status(thm), theory('equality')], [c_510, c_1557])).
% 3.33/1.56  tff(c_1653, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_1137, c_1588])).
% 3.33/1.56  tff(c_1679, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1653, c_22])).
% 3.33/1.56  tff(c_1680, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_526])).
% 3.33/1.56  tff(c_1682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_1680])).
% 3.33/1.56  tff(c_1683, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_76])).
% 3.33/1.56  tff(c_1684, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 3.33/1.56  tff(c_24, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.56  tff(c_1689, plain, (![A_11]: (r1_tarski('#skF_7', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_1684, c_24])).
% 3.33/1.56  tff(c_1770, plain, (![A_217, B_218]: (k2_xboole_0(A_217, B_218)=B_218 | ~r1_tarski(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.56  tff(c_1786, plain, (![A_11]: (k2_xboole_0('#skF_7', A_11)=A_11)), inference(resolution, [status(thm)], [c_1689, c_1770])).
% 3.33/1.56  tff(c_1787, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_80])).
% 3.33/1.56  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1683, c_1787])).
% 3.33/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.56  
% 3.33/1.56  Inference rules
% 3.33/1.56  ----------------------
% 3.33/1.56  #Ref     : 0
% 3.33/1.56  #Sup     : 394
% 3.33/1.56  #Fact    : 0
% 3.33/1.56  #Define  : 0
% 3.33/1.56  #Split   : 4
% 3.33/1.56  #Chain   : 0
% 3.33/1.56  #Close   : 0
% 3.33/1.56  
% 3.33/1.56  Ordering : KBO
% 3.33/1.56  
% 3.33/1.56  Simplification rules
% 3.33/1.56  ----------------------
% 3.33/1.56  #Subsume      : 26
% 3.33/1.56  #Demod        : 253
% 3.33/1.56  #Tautology    : 269
% 3.33/1.56  #SimpNegUnit  : 10
% 3.33/1.56  #BackRed      : 3
% 3.33/1.56  
% 3.33/1.56  #Partial instantiations: 0
% 3.33/1.56  #Strategies tried      : 1
% 3.33/1.56  
% 3.33/1.56  Timing (in seconds)
% 3.33/1.56  ----------------------
% 3.33/1.56  Preprocessing        : 0.36
% 3.33/1.56  Parsing              : 0.18
% 3.33/1.56  CNF conversion       : 0.03
% 3.33/1.56  Main loop            : 0.46
% 3.33/1.56  Inferencing          : 0.17
% 3.33/1.56  Reduction            : 0.16
% 3.33/1.56  Demodulation         : 0.12
% 3.33/1.56  BG Simplification    : 0.02
% 3.33/1.56  Subsumption          : 0.07
% 3.33/1.56  Abstraction          : 0.02
% 3.33/1.56  MUC search           : 0.00
% 3.33/1.56  Cooper               : 0.00
% 3.33/1.56  Total                : 0.85
% 3.33/1.56  Index Insertion      : 0.00
% 3.33/1.56  Index Deletion       : 0.00
% 3.33/1.56  Index Matching       : 0.00
% 3.33/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
