%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:01 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 115 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :   74 ( 134 expanded)
%              Number of equality atoms :   42 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_34,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    ! [A_30] : k2_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_32])).

tff(c_358,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_368,plain,(
    ! [B_54] : k4_xboole_0(B_54,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_68])).

tff(c_395,plain,(
    ! [B_54] : k4_xboole_0(B_54,k1_xboole_0) = B_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_368])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_242,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),B_47)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2861,plain,(
    ! [A_162,A_163,B_164] :
      ( ~ r2_hidden('#skF_3'(A_162,k4_xboole_0(A_163,B_164)),B_164)
      | r1_xboole_0(A_162,k4_xboole_0(A_163,B_164)) ) ),
    inference(resolution,[status(thm)],[c_242,c_6])).

tff(c_2925,plain,(
    ! [A_165,A_166] : r1_xboole_0(A_165,k4_xboole_0(A_166,A_165)) ),
    inference(resolution,[status(thm)],[c_26,c_2861])).

tff(c_403,plain,(
    ! [B_55] : k4_xboole_0(B_55,k1_xboole_0) = B_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_368])).

tff(c_138,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    ! [B_33] : k3_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_68])).

tff(c_253,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_253])).

tff(c_268,plain,(
    ! [B_33] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_253])).

tff(c_274,plain,(
    ! [B_50,B_33] : k4_xboole_0(k1_xboole_0,B_50) = k4_xboole_0(k1_xboole_0,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_268])).

tff(c_413,plain,(
    ! [B_33] : k4_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_274])).

tff(c_181,plain,(
    ! [A_43,B_44] : k4_xboole_0(k2_xboole_0(A_43,B_44),B_44) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,(
    ! [A_30] : k4_xboole_0(k1_xboole_0,A_30) = k4_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_181])).

tff(c_450,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_199])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_817,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r2_hidden('#skF_1'(A_85,B_86,C_87),B_86)
      | r2_hidden('#skF_2'(A_85,B_86,C_87),C_87)
      | k4_xboole_0(A_85,B_86) = C_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_820,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_817])).

tff(c_1995,plain,(
    ! [A_137,C_138] :
      ( r2_hidden('#skF_2'(A_137,A_137,C_138),C_138)
      | k1_xboole_0 = C_138 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_820])).

tff(c_30,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2029,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1995,c_30])).

tff(c_2980,plain,(
    ! [A_167,A_168] : k3_xboole_0(A_167,k4_xboole_0(A_168,A_167)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2925,c_2029])).

tff(c_3006,plain,(
    ! [A_167,A_168] : k4_xboole_0(A_167,k4_xboole_0(A_168,A_167)) = k4_xboole_0(A_167,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2980,c_40])).

tff(c_3064,plain,(
    ! [A_167,A_168] : k4_xboole_0(A_167,k4_xboole_0(A_168,A_167)) = A_167 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_3006])).

tff(c_38,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_364,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(B_54,A_53)) = k4_xboole_0(A_53,k4_xboole_0(B_54,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_38])).

tff(c_6034,plain,(
    ! [A_228,B_229] : k4_xboole_0(k2_xboole_0(A_228,B_229),k4_xboole_0(B_229,A_228)) = A_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_364])).

tff(c_6223,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26,B_27),A_26),k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6034])).

tff(c_6284,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2,c_6223])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6284,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.29  
% 6.42/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.30  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.42/2.30  
% 6.42/2.30  %Foreground sorts:
% 6.42/2.30  
% 6.42/2.30  
% 6.42/2.30  %Background operators:
% 6.42/2.30  
% 6.42/2.30  
% 6.42/2.30  %Foreground operators:
% 6.42/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.42/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.42/2.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.42/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.42/2.30  tff('#skF_6', type, '#skF_6': $i).
% 6.42/2.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.42/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.42/2.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.42/2.30  
% 6.42/2.31  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.42/2.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.42/2.31  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.42/2.31  tff(f_71, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.42/2.31  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.42/2.31  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.42/2.31  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.42/2.31  tff(f_77, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.42/2.31  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.42/2.31  tff(f_82, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.42/2.31  tff(c_34, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k3_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.42/2.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.42/2.31  tff(c_40, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.42/2.31  tff(c_52, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.42/2.31  tff(c_32, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.42/2.31  tff(c_68, plain, (![A_30]: (k2_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_52, c_32])).
% 6.42/2.31  tff(c_358, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.31  tff(c_368, plain, (![B_54]: (k4_xboole_0(B_54, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_54))), inference(superposition, [status(thm), theory('equality')], [c_358, c_68])).
% 6.42/2.31  tff(c_395, plain, (![B_54]: (k4_xboole_0(B_54, k1_xboole_0)=B_54)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_368])).
% 6.42/2.31  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.42/2.31  tff(c_242, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), B_47) | r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.42/2.31  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.42/2.31  tff(c_2861, plain, (![A_162, A_163, B_164]: (~r2_hidden('#skF_3'(A_162, k4_xboole_0(A_163, B_164)), B_164) | r1_xboole_0(A_162, k4_xboole_0(A_163, B_164)))), inference(resolution, [status(thm)], [c_242, c_6])).
% 6.42/2.31  tff(c_2925, plain, (![A_165, A_166]: (r1_xboole_0(A_165, k4_xboole_0(A_166, A_165)))), inference(resolution, [status(thm)], [c_26, c_2861])).
% 6.42/2.31  tff(c_403, plain, (![B_55]: (k4_xboole_0(B_55, k1_xboole_0)=B_55)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_368])).
% 6.42/2.31  tff(c_138, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k3_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.42/2.31  tff(c_145, plain, (![B_33]: (k3_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_68])).
% 6.42/2.31  tff(c_253, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.42/2.31  tff(c_271, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_50))), inference(superposition, [status(thm), theory('equality')], [c_145, c_253])).
% 6.42/2.31  tff(c_268, plain, (![B_33]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_33))), inference(superposition, [status(thm), theory('equality')], [c_145, c_253])).
% 6.42/2.31  tff(c_274, plain, (![B_50, B_33]: (k4_xboole_0(k1_xboole_0, B_50)=k4_xboole_0(k1_xboole_0, B_33))), inference(superposition, [status(thm), theory('equality')], [c_271, c_268])).
% 6.42/2.31  tff(c_413, plain, (![B_33]: (k4_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_403, c_274])).
% 6.42/2.31  tff(c_181, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), B_44)=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.42/2.31  tff(c_199, plain, (![A_30]: (k4_xboole_0(k1_xboole_0, A_30)=k4_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_68, c_181])).
% 6.42/2.31  tff(c_450, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_413, c_199])).
% 6.42/2.31  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.42/2.31  tff(c_817, plain, (![A_85, B_86, C_87]: (~r2_hidden('#skF_1'(A_85, B_86, C_87), B_86) | r2_hidden('#skF_2'(A_85, B_86, C_87), C_87) | k4_xboole_0(A_85, B_86)=C_87)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.42/2.31  tff(c_820, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_817])).
% 6.42/2.31  tff(c_1995, plain, (![A_137, C_138]: (r2_hidden('#skF_2'(A_137, A_137, C_138), C_138) | k1_xboole_0=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_450, c_820])).
% 6.42/2.31  tff(c_30, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.42/2.31  tff(c_2029, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1995, c_30])).
% 6.42/2.31  tff(c_2980, plain, (![A_167, A_168]: (k3_xboole_0(A_167, k4_xboole_0(A_168, A_167))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2925, c_2029])).
% 6.42/2.31  tff(c_3006, plain, (![A_167, A_168]: (k4_xboole_0(A_167, k4_xboole_0(A_168, A_167))=k4_xboole_0(A_167, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2980, c_40])).
% 6.42/2.31  tff(c_3064, plain, (![A_167, A_168]: (k4_xboole_0(A_167, k4_xboole_0(A_168, A_167))=A_167)), inference(demodulation, [status(thm), theory('equality')], [c_395, c_3006])).
% 6.42/2.31  tff(c_38, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.42/2.31  tff(c_364, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(B_54, A_53))=k4_xboole_0(A_53, k4_xboole_0(B_54, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_358, c_38])).
% 6.42/2.31  tff(c_6034, plain, (![A_228, B_229]: (k4_xboole_0(k2_xboole_0(A_228, B_229), k4_xboole_0(B_229, A_228))=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_364])).
% 6.42/2.31  tff(c_6223, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26, B_27), A_26), k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6034])).
% 6.42/2.31  tff(c_6284, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2, c_6223])).
% 6.42/2.31  tff(c_42, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.42/2.31  tff(c_10292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6284, c_42])).
% 6.42/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.31  
% 6.42/2.31  Inference rules
% 6.42/2.31  ----------------------
% 6.42/2.31  #Ref     : 0
% 6.42/2.31  #Sup     : 2591
% 6.42/2.31  #Fact    : 0
% 6.42/2.31  #Define  : 0
% 6.42/2.31  #Split   : 1
% 6.42/2.31  #Chain   : 0
% 6.42/2.31  #Close   : 0
% 6.42/2.31  
% 6.42/2.31  Ordering : KBO
% 6.42/2.31  
% 6.42/2.31  Simplification rules
% 6.42/2.31  ----------------------
% 6.42/2.31  #Subsume      : 323
% 6.42/2.31  #Demod        : 2412
% 6.42/2.31  #Tautology    : 1681
% 6.42/2.31  #SimpNegUnit  : 47
% 6.42/2.31  #BackRed      : 6
% 6.42/2.31  
% 6.42/2.31  #Partial instantiations: 0
% 6.42/2.31  #Strategies tried      : 1
% 6.42/2.31  
% 6.42/2.31  Timing (in seconds)
% 6.42/2.31  ----------------------
% 6.42/2.31  Preprocessing        : 0.29
% 6.42/2.31  Parsing              : 0.16
% 6.42/2.31  CNF conversion       : 0.02
% 6.42/2.31  Main loop            : 1.25
% 6.42/2.31  Inferencing          : 0.38
% 6.42/2.31  Reduction            : 0.52
% 6.42/2.31  Demodulation         : 0.43
% 6.42/2.31  BG Simplification    : 0.04
% 6.42/2.31  Subsumption          : 0.23
% 6.42/2.31  Abstraction          : 0.06
% 6.42/2.31  MUC search           : 0.00
% 6.42/2.31  Cooper               : 0.00
% 6.42/2.31  Total                : 1.58
% 6.42/2.31  Index Insertion      : 0.00
% 6.42/2.31  Index Deletion       : 0.00
% 6.42/2.31  Index Matching       : 0.00
% 6.42/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
