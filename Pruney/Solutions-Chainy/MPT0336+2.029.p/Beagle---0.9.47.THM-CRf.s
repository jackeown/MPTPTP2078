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
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 109 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 136 expanded)
%              Number of equality atoms :   44 (  63 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_72,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_216,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_336,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_32])).

tff(c_339,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_336])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_745,plain,(
    ! [B_106,A_107] :
      ( k1_tarski(B_106) = A_107
      | k1_xboole_0 = A_107
      | ~ r1_tarski(A_107,k1_tarski(B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_756,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_745])).

tff(c_1119,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_357,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_390,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_357])).

tff(c_1134,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_390])).

tff(c_1142,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1134])).

tff(c_26,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1163,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_26])).

tff(c_70,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_139,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_139])).

tff(c_1211,plain,(
    ! [A_127,B_128,C_129] :
      ( k3_xboole_0(A_127,k2_xboole_0(B_128,C_129)) = k3_xboole_0(A_127,C_129)
      | ~ r1_xboole_0(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [A_62,B_63] :
      ( r1_xboole_0(A_62,B_63)
      | k3_xboole_0(A_62,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_136,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_68])).

tff(c_138,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_1254,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_138])).

tff(c_1300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_151,c_2,c_1254])).

tff(c_1301,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_20,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_234,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_246,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_835,plain,(
    ! [A_115,B_116,C_117] : k3_xboole_0(k3_xboole_0(A_115,B_116),C_117) = k3_xboole_0(A_115,k3_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_908,plain,(
    ! [C_117] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_117)) = k3_xboole_0(k1_xboole_0,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_835])).

tff(c_937,plain,(
    ! [C_118] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_118)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_908])).

tff(c_14,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_948,plain,(
    ! [C_118] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_118)) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_14])).

tff(c_975,plain,(
    ! [C_119] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_119)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_948])).

tff(c_1021,plain,(
    ! [C_120] : r1_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_26])).

tff(c_1042,plain,(
    ! [A_1] : r1_xboole_0('#skF_6',k3_xboole_0(A_1,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1021])).

tff(c_1312,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_1042])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3836,plain,(
    ! [C_3703] :
      ( ~ r2_hidden(C_3703,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_3703,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1312,c_8])).

tff(c_3848,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_339,c_3836])).

tff(c_3854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.94  
% 4.71/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.71/1.94  
% 4.71/1.94  %Foreground sorts:
% 4.71/1.94  
% 4.71/1.94  
% 4.71/1.94  %Background operators:
% 4.71/1.94  
% 4.71/1.94  
% 4.71/1.94  %Foreground operators:
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.71/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.94  tff('#skF_7', type, '#skF_7': $i).
% 4.71/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.71/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.71/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.71/1.94  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.71/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.71/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/1.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.71/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.71/1.94  
% 4.71/1.95  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.71/1.95  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.71/1.95  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.71/1.95  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.71/1.95  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.71/1.95  tff(f_96, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.71/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.71/1.95  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.71/1.95  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.71/1.95  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.71/1.95  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.71/1.95  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.71/1.95  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.71/1.95  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.71/1.95  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.71/1.95  tff(c_72, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.71/1.95  tff(c_52, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.71/1.95  tff(c_216, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.71/1.95  tff(c_32, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.71/1.95  tff(c_336, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_32])).
% 4.71/1.95  tff(c_339, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_336])).
% 4.71/1.95  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.71/1.95  tff(c_74, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.71/1.95  tff(c_745, plain, (![B_106, A_107]: (k1_tarski(B_106)=A_107 | k1_xboole_0=A_107 | ~r1_tarski(A_107, k1_tarski(B_106)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.71/1.95  tff(c_756, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_745])).
% 4.71/1.95  tff(c_1119, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_756])).
% 4.71/1.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.71/1.95  tff(c_357, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.71/1.95  tff(c_390, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_357])).
% 4.71/1.95  tff(c_1134, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1119, c_390])).
% 4.71/1.95  tff(c_1142, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1134])).
% 4.71/1.95  tff(c_26, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.71/1.95  tff(c_1163, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1142, c_26])).
% 4.71/1.95  tff(c_70, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.71/1.95  tff(c_139, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.95  tff(c_151, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_139])).
% 4.71/1.95  tff(c_1211, plain, (![A_127, B_128, C_129]: (k3_xboole_0(A_127, k2_xboole_0(B_128, C_129))=k3_xboole_0(A_127, C_129) | ~r1_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.71/1.95  tff(c_133, plain, (![A_62, B_63]: (r1_xboole_0(A_62, B_63) | k3_xboole_0(A_62, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.95  tff(c_68, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.71/1.95  tff(c_136, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_68])).
% 4.71/1.95  tff(c_138, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_136])).
% 4.71/1.95  tff(c_1254, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_138])).
% 4.71/1.95  tff(c_1300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1163, c_151, c_2, c_1254])).
% 4.71/1.95  tff(c_1301, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_756])).
% 4.71/1.95  tff(c_20, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.71/1.95  tff(c_234, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.71/1.95  tff(c_246, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_234])).
% 4.71/1.95  tff(c_835, plain, (![A_115, B_116, C_117]: (k3_xboole_0(k3_xboole_0(A_115, B_116), C_117)=k3_xboole_0(A_115, k3_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.71/1.95  tff(c_908, plain, (![C_117]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_117))=k3_xboole_0(k1_xboole_0, C_117))), inference(superposition, [status(thm), theory('equality')], [c_151, c_835])).
% 4.71/1.95  tff(c_937, plain, (![C_118]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_118))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_246, c_908])).
% 4.71/1.95  tff(c_14, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.71/1.95  tff(c_948, plain, (![C_118]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_118))=k5_xboole_0('#skF_6', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_937, c_14])).
% 4.71/1.95  tff(c_975, plain, (![C_119]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_119))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_948])).
% 4.71/1.95  tff(c_1021, plain, (![C_120]: (r1_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_120)))), inference(superposition, [status(thm), theory('equality')], [c_975, c_26])).
% 4.71/1.95  tff(c_1042, plain, (![A_1]: (r1_xboole_0('#skF_6', k3_xboole_0(A_1, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1021])).
% 4.71/1.95  tff(c_1312, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1301, c_1042])).
% 4.71/1.95  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/1.95  tff(c_3836, plain, (![C_3703]: (~r2_hidden(C_3703, k1_tarski('#skF_7')) | ~r2_hidden(C_3703, '#skF_6'))), inference(resolution, [status(thm)], [c_1312, c_8])).
% 4.71/1.95  tff(c_3848, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_339, c_3836])).
% 4.71/1.95  tff(c_3854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3848])).
% 4.71/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.95  
% 4.71/1.95  Inference rules
% 4.71/1.95  ----------------------
% 4.71/1.95  #Ref     : 0
% 4.71/1.95  #Sup     : 846
% 4.71/1.95  #Fact    : 6
% 4.71/1.95  #Define  : 0
% 4.71/1.95  #Split   : 1
% 4.71/1.95  #Chain   : 0
% 4.71/1.95  #Close   : 0
% 4.71/1.95  
% 4.71/1.95  Ordering : KBO
% 4.71/1.95  
% 4.71/1.95  Simplification rules
% 4.71/1.95  ----------------------
% 4.71/1.95  #Subsume      : 22
% 4.71/1.95  #Demod        : 595
% 4.71/1.95  #Tautology    : 562
% 4.71/1.95  #SimpNegUnit  : 3
% 4.71/1.95  #BackRed      : 9
% 4.71/1.95  
% 4.71/1.95  #Partial instantiations: 1854
% 4.71/1.95  #Strategies tried      : 1
% 4.71/1.95  
% 4.71/1.95  Timing (in seconds)
% 4.71/1.95  ----------------------
% 4.71/1.96  Preprocessing        : 0.34
% 4.71/1.96  Parsing              : 0.18
% 4.71/1.96  CNF conversion       : 0.02
% 4.71/1.96  Main loop            : 0.77
% 4.71/1.96  Inferencing          : 0.29
% 4.71/1.96  Reduction            : 0.29
% 4.71/1.96  Demodulation         : 0.23
% 4.71/1.96  BG Simplification    : 0.03
% 4.71/1.96  Subsumption          : 0.12
% 4.71/1.96  Abstraction          : 0.03
% 4.71/1.96  MUC search           : 0.00
% 4.71/1.96  Cooper               : 0.00
% 4.71/1.96  Total                : 1.14
% 4.71/1.96  Index Insertion      : 0.00
% 4.71/1.96  Index Deletion       : 0.00
% 4.71/1.96  Index Matching       : 0.00
% 4.71/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
