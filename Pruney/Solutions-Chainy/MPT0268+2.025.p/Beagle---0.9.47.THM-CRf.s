%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   76 (  95 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 119 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_160,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),B_69)
      | r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_294,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(k1_tarski(A_89),B_90) = k1_xboole_0
      | r2_hidden(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_215,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_300,plain,(
    ! [B_90,A_89] :
      ( k4_xboole_0(B_90,k1_tarski(A_89)) = k5_xboole_0(B_90,k1_xboole_0)
      | r2_hidden(A_89,B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_215])).

tff(c_385,plain,(
    ! [B_96,A_97] :
      ( k4_xboole_0(B_96,k1_tarski(A_97)) = B_96
      | r2_hidden(A_97,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_300])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_404,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_185])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_404])).

tff(c_428,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_44,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_167,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [E_21,A_15,C_17] : r2_hidden(E_21,k1_enumset1(A_15,E_21,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_466,plain,(
    ! [A_98,B_99] : r2_hidden(A_98,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_24])).

tff(c_469,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_466])).

tff(c_429,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_444,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_62])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_454,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_18])).

tff(c_788,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_813,plain,(
    ! [C_120] :
      ( ~ r2_hidden(C_120,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_120,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_454,c_788])).

tff(c_825,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_469,c_813])).

tff(c_831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_825])).

tff(c_832,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_955,plain,(
    ! [A_140,B_141] : k1_enumset1(A_140,A_140,B_141) = k2_tarski(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_973,plain,(
    ! [A_142,B_143] : r2_hidden(A_142,k2_tarski(A_142,B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_24])).

tff(c_976,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_973])).

tff(c_833,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_911,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_64])).

tff(c_921,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_18])).

tff(c_1240,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ r1_xboole_0(A_165,B_166)
      | ~ r2_hidden(C_167,B_166)
      | ~ r2_hidden(C_167,A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1259,plain,(
    ! [C_168] :
      ( ~ r2_hidden(C_168,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_168,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_921,c_1240])).

tff(c_1271,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_976,c_1259])).

tff(c_1277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_1271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.75/1.45  
% 2.75/1.45  %Foreground sorts:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Background operators:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Foreground operators:
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.75/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.75/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.45  
% 3.00/1.47  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.00/1.47  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.00/1.47  tff(f_87, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.00/1.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.00/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.47  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.47  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.00/1.47  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.00/1.47  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.00/1.47  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.00/1.47  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.00/1.47  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.00/1.47  tff(c_84, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.00/1.47  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.47  tff(c_160, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), B_69) | r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.47  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.47  tff(c_294, plain, (![A_89, B_90]: (k3_xboole_0(k1_tarski(A_89), B_90)=k1_xboole_0 | r2_hidden(A_89, B_90))), inference(resolution, [status(thm)], [c_160, c_4])).
% 3.00/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.47  tff(c_197, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.47  tff(c_215, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 3.00/1.47  tff(c_300, plain, (![B_90, A_89]: (k4_xboole_0(B_90, k1_tarski(A_89))=k5_xboole_0(B_90, k1_xboole_0) | r2_hidden(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_294, c_215])).
% 3.00/1.47  tff(c_385, plain, (![B_96, A_97]: (k4_xboole_0(B_96, k1_tarski(A_97))=B_96 | r2_hidden(A_97, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_300])).
% 3.00/1.47  tff(c_58, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.00/1.47  tff(c_185, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 3.00/1.47  tff(c_404, plain, (r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_385, c_185])).
% 3.00/1.47  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_404])).
% 3.00/1.47  tff(c_428, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 3.00/1.47  tff(c_44, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.00/1.47  tff(c_167, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.47  tff(c_24, plain, (![E_21, A_15, C_17]: (r2_hidden(E_21, k1_enumset1(A_15, E_21, C_17)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.47  tff(c_466, plain, (![A_98, B_99]: (r2_hidden(A_98, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_24])).
% 3.00/1.47  tff(c_469, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_466])).
% 3.00/1.47  tff(c_429, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.00/1.47  tff(c_62, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.00/1.47  tff(c_444, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_62])).
% 3.00/1.47  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.47  tff(c_454, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_18])).
% 3.00/1.47  tff(c_788, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.47  tff(c_813, plain, (![C_120]: (~r2_hidden(C_120, k1_tarski('#skF_7')) | ~r2_hidden(C_120, '#skF_6'))), inference(resolution, [status(thm)], [c_454, c_788])).
% 3.00/1.47  tff(c_825, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_469, c_813])).
% 3.00/1.47  tff(c_831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_428, c_825])).
% 3.00/1.47  tff(c_832, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 3.00/1.47  tff(c_955, plain, (![A_140, B_141]: (k1_enumset1(A_140, A_140, B_141)=k2_tarski(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.47  tff(c_973, plain, (![A_142, B_143]: (r2_hidden(A_142, k2_tarski(A_142, B_143)))), inference(superposition, [status(thm), theory('equality')], [c_955, c_24])).
% 3.00/1.47  tff(c_976, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_973])).
% 3.00/1.47  tff(c_833, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.00/1.47  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.00/1.47  tff(c_911, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_64])).
% 3.00/1.47  tff(c_921, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_911, c_18])).
% 3.00/1.47  tff(c_1240, plain, (![A_165, B_166, C_167]: (~r1_xboole_0(A_165, B_166) | ~r2_hidden(C_167, B_166) | ~r2_hidden(C_167, A_165))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.47  tff(c_1259, plain, (![C_168]: (~r2_hidden(C_168, k1_tarski('#skF_7')) | ~r2_hidden(C_168, '#skF_6'))), inference(resolution, [status(thm)], [c_921, c_1240])).
% 3.00/1.47  tff(c_1271, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_976, c_1259])).
% 3.00/1.47  tff(c_1277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_1271])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 302
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 2
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Subsume      : 3
% 3.00/1.47  #Demod        : 146
% 3.00/1.47  #Tautology    : 209
% 3.00/1.47  #SimpNegUnit  : 3
% 3.00/1.47  #BackRed      : 0
% 3.00/1.47  
% 3.00/1.47  #Partial instantiations: 0
% 3.00/1.47  #Strategies tried      : 1
% 3.00/1.47  
% 3.00/1.47  Timing (in seconds)
% 3.00/1.47  ----------------------
% 3.03/1.47  Preprocessing        : 0.30
% 3.03/1.47  Parsing              : 0.15
% 3.03/1.47  CNF conversion       : 0.02
% 3.03/1.47  Main loop            : 0.36
% 3.03/1.47  Inferencing          : 0.13
% 3.03/1.47  Reduction            : 0.13
% 3.03/1.47  Demodulation         : 0.10
% 3.03/1.47  BG Simplification    : 0.02
% 3.03/1.47  Subsumption          : 0.06
% 3.03/1.47  Abstraction          : 0.02
% 3.03/1.47  MUC search           : 0.00
% 3.03/1.47  Cooper               : 0.00
% 3.03/1.47  Total                : 0.69
% 3.03/1.47  Index Insertion      : 0.00
% 3.03/1.47  Index Deletion       : 0.00
% 3.03/1.47  Index Matching       : 0.00
% 3.03/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
