%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 127 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
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

tff(c_58,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),B_38)
      | r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_168,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_190,plain,(
    ! [A_73,B_74] :
      ( ~ r1_xboole_0(A_73,B_74)
      | k3_xboole_0(A_73,B_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_168])).

tff(c_919,plain,(
    ! [A_148,B_149] :
      ( k3_xboole_0(k1_tarski(A_148),B_149) = k1_xboole_0
      | r2_hidden(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_54,c_190])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_165,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_940,plain,(
    ! [B_149,A_148] :
      ( k4_xboole_0(B_149,k1_tarski(A_148)) = k5_xboole_0(B_149,k1_xboole_0)
      | r2_hidden(A_148,B_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_165])).

tff(c_1712,plain,(
    ! [B_2039,A_2040] :
      ( k4_xboole_0(B_2039,k1_tarski(A_2040)) = B_2039
      | r2_hidden(A_2040,B_2039) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_940])).

tff(c_56,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_150,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1737,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1712,c_150])).

tff(c_1756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1737])).

tff(c_1757,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_46,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_138,plain,(
    ! [B_57,A_58] : r2_hidden(B_57,k2_tarski(A_58,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_24])).

tff(c_141,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_138])).

tff(c_1758,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1768,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_60])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1772,plain,(
    r1_xboole_0('#skF_8',k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_20])).

tff(c_1991,plain,(
    ! [A_2093,B_2094,C_2095] :
      ( ~ r1_xboole_0(A_2093,B_2094)
      | ~ r2_hidden(C_2095,B_2094)
      | ~ r2_hidden(C_2095,A_2093) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2013,plain,(
    ! [C_2096] :
      ( ~ r2_hidden(C_2096,k1_tarski('#skF_9'))
      | ~ r2_hidden(C_2096,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1772,c_1991])).

tff(c_2025,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_141,c_2013])).

tff(c_2035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_2025])).

tff(c_2036,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2074,plain,(
    ! [A_2105,B_2106] : k1_enumset1(A_2105,A_2105,B_2106) = k2_tarski(A_2105,B_2106) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2092,plain,(
    ! [B_2107,A_2108] : r2_hidden(B_2107,k2_tarski(A_2108,B_2107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_24])).

tff(c_2095,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2092])).

tff(c_2037,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2098,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_62])).

tff(c_2102,plain,(
    r1_xboole_0('#skF_8',k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_20])).

tff(c_2425,plain,(
    ! [A_2134,B_2135,C_2136] :
      ( ~ r1_xboole_0(A_2134,B_2135)
      | ~ r2_hidden(C_2136,B_2135)
      | ~ r2_hidden(C_2136,A_2134) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2547,plain,(
    ! [C_2141] :
      ( ~ r2_hidden(C_2141,k1_tarski('#skF_9'))
      | ~ r2_hidden(C_2141,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2102,c_2425])).

tff(c_2559,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2095,c_2547])).

tff(c_2569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_2559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.60  
% 3.51/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.60  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2 > #skF_1
% 3.51/1.60  
% 3.51/1.60  %Foreground sorts:
% 3.51/1.60  
% 3.51/1.60  
% 3.51/1.60  %Background operators:
% 3.51/1.60  
% 3.51/1.60  
% 3.51/1.60  %Foreground operators:
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.51/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.51/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.51/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.51/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.51/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.51/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.51/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.51/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.51/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.60  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.51/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.51/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.51/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.60  
% 3.51/1.61  tff(f_107, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.51/1.61  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.51/1.61  tff(f_101, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.51/1.61  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.51/1.61  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.51/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.51/1.61  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.51/1.61  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.51/1.61  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.51/1.61  tff(f_88, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.51/1.61  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.51/1.61  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.51/1.61  tff(c_58, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.51/1.61  tff(c_84, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 3.51/1.61  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.51/1.61  tff(c_54, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), B_38) | r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.61  tff(c_14, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.51/1.61  tff(c_168, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.51/1.61  tff(c_190, plain, (![A_73, B_74]: (~r1_xboole_0(A_73, B_74) | k3_xboole_0(A_73, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_168])).
% 3.51/1.61  tff(c_919, plain, (![A_148, B_149]: (k3_xboole_0(k1_tarski(A_148), B_149)=k1_xboole_0 | r2_hidden(A_148, B_149))), inference(resolution, [status(thm)], [c_54, c_190])).
% 3.51/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.61  tff(c_153, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.61  tff(c_165, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 3.51/1.61  tff(c_940, plain, (![B_149, A_148]: (k4_xboole_0(B_149, k1_tarski(A_148))=k5_xboole_0(B_149, k1_xboole_0) | r2_hidden(A_148, B_149))), inference(superposition, [status(thm), theory('equality')], [c_919, c_165])).
% 3.51/1.61  tff(c_1712, plain, (![B_2039, A_2040]: (k4_xboole_0(B_2039, k1_tarski(A_2040))=B_2039 | r2_hidden(A_2040, B_2039))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_940])).
% 3.51/1.61  tff(c_56, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.51/1.61  tff(c_150, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 3.51/1.61  tff(c_1737, plain, (r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1712, c_150])).
% 3.51/1.61  tff(c_1756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1737])).
% 3.51/1.61  tff(c_1757, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 3.51/1.61  tff(c_46, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.51/1.61  tff(c_120, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.51/1.61  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.61  tff(c_138, plain, (![B_57, A_58]: (r2_hidden(B_57, k2_tarski(A_58, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_24])).
% 3.51/1.61  tff(c_141, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_138])).
% 3.51/1.61  tff(c_1758, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 3.51/1.61  tff(c_60, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.51/1.61  tff(c_1768, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_60])).
% 3.51/1.61  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.51/1.61  tff(c_1772, plain, (r1_xboole_0('#skF_8', k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1768, c_20])).
% 3.51/1.61  tff(c_1991, plain, (![A_2093, B_2094, C_2095]: (~r1_xboole_0(A_2093, B_2094) | ~r2_hidden(C_2095, B_2094) | ~r2_hidden(C_2095, A_2093))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.61  tff(c_2013, plain, (![C_2096]: (~r2_hidden(C_2096, k1_tarski('#skF_9')) | ~r2_hidden(C_2096, '#skF_8'))), inference(resolution, [status(thm)], [c_1772, c_1991])).
% 3.51/1.61  tff(c_2025, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_141, c_2013])).
% 3.51/1.61  tff(c_2035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1757, c_2025])).
% 3.51/1.61  tff(c_2036, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_58])).
% 3.51/1.61  tff(c_2074, plain, (![A_2105, B_2106]: (k1_enumset1(A_2105, A_2105, B_2106)=k2_tarski(A_2105, B_2106))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.51/1.61  tff(c_2092, plain, (![B_2107, A_2108]: (r2_hidden(B_2107, k2_tarski(A_2108, B_2107)))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_24])).
% 3.51/1.61  tff(c_2095, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2092])).
% 3.51/1.61  tff(c_2037, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 3.51/1.61  tff(c_62, plain, (~r2_hidden('#skF_7', '#skF_6') | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.51/1.61  tff(c_2098, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_62])).
% 3.51/1.61  tff(c_2102, plain, (r1_xboole_0('#skF_8', k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2098, c_20])).
% 3.51/1.61  tff(c_2425, plain, (![A_2134, B_2135, C_2136]: (~r1_xboole_0(A_2134, B_2135) | ~r2_hidden(C_2136, B_2135) | ~r2_hidden(C_2136, A_2134))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.61  tff(c_2547, plain, (![C_2141]: (~r2_hidden(C_2141, k1_tarski('#skF_9')) | ~r2_hidden(C_2141, '#skF_8'))), inference(resolution, [status(thm)], [c_2102, c_2425])).
% 3.51/1.61  tff(c_2559, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2095, c_2547])).
% 3.51/1.61  tff(c_2569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2036, c_2559])).
% 3.51/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.61  
% 3.51/1.61  Inference rules
% 3.51/1.61  ----------------------
% 3.51/1.61  #Ref     : 0
% 3.51/1.61  #Sup     : 511
% 3.51/1.61  #Fact    : 6
% 3.51/1.61  #Define  : 0
% 3.51/1.61  #Split   : 2
% 3.51/1.61  #Chain   : 0
% 3.51/1.61  #Close   : 0
% 3.51/1.61  
% 3.51/1.61  Ordering : KBO
% 3.51/1.61  
% 3.51/1.61  Simplification rules
% 3.51/1.61  ----------------------
% 3.51/1.61  #Subsume      : 71
% 3.51/1.61  #Demod        : 181
% 3.51/1.61  #Tautology    : 266
% 3.51/1.61  #SimpNegUnit  : 15
% 3.51/1.61  #BackRed      : 0
% 3.51/1.61  
% 3.51/1.61  #Partial instantiations: 990
% 3.51/1.61  #Strategies tried      : 1
% 3.51/1.61  
% 3.51/1.61  Timing (in seconds)
% 3.51/1.61  ----------------------
% 3.51/1.62  Preprocessing        : 0.32
% 3.51/1.62  Parsing              : 0.16
% 3.51/1.62  CNF conversion       : 0.02
% 3.51/1.62  Main loop            : 0.55
% 3.51/1.62  Inferencing          : 0.25
% 3.51/1.62  Reduction            : 0.16
% 3.51/1.62  Demodulation         : 0.12
% 3.51/1.62  BG Simplification    : 0.03
% 3.51/1.62  Subsumption          : 0.07
% 3.51/1.62  Abstraction          : 0.03
% 3.51/1.62  MUC search           : 0.00
% 3.51/1.62  Cooper               : 0.00
% 3.51/1.62  Total                : 0.90
% 3.51/1.62  Index Insertion      : 0.00
% 3.51/1.62  Index Deletion       : 0.00
% 3.51/1.62  Index Matching       : 0.00
% 3.51/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
