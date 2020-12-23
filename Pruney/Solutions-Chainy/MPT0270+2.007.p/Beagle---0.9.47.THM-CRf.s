%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 9.97s
% Output     : CNFRefutation 9.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 116 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 141 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_113,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
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

tff(c_86,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(k1_tarski(A_83),B_84)
      | r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_252,plain,(
    ! [A_117,B_118] : k3_tarski(k2_tarski(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_316,plain,(
    ! [A_122,B_123] : k3_tarski(k2_tarski(A_122,B_123)) = k2_xboole_0(B_123,A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_80,plain,(
    ! [A_85,B_86] : k3_tarski(k2_tarski(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_322,plain,(
    ! [B_123,A_122] : k2_xboole_0(B_123,A_122) = k2_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_80])).

tff(c_663,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(k2_xboole_0(A_143,B_144),B_144) = A_143
      | ~ r1_xboole_0(A_143,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2494,plain,(
    ! [A_251,B_252] :
      ( k4_xboole_0(k2_xboole_0(A_251,B_252),A_251) = B_252
      | ~ r1_xboole_0(B_252,A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_663])).

tff(c_2552,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(k4_xboole_0(B_14,A_13),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2494])).

tff(c_2583,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2552])).

tff(c_695,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(k2_xboole_0(A_122,B_123),A_122) = B_123
      | ~ r1_xboole_0(B_123,A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_663])).

tff(c_2682,plain,(
    ! [B_259,A_260] :
      ( k4_xboole_0(B_259,A_260) = B_259
      | ~ r1_xboole_0(B_259,A_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2583,c_695])).

tff(c_16488,plain,(
    ! [A_23754,B_23755] :
      ( k4_xboole_0(k1_tarski(A_23754),B_23755) = k1_tarski(A_23754)
      | r2_hidden(A_23754,B_23755) ) ),
    inference(resolution,[status(thm)],[c_78,c_2682])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_16597,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16488,c_169])).

tff(c_16661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_16597])).

tff(c_16662,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_64,plain,(
    ! [A_55] : k2_tarski(A_55,A_55) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16707,plain,(
    ! [A_23932,B_23933] : k1_enumset1(A_23932,A_23932,B_23933) = k2_tarski(A_23932,B_23933) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16725,plain,(
    ! [A_23934,B_23935] : r2_hidden(A_23934,k2_tarski(A_23934,B_23935)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16707,c_40])).

tff(c_16734,plain,(
    ! [A_55] : r2_hidden(A_55,k1_tarski(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_16725])).

tff(c_16663,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16738,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16663,c_88])).

tff(c_16742,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16738,c_22])).

tff(c_17327,plain,(
    ! [A_23975,B_23976,C_23977] :
      ( ~ r1_xboole_0(A_23975,B_23976)
      | ~ r2_hidden(C_23977,B_23976)
      | ~ r2_hidden(C_23977,A_23975) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17412,plain,(
    ! [C_23985] :
      ( ~ r2_hidden(C_23985,'#skF_7')
      | ~ r2_hidden(C_23985,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_16742,c_17327])).

tff(c_17424,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_16734,c_17412])).

tff(c_17430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16662,c_17424])).

tff(c_17431,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_17470,plain,(
    ! [A_23997,B_23998] : k1_enumset1(A_23997,A_23997,B_23998) = k2_tarski(A_23997,B_23998) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ! [E_38,A_32,B_33] : r2_hidden(E_38,k1_enumset1(A_32,B_33,E_38)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17488,plain,(
    ! [B_23999,A_24000] : r2_hidden(B_23999,k2_tarski(A_24000,B_23999)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17470,c_36])).

tff(c_17497,plain,(
    ! [A_55] : r2_hidden(A_55,k1_tarski(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_17488])).

tff(c_17432,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_17513,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17432,c_90])).

tff(c_17517,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17513,c_22])).

tff(c_18172,plain,(
    ! [A_24045,B_24046,C_24047] :
      ( ~ r1_xboole_0(A_24045,B_24046)
      | ~ r2_hidden(C_24047,B_24046)
      | ~ r2_hidden(C_24047,A_24045) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18291,plain,(
    ! [C_24054] :
      ( ~ r2_hidden(C_24054,'#skF_7')
      | ~ r2_hidden(C_24054,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_17517,c_18172])).

tff(c_18303,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_17497,c_18291])).

tff(c_18309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17431,c_18303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.97/3.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.89  
% 9.97/3.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.90  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.97/3.90  
% 9.97/3.90  %Foreground sorts:
% 9.97/3.90  
% 9.97/3.90  
% 9.97/3.90  %Background operators:
% 9.97/3.90  
% 9.97/3.90  
% 9.97/3.90  %Foreground operators:
% 9.97/3.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.97/3.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.97/3.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.97/3.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.97/3.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.97/3.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.97/3.90  tff('#skF_7', type, '#skF_7': $i).
% 9.97/3.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.97/3.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.97/3.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.97/3.90  tff('#skF_5', type, '#skF_5': $i).
% 9.97/3.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.97/3.90  tff('#skF_6', type, '#skF_6': $i).
% 9.97/3.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.97/3.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.97/3.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.97/3.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.97/3.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.97/3.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.97/3.90  tff('#skF_4', type, '#skF_4': $i).
% 9.97/3.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.97/3.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.97/3.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.97/3.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.97/3.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.97/3.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.97/3.90  
% 9.97/3.91  tff(f_121, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.97/3.91  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.97/3.91  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.97/3.91  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.97/3.91  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.97/3.91  tff(f_113, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.97/3.91  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.97/3.91  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.97/3.91  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.97/3.91  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.97/3.91  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.97/3.91  tff(c_86, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.97/3.91  tff(c_168, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 9.97/3.91  tff(c_78, plain, (![A_83, B_84]: (r1_xboole_0(k1_tarski(A_83), B_84) | r2_hidden(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.97/3.91  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.97/3.91  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.97/3.91  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.97/3.91  tff(c_252, plain, (![A_117, B_118]: (k3_tarski(k2_tarski(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.97/3.91  tff(c_316, plain, (![A_122, B_123]: (k3_tarski(k2_tarski(A_122, B_123))=k2_xboole_0(B_123, A_122))), inference(superposition, [status(thm), theory('equality')], [c_32, c_252])).
% 9.97/3.91  tff(c_80, plain, (![A_85, B_86]: (k3_tarski(k2_tarski(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.97/3.91  tff(c_322, plain, (![B_123, A_122]: (k2_xboole_0(B_123, A_122)=k2_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_316, c_80])).
% 9.97/3.91  tff(c_663, plain, (![A_143, B_144]: (k4_xboole_0(k2_xboole_0(A_143, B_144), B_144)=A_143 | ~r1_xboole_0(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.97/3.91  tff(c_2494, plain, (![A_251, B_252]: (k4_xboole_0(k2_xboole_0(A_251, B_252), A_251)=B_252 | ~r1_xboole_0(B_252, A_251))), inference(superposition, [status(thm), theory('equality')], [c_322, c_663])).
% 9.97/3.91  tff(c_2552, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13) | ~r1_xboole_0(k4_xboole_0(B_14, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2494])).
% 9.97/3.91  tff(c_2583, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2552])).
% 9.97/3.91  tff(c_695, plain, (![A_122, B_123]: (k4_xboole_0(k2_xboole_0(A_122, B_123), A_122)=B_123 | ~r1_xboole_0(B_123, A_122))), inference(superposition, [status(thm), theory('equality')], [c_322, c_663])).
% 9.97/3.91  tff(c_2682, plain, (![B_259, A_260]: (k4_xboole_0(B_259, A_260)=B_259 | ~r1_xboole_0(B_259, A_260))), inference(demodulation, [status(thm), theory('equality')], [c_2583, c_695])).
% 9.97/3.91  tff(c_16488, plain, (![A_23754, B_23755]: (k4_xboole_0(k1_tarski(A_23754), B_23755)=k1_tarski(A_23754) | r2_hidden(A_23754, B_23755))), inference(resolution, [status(thm)], [c_78, c_2682])).
% 9.97/3.91  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.97/3.91  tff(c_169, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 9.97/3.91  tff(c_16597, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16488, c_169])).
% 9.97/3.91  tff(c_16661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_16597])).
% 9.97/3.91  tff(c_16662, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 9.97/3.91  tff(c_64, plain, (![A_55]: (k2_tarski(A_55, A_55)=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.97/3.91  tff(c_16707, plain, (![A_23932, B_23933]: (k1_enumset1(A_23932, A_23932, B_23933)=k2_tarski(A_23932, B_23933))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.97/3.91  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.97/3.91  tff(c_16725, plain, (![A_23934, B_23935]: (r2_hidden(A_23934, k2_tarski(A_23934, B_23935)))), inference(superposition, [status(thm), theory('equality')], [c_16707, c_40])).
% 9.97/3.91  tff(c_16734, plain, (![A_55]: (r2_hidden(A_55, k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_16725])).
% 9.97/3.91  tff(c_16663, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 9.97/3.91  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.97/3.91  tff(c_16738, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16663, c_88])).
% 9.97/3.91  tff(c_16742, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16738, c_22])).
% 9.97/3.91  tff(c_17327, plain, (![A_23975, B_23976, C_23977]: (~r1_xboole_0(A_23975, B_23976) | ~r2_hidden(C_23977, B_23976) | ~r2_hidden(C_23977, A_23975))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.97/3.91  tff(c_17412, plain, (![C_23985]: (~r2_hidden(C_23985, '#skF_7') | ~r2_hidden(C_23985, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_16742, c_17327])).
% 9.97/3.91  tff(c_17424, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_16734, c_17412])).
% 9.97/3.91  tff(c_17430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16662, c_17424])).
% 9.97/3.91  tff(c_17431, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 9.97/3.91  tff(c_17470, plain, (![A_23997, B_23998]: (k1_enumset1(A_23997, A_23997, B_23998)=k2_tarski(A_23997, B_23998))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.97/3.91  tff(c_36, plain, (![E_38, A_32, B_33]: (r2_hidden(E_38, k1_enumset1(A_32, B_33, E_38)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.97/3.91  tff(c_17488, plain, (![B_23999, A_24000]: (r2_hidden(B_23999, k2_tarski(A_24000, B_23999)))), inference(superposition, [status(thm), theory('equality')], [c_17470, c_36])).
% 9.97/3.91  tff(c_17497, plain, (![A_55]: (r2_hidden(A_55, k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_17488])).
% 9.97/3.91  tff(c_17432, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 9.97/3.91  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.97/3.91  tff(c_17513, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17432, c_90])).
% 9.97/3.91  tff(c_17517, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17513, c_22])).
% 9.97/3.91  tff(c_18172, plain, (![A_24045, B_24046, C_24047]: (~r1_xboole_0(A_24045, B_24046) | ~r2_hidden(C_24047, B_24046) | ~r2_hidden(C_24047, A_24045))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.97/3.91  tff(c_18291, plain, (![C_24054]: (~r2_hidden(C_24054, '#skF_7') | ~r2_hidden(C_24054, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_17517, c_18172])).
% 9.97/3.91  tff(c_18303, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_17497, c_18291])).
% 9.97/3.91  tff(c_18309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17431, c_18303])).
% 9.97/3.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.91  
% 9.97/3.91  Inference rules
% 9.97/3.91  ----------------------
% 9.97/3.91  #Ref     : 0
% 9.97/3.91  #Sup     : 3912
% 9.97/3.91  #Fact    : 18
% 9.97/3.91  #Define  : 0
% 9.97/3.91  #Split   : 2
% 9.97/3.91  #Chain   : 0
% 9.97/3.91  #Close   : 0
% 9.97/3.91  
% 9.97/3.91  Ordering : KBO
% 9.97/3.91  
% 9.97/3.91  Simplification rules
% 9.97/3.91  ----------------------
% 9.97/3.91  #Subsume      : 330
% 9.97/3.91  #Demod        : 3873
% 9.97/3.91  #Tautology    : 2240
% 9.97/3.91  #SimpNegUnit  : 11
% 9.97/3.91  #BackRed      : 3
% 9.97/3.91  
% 9.97/3.91  #Partial instantiations: 8946
% 9.97/3.91  #Strategies tried      : 1
% 9.97/3.91  
% 9.97/3.91  Timing (in seconds)
% 9.97/3.91  ----------------------
% 9.97/3.91  Preprocessing        : 0.39
% 9.97/3.91  Parsing              : 0.20
% 9.97/3.91  CNF conversion       : 0.03
% 9.97/3.91  Main loop            : 2.73
% 9.97/3.91  Inferencing          : 0.89
% 9.97/3.91  Reduction            : 1.25
% 9.97/3.91  Demodulation         : 1.09
% 9.97/3.91  BG Simplification    : 0.11
% 9.97/3.91  Subsumption          : 0.36
% 9.97/3.91  Abstraction          : 0.13
% 9.97/3.91  MUC search           : 0.00
% 9.97/3.91  Cooper               : 0.00
% 9.97/3.91  Total                : 3.15
% 9.97/3.91  Index Insertion      : 0.00
% 9.97/3.91  Index Deletion       : 0.00
% 9.97/3.91  Index Matching       : 0.00
% 9.97/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
