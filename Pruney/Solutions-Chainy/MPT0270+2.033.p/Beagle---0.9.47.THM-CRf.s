%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 124 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(k1_tarski(A_55),B_56)
      | r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,k3_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    ! [A_85,B_86] :
      ( ~ r1_xboole_0(A_85,B_86)
      | k3_xboole_0(A_85,B_86) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_157])).

tff(c_919,plain,(
    ! [A_150,B_151] :
      ( k3_xboole_0(k1_tarski(A_150),B_151) = k1_xboole_0
      | r2_hidden(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_60,c_169])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_946,plain,(
    ! [A_150,B_151] :
      ( k5_xboole_0(k1_tarski(A_150),k1_xboole_0) = k4_xboole_0(k1_tarski(A_150),B_151)
      | r2_hidden(A_150,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_16])).

tff(c_1787,plain,(
    ! [A_207,B_208] :
      ( k4_xboole_0(k1_tarski(A_207),B_208) = k1_tarski(A_207)
      | r2_hidden(A_207,B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_946])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_125,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1827,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_125])).

tff(c_1860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1827])).

tff(c_1861,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_46,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1871,plain,(
    ! [A_212,B_213] : k1_enumset1(A_212,A_212,B_213) = k2_tarski(A_212,B_213) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1889,plain,(
    ! [B_214,A_215] : r2_hidden(B_214,k2_tarski(A_215,B_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_24])).

tff(c_1892,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1889])).

tff(c_1862,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1917,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_66])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1921,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1917,c_20])).

tff(c_2322,plain,(
    ! [A_246,B_247,C_248] :
      ( ~ r1_xboole_0(A_246,B_247)
      | ~ r2_hidden(C_248,B_247)
      | ~ r2_hidden(C_248,A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2445,plain,(
    ! [C_253] :
      ( ~ r2_hidden(C_253,'#skF_9')
      | ~ r2_hidden(C_253,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1921,c_2322])).

tff(c_2457,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_1892,c_2445])).

tff(c_2467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_2457])).

tff(c_2468,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2472,plain,(
    ! [A_259,B_260] : k1_enumset1(A_259,A_259,B_260) = k2_tarski(A_259,B_260) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2505,plain,(
    ! [B_263,A_264] : r2_hidden(B_263,k2_tarski(A_264,B_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2472,c_24])).

tff(c_2508,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2505])).

tff(c_2469,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2612,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2469,c_68])).

tff(c_2619,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2612,c_20])).

tff(c_2729,plain,(
    ! [A_288,B_289,C_290] :
      ( ~ r1_xboole_0(A_288,B_289)
      | ~ r2_hidden(C_290,B_289)
      | ~ r2_hidden(C_290,A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2857,plain,(
    ! [C_294] :
      ( ~ r2_hidden(C_294,'#skF_9')
      | ~ r2_hidden(C_294,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2619,c_2729])).

tff(c_2869,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2508,c_2857])).

tff(c_2879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.88  
% 3.98/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.88  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2 > #skF_1
% 3.98/1.88  
% 3.98/1.88  %Foreground sorts:
% 3.98/1.88  
% 3.98/1.88  
% 3.98/1.88  %Background operators:
% 3.98/1.88  
% 3.98/1.88  
% 3.98/1.88  %Foreground operators:
% 3.98/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.98/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.98/1.88  tff('#skF_7', type, '#skF_7': $i).
% 3.98/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.98/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.88  tff('#skF_6', type, '#skF_6': $i).
% 3.98/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.98/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.98/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.88  tff('#skF_9', type, '#skF_9': $i).
% 3.98/1.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.98/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.88  tff('#skF_8', type, '#skF_8': $i).
% 3.98/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.98/1.88  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.98/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.98/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.88  
% 3.98/1.90  tff(f_113, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.98/1.90  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.98/1.90  tff(f_107, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.98/1.90  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.98/1.90  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.98/1.90  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.98/1.90  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.98/1.90  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.98/1.90  tff(f_88, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.98/1.90  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.98/1.90  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.98/1.90  tff(c_64, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.90  tff(c_124, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 3.98/1.90  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.98/1.90  tff(c_60, plain, (![A_55, B_56]: (r1_xboole_0(k1_tarski(A_55), B_56) | r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.98/1.90  tff(c_14, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.98/1.90  tff(c_157, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, k3_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.98/1.90  tff(c_169, plain, (![A_85, B_86]: (~r1_xboole_0(A_85, B_86) | k3_xboole_0(A_85, B_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_157])).
% 3.98/1.90  tff(c_919, plain, (![A_150, B_151]: (k3_xboole_0(k1_tarski(A_150), B_151)=k1_xboole_0 | r2_hidden(A_150, B_151))), inference(resolution, [status(thm)], [c_60, c_169])).
% 3.98/1.90  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.98/1.90  tff(c_946, plain, (![A_150, B_151]: (k5_xboole_0(k1_tarski(A_150), k1_xboole_0)=k4_xboole_0(k1_tarski(A_150), B_151) | r2_hidden(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_919, c_16])).
% 3.98/1.90  tff(c_1787, plain, (![A_207, B_208]: (k4_xboole_0(k1_tarski(A_207), B_208)=k1_tarski(A_207) | r2_hidden(A_207, B_208))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_946])).
% 3.98/1.90  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.90  tff(c_125, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 3.98/1.90  tff(c_1827, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1787, c_125])).
% 3.98/1.90  tff(c_1860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_1827])).
% 3.98/1.90  tff(c_1861, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 3.98/1.90  tff(c_46, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.98/1.90  tff(c_1871, plain, (![A_212, B_213]: (k1_enumset1(A_212, A_212, B_213)=k2_tarski(A_212, B_213))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.98/1.90  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.98/1.90  tff(c_1889, plain, (![B_214, A_215]: (r2_hidden(B_214, k2_tarski(A_215, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_1871, c_24])).
% 3.98/1.90  tff(c_1892, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1889])).
% 3.98/1.90  tff(c_1862, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 3.98/1.90  tff(c_66, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.90  tff(c_1917, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_66])).
% 3.98/1.90  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.98/1.90  tff(c_1921, plain, (r1_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1917, c_20])).
% 3.98/1.90  tff(c_2322, plain, (![A_246, B_247, C_248]: (~r1_xboole_0(A_246, B_247) | ~r2_hidden(C_248, B_247) | ~r2_hidden(C_248, A_246))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.90  tff(c_2445, plain, (![C_253]: (~r2_hidden(C_253, '#skF_9') | ~r2_hidden(C_253, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_1921, c_2322])).
% 3.98/1.90  tff(c_2457, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_1892, c_2445])).
% 3.98/1.90  tff(c_2467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1861, c_2457])).
% 3.98/1.90  tff(c_2468, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_64])).
% 3.98/1.90  tff(c_2472, plain, (![A_259, B_260]: (k1_enumset1(A_259, A_259, B_260)=k2_tarski(A_259, B_260))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.98/1.90  tff(c_2505, plain, (![B_263, A_264]: (r2_hidden(B_263, k2_tarski(A_264, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_2472, c_24])).
% 3.98/1.90  tff(c_2508, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2505])).
% 3.98/1.90  tff(c_2469, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 3.98/1.90  tff(c_68, plain, (~r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.90  tff(c_2612, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2469, c_68])).
% 3.98/1.90  tff(c_2619, plain, (r1_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2612, c_20])).
% 3.98/1.90  tff(c_2729, plain, (![A_288, B_289, C_290]: (~r1_xboole_0(A_288, B_289) | ~r2_hidden(C_290, B_289) | ~r2_hidden(C_290, A_288))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.90  tff(c_2857, plain, (![C_294]: (~r2_hidden(C_294, '#skF_9') | ~r2_hidden(C_294, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_2619, c_2729])).
% 3.98/1.90  tff(c_2869, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2508, c_2857])).
% 3.98/1.90  tff(c_2879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2468, c_2869])).
% 3.98/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.90  
% 3.98/1.90  Inference rules
% 3.98/1.90  ----------------------
% 3.98/1.90  #Ref     : 0
% 3.98/1.90  #Sup     : 682
% 3.98/1.90  #Fact    : 0
% 3.98/1.90  #Define  : 0
% 3.98/1.90  #Split   : 2
% 3.98/1.90  #Chain   : 0
% 3.98/1.90  #Close   : 0
% 3.98/1.90  
% 3.98/1.90  Ordering : KBO
% 3.98/1.90  
% 3.98/1.90  Simplification rules
% 3.98/1.90  ----------------------
% 3.98/1.90  #Subsume      : 105
% 3.98/1.90  #Demod        : 301
% 3.98/1.90  #Tautology    : 415
% 3.98/1.90  #SimpNegUnit  : 22
% 3.98/1.90  #BackRed      : 0
% 3.98/1.90  
% 3.98/1.90  #Partial instantiations: 0
% 3.98/1.90  #Strategies tried      : 1
% 3.98/1.90  
% 3.98/1.90  Timing (in seconds)
% 3.98/1.90  ----------------------
% 3.98/1.90  Preprocessing        : 0.42
% 3.98/1.90  Parsing              : 0.20
% 3.98/1.90  CNF conversion       : 0.04
% 3.98/1.90  Main loop            : 0.60
% 3.98/1.90  Inferencing          : 0.21
% 3.98/1.90  Reduction            : 0.21
% 3.98/1.90  Demodulation         : 0.16
% 3.98/1.90  BG Simplification    : 0.03
% 3.98/1.90  Subsumption          : 0.10
% 3.98/1.90  Abstraction          : 0.03
% 3.98/1.90  MUC search           : 0.00
% 3.98/1.90  Cooper               : 0.00
% 3.98/1.90  Total                : 1.05
% 3.98/1.90  Index Insertion      : 0.00
% 3.98/1.90  Index Deletion       : 0.00
% 3.98/1.90  Index Matching       : 0.00
% 3.98/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
