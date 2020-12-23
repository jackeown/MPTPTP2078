%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:54 EST 2020

% Result     : Theorem 8.92s
% Output     : CNFRefutation 9.24s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_113,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_86,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,(
    ! [A_84,B_85] :
      ( r1_xboole_0(k1_tarski(A_84),B_85)
      | r2_hidden(A_84,B_85) ) ),
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
    ! [A_118,B_119] : k3_tarski(k2_tarski(A_118,B_119)) = k2_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_299,plain,(
    ! [A_123,B_124] : k3_tarski(k2_tarski(A_123,B_124)) = k2_xboole_0(B_124,A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_80,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_305,plain,(
    ! [B_124,A_123] : k2_xboole_0(B_124,A_123) = k2_xboole_0(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_80])).

tff(c_541,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(k2_xboole_0(A_140,B_141),B_141) = A_140
      | ~ r1_xboole_0(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2403,plain,(
    ! [A_250,B_251] :
      ( k4_xboole_0(k2_xboole_0(A_250,B_251),A_250) = B_251
      | ~ r1_xboole_0(B_251,A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2476,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(k4_xboole_0(B_14,A_13),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2403])).

tff(c_2495,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2476])).

tff(c_573,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(k2_xboole_0(A_123,B_124),A_123) = B_124
      | ~ r1_xboole_0(B_124,A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2590,plain,(
    ! [B_254,A_255] :
      ( k4_xboole_0(B_254,A_255) = B_254
      | ~ r1_xboole_0(B_254,A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2495,c_573])).

tff(c_14116,plain,(
    ! [A_21741,B_21742] :
      ( k4_xboole_0(k1_tarski(A_21741),B_21742) = k1_tarski(A_21741)
      | r2_hidden(A_21741,B_21742) ) ),
    inference(resolution,[status(thm)],[c_78,c_2590])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_14213,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14116,c_169])).

tff(c_14274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_14213])).

tff(c_14275,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_64,plain,(
    ! [A_56] : k2_tarski(A_56,A_56) = k1_tarski(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14321,plain,(
    ! [A_21921,B_21922] : k1_enumset1(A_21921,A_21921,B_21922) = k2_tarski(A_21921,B_21922) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [E_38,A_32,C_34] : r2_hidden(E_38,k1_enumset1(A_32,E_38,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14339,plain,(
    ! [A_21923,B_21924] : r2_hidden(A_21923,k2_tarski(A_21923,B_21924)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14321,c_38])).

tff(c_14348,plain,(
    ! [A_56] : r2_hidden(A_56,k1_tarski(A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14339])).

tff(c_14276,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14432,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14276,c_88])).

tff(c_14436,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14432,c_22])).

tff(c_14741,plain,(
    ! [A_21952,B_21953,C_21954] :
      ( ~ r1_xboole_0(A_21952,B_21953)
      | ~ r2_hidden(C_21954,B_21953)
      | ~ r2_hidden(C_21954,A_21952) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14859,plain,(
    ! [C_21960] :
      ( ~ r2_hidden(C_21960,'#skF_7')
      | ~ r2_hidden(C_21960,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_14436,c_14741])).

tff(c_14871,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14348,c_14859])).

tff(c_14877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14275,c_14871])).

tff(c_14878,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_14917,plain,(
    ! [A_21974,B_21975] : k1_enumset1(A_21974,A_21974,B_21975) = k2_tarski(A_21974,B_21975) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14935,plain,(
    ! [A_21976,B_21977] : r2_hidden(A_21976,k2_tarski(A_21976,B_21977)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14917,c_40])).

tff(c_14944,plain,(
    ! [A_56] : r2_hidden(A_56,k1_tarski(A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14935])).

tff(c_14879,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14946,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14879,c_90])).

tff(c_14950,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14946,c_22])).

tff(c_15418,plain,(
    ! [A_22013,B_22014,C_22015] :
      ( ~ r1_xboole_0(A_22013,B_22014)
      | ~ r2_hidden(C_22015,B_22014)
      | ~ r2_hidden(C_22015,A_22013) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15639,plain,(
    ! [C_22023] :
      ( ~ r2_hidden(C_22023,'#skF_7')
      | ~ r2_hidden(C_22023,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_14950,c_15418])).

tff(c_15651,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14944,c_15639])).

tff(c_15657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14878,c_15651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n009.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 17:00:41 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.92/2.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/2.97  
% 8.92/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/2.98  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 8.92/2.98  
% 8.92/2.98  %Foreground sorts:
% 8.92/2.98  
% 8.92/2.98  
% 8.92/2.98  %Background operators:
% 8.92/2.98  
% 8.92/2.98  
% 8.92/2.98  %Foreground operators:
% 8.92/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.92/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.92/2.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.92/2.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.92/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.92/2.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.92/2.98  tff('#skF_7', type, '#skF_7': $i).
% 8.92/2.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.92/2.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.92/2.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.92/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.92/2.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.92/2.98  tff('#skF_6', type, '#skF_6': $i).
% 8.92/2.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.92/2.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.92/2.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.92/2.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.92/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.92/2.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.92/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.92/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.92/2.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.92/2.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.92/2.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.92/2.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.92/2.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.92/2.98  
% 9.24/2.99  tff(f_121, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.24/2.99  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.24/2.99  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.24/2.99  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.24/2.99  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.24/2.99  tff(f_113, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.24/2.99  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.24/2.99  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.24/2.99  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.24/2.99  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.24/2.99  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.24/2.99  tff(c_86, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.24/2.99  tff(c_168, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 9.24/2.99  tff(c_78, plain, (![A_84, B_85]: (r1_xboole_0(k1_tarski(A_84), B_85) | r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.24/2.99  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.24/2.99  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.24/2.99  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.24/2.99  tff(c_252, plain, (![A_118, B_119]: (k3_tarski(k2_tarski(A_118, B_119))=k2_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.24/2.99  tff(c_299, plain, (![A_123, B_124]: (k3_tarski(k2_tarski(A_123, B_124))=k2_xboole_0(B_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_32, c_252])).
% 9.24/2.99  tff(c_80, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.24/2.99  tff(c_305, plain, (![B_124, A_123]: (k2_xboole_0(B_124, A_123)=k2_xboole_0(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_299, c_80])).
% 9.24/2.99  tff(c_541, plain, (![A_140, B_141]: (k4_xboole_0(k2_xboole_0(A_140, B_141), B_141)=A_140 | ~r1_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.24/2.99  tff(c_2403, plain, (![A_250, B_251]: (k4_xboole_0(k2_xboole_0(A_250, B_251), A_250)=B_251 | ~r1_xboole_0(B_251, A_250))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.24/2.99  tff(c_2476, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13) | ~r1_xboole_0(k4_xboole_0(B_14, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2403])).
% 9.24/2.99  tff(c_2495, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2476])).
% 9.24/2.99  tff(c_573, plain, (![A_123, B_124]: (k4_xboole_0(k2_xboole_0(A_123, B_124), A_123)=B_124 | ~r1_xboole_0(B_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.24/2.99  tff(c_2590, plain, (![B_254, A_255]: (k4_xboole_0(B_254, A_255)=B_254 | ~r1_xboole_0(B_254, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_2495, c_573])).
% 9.24/2.99  tff(c_14116, plain, (![A_21741, B_21742]: (k4_xboole_0(k1_tarski(A_21741), B_21742)=k1_tarski(A_21741) | r2_hidden(A_21741, B_21742))), inference(resolution, [status(thm)], [c_78, c_2590])).
% 9.24/2.99  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.24/2.99  tff(c_169, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 9.24/2.99  tff(c_14213, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14116, c_169])).
% 9.24/2.99  tff(c_14274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_14213])).
% 9.24/2.99  tff(c_14275, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 9.24/2.99  tff(c_64, plain, (![A_56]: (k2_tarski(A_56, A_56)=k1_tarski(A_56))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.24/2.99  tff(c_14321, plain, (![A_21921, B_21922]: (k1_enumset1(A_21921, A_21921, B_21922)=k2_tarski(A_21921, B_21922))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.24/2.99  tff(c_38, plain, (![E_38, A_32, C_34]: (r2_hidden(E_38, k1_enumset1(A_32, E_38, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.24/2.99  tff(c_14339, plain, (![A_21923, B_21924]: (r2_hidden(A_21923, k2_tarski(A_21923, B_21924)))), inference(superposition, [status(thm), theory('equality')], [c_14321, c_38])).
% 9.24/2.99  tff(c_14348, plain, (![A_56]: (r2_hidden(A_56, k1_tarski(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14339])).
% 9.24/2.99  tff(c_14276, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 9.24/2.99  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.24/2.99  tff(c_14432, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14276, c_88])).
% 9.24/2.99  tff(c_14436, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14432, c_22])).
% 9.24/2.99  tff(c_14741, plain, (![A_21952, B_21953, C_21954]: (~r1_xboole_0(A_21952, B_21953) | ~r2_hidden(C_21954, B_21953) | ~r2_hidden(C_21954, A_21952))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/2.99  tff(c_14859, plain, (![C_21960]: (~r2_hidden(C_21960, '#skF_7') | ~r2_hidden(C_21960, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_14436, c_14741])).
% 9.24/2.99  tff(c_14871, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14348, c_14859])).
% 9.24/2.99  tff(c_14877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14275, c_14871])).
% 9.24/2.99  tff(c_14878, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 9.24/2.99  tff(c_14917, plain, (![A_21974, B_21975]: (k1_enumset1(A_21974, A_21974, B_21975)=k2_tarski(A_21974, B_21975))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.24/2.99  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.24/2.99  tff(c_14935, plain, (![A_21976, B_21977]: (r2_hidden(A_21976, k2_tarski(A_21976, B_21977)))), inference(superposition, [status(thm), theory('equality')], [c_14917, c_40])).
% 9.24/2.99  tff(c_14944, plain, (![A_56]: (r2_hidden(A_56, k1_tarski(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14935])).
% 9.24/2.99  tff(c_14879, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 9.24/2.99  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.24/2.99  tff(c_14946, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14879, c_90])).
% 9.24/2.99  tff(c_14950, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14946, c_22])).
% 9.24/2.99  tff(c_15418, plain, (![A_22013, B_22014, C_22015]: (~r1_xboole_0(A_22013, B_22014) | ~r2_hidden(C_22015, B_22014) | ~r2_hidden(C_22015, A_22013))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.24/2.99  tff(c_15639, plain, (![C_22023]: (~r2_hidden(C_22023, '#skF_7') | ~r2_hidden(C_22023, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_14950, c_15418])).
% 9.24/2.99  tff(c_15651, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14944, c_15639])).
% 9.24/2.99  tff(c_15657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14878, c_15651])).
% 9.24/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.24/2.99  
% 9.24/2.99  Inference rules
% 9.24/2.99  ----------------------
% 9.24/2.99  #Ref     : 0
% 9.24/2.99  #Sup     : 3287
% 9.24/2.99  #Fact    : 18
% 9.24/2.99  #Define  : 0
% 9.24/2.99  #Split   : 2
% 9.24/2.99  #Chain   : 0
% 9.24/2.99  #Close   : 0
% 9.24/2.99  
% 9.24/2.99  Ordering : KBO
% 9.24/2.99  
% 9.24/2.99  Simplification rules
% 9.24/2.99  ----------------------
% 9.24/2.99  #Subsume      : 275
% 9.24/2.99  #Demod        : 2941
% 9.24/2.99  #Tautology    : 1805
% 9.24/2.99  #SimpNegUnit  : 11
% 9.24/2.99  #BackRed      : 3
% 9.24/2.99  
% 9.24/2.99  #Partial instantiations: 8190
% 9.24/2.99  #Strategies tried      : 1
% 9.24/2.99  
% 9.24/2.99  Timing (in seconds)
% 9.24/2.99  ----------------------
% 9.24/2.99  Preprocessing        : 0.37
% 9.24/2.99  Parsing              : 0.19
% 9.24/2.99  CNF conversion       : 0.03
% 9.24/2.99  Main loop            : 2.00
% 9.24/2.99  Inferencing          : 0.74
% 9.24/2.99  Reduction            : 0.83
% 9.24/2.99  Demodulation         : 0.72
% 9.24/2.99  BG Simplification    : 0.07
% 9.24/2.99  Subsumption          : 0.26
% 9.24/2.99  Abstraction          : 0.09
% 9.24/2.99  MUC search           : 0.00
% 9.24/2.99  Cooper               : 0.00
% 9.24/2.99  Total                : 2.40
% 9.24/2.99  Index Insertion      : 0.00
% 9.24/3.00  Index Deletion       : 0.00
% 9.24/3.00  Index Matching       : 0.00
% 9.24/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
