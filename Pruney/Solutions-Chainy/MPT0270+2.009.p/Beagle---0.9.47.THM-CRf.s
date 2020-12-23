%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:54 EST 2020

% Result     : Theorem 9.30s
% Output     : CNFRefutation 9.30s
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
    ! [A_86,B_87] :
      ( r1_xboole_0(k1_tarski(A_86),B_87)
      | r2_hidden(A_86,B_87) ) ),
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
    ! [A_120,B_121] : k3_tarski(k2_tarski(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_299,plain,(
    ! [A_125,B_126] : k3_tarski(k2_tarski(A_125,B_126)) = k2_xboole_0(B_126,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_80,plain,(
    ! [A_88,B_89] : k3_tarski(k2_tarski(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_305,plain,(
    ! [B_126,A_125] : k2_xboole_0(B_126,A_125) = k2_xboole_0(A_125,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_80])).

tff(c_541,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(k2_xboole_0(A_142,B_143),B_143) = A_142
      | ~ r1_xboole_0(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2328,plain,(
    ! [B_251,A_252] :
      ( k4_xboole_0(k2_xboole_0(B_251,A_252),B_251) = A_252
      | ~ r1_xboole_0(A_252,B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2398,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(k4_xboole_0(B_14,A_13),A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2328])).

tff(c_2417,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2398])).

tff(c_570,plain,(
    ! [B_126,A_125] :
      ( k4_xboole_0(k2_xboole_0(B_126,A_125),B_126) = A_125
      | ~ r1_xboole_0(A_125,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_541])).

tff(c_2509,plain,(
    ! [A_255,B_256] :
      ( k4_xboole_0(A_255,B_256) = A_255
      | ~ r1_xboole_0(A_255,B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_570])).

tff(c_12516,plain,(
    ! [A_21244,B_21245] :
      ( k4_xboole_0(k1_tarski(A_21244),B_21245) = k1_tarski(A_21244)
      | r2_hidden(A_21244,B_21245) ) ),
    inference(resolution,[status(thm)],[c_78,c_2509])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_12618,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12516,c_169])).

tff(c_12678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_12618])).

tff(c_12679,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_64,plain,(
    ! [A_58] : k2_tarski(A_58,A_58) = k1_tarski(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12725,plain,(
    ! [A_21424,B_21425] : k1_enumset1(A_21424,A_21424,B_21425) = k2_tarski(A_21424,B_21425) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [E_38,A_32,C_34] : r2_hidden(E_38,k1_enumset1(A_32,E_38,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12743,plain,(
    ! [A_21426,B_21427] : r2_hidden(A_21426,k2_tarski(A_21426,B_21427)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12725,c_38])).

tff(c_12752,plain,(
    ! [A_58] : r2_hidden(A_58,k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_12743])).

tff(c_12680,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12836,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12680,c_88])).

tff(c_12840,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12836,c_22])).

tff(c_13145,plain,(
    ! [A_21455,B_21456,C_21457] :
      ( ~ r1_xboole_0(A_21455,B_21456)
      | ~ r2_hidden(C_21457,B_21456)
      | ~ r2_hidden(C_21457,A_21455) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13263,plain,(
    ! [C_21463] :
      ( ~ r2_hidden(C_21463,'#skF_7')
      | ~ r2_hidden(C_21463,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12840,c_13145])).

tff(c_13275,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12752,c_13263])).

tff(c_13281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12679,c_13275])).

tff(c_13282,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_13321,plain,(
    ! [A_21477,B_21478] : k1_enumset1(A_21477,A_21477,B_21478) = k2_tarski(A_21477,B_21478) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [E_38,B_33,C_34] : r2_hidden(E_38,k1_enumset1(E_38,B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13339,plain,(
    ! [A_21479,B_21480] : r2_hidden(A_21479,k2_tarski(A_21479,B_21480)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13321,c_40])).

tff(c_13348,plain,(
    ! [A_58] : r2_hidden(A_58,k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_13339])).

tff(c_13283,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_13350,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13283,c_90])).

tff(c_13354,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13350,c_22])).

tff(c_13822,plain,(
    ! [A_21516,B_21517,C_21518] :
      ( ~ r1_xboole_0(A_21516,B_21517)
      | ~ r2_hidden(C_21518,B_21517)
      | ~ r2_hidden(C_21518,A_21516) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14043,plain,(
    ! [C_21526] :
      ( ~ r2_hidden(C_21526,'#skF_7')
      | ~ r2_hidden(C_21526,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_13354,c_13822])).

tff(c_14055,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_13348,c_14043])).

tff(c_14061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13282,c_14055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.30/3.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.11  
% 9.30/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.11  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.30/3.11  
% 9.30/3.11  %Foreground sorts:
% 9.30/3.11  
% 9.30/3.11  
% 9.30/3.11  %Background operators:
% 9.30/3.11  
% 9.30/3.11  
% 9.30/3.11  %Foreground operators:
% 9.30/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.30/3.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.30/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.30/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.30/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.30/3.11  tff('#skF_7', type, '#skF_7': $i).
% 9.30/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.30/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.30/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.30/3.11  tff('#skF_5', type, '#skF_5': $i).
% 9.30/3.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.30/3.11  tff('#skF_6', type, '#skF_6': $i).
% 9.30/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.30/3.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.30/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.30/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.30/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.30/3.11  tff('#skF_4', type, '#skF_4': $i).
% 9.30/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.30/3.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.30/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.30/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.30/3.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.30/3.11  
% 9.30/3.12  tff(f_121, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 9.30/3.12  tff(f_111, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.30/3.12  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.30/3.12  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.30/3.12  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.30/3.12  tff(f_113, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.30/3.12  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.30/3.12  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.30/3.12  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.30/3.12  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.30/3.12  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.30/3.12  tff(c_86, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.30/3.12  tff(c_168, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 9.30/3.12  tff(c_78, plain, (![A_86, B_87]: (r1_xboole_0(k1_tarski(A_86), B_87) | r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.30/3.12  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.30/3.12  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.12  tff(c_32, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.30/3.12  tff(c_252, plain, (![A_120, B_121]: (k3_tarski(k2_tarski(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.30/3.12  tff(c_299, plain, (![A_125, B_126]: (k3_tarski(k2_tarski(A_125, B_126))=k2_xboole_0(B_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_32, c_252])).
% 9.30/3.12  tff(c_80, plain, (![A_88, B_89]: (k3_tarski(k2_tarski(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.30/3.12  tff(c_305, plain, (![B_126, A_125]: (k2_xboole_0(B_126, A_125)=k2_xboole_0(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_299, c_80])).
% 9.30/3.12  tff(c_541, plain, (![A_142, B_143]: (k4_xboole_0(k2_xboole_0(A_142, B_143), B_143)=A_142 | ~r1_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.30/3.12  tff(c_2328, plain, (![B_251, A_252]: (k4_xboole_0(k2_xboole_0(B_251, A_252), B_251)=A_252 | ~r1_xboole_0(A_252, B_251))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.30/3.12  tff(c_2398, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13) | ~r1_xboole_0(k4_xboole_0(B_14, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2328])).
% 9.30/3.12  tff(c_2417, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2398])).
% 9.30/3.12  tff(c_570, plain, (![B_126, A_125]: (k4_xboole_0(k2_xboole_0(B_126, A_125), B_126)=A_125 | ~r1_xboole_0(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_305, c_541])).
% 9.30/3.12  tff(c_2509, plain, (![A_255, B_256]: (k4_xboole_0(A_255, B_256)=A_255 | ~r1_xboole_0(A_255, B_256))), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_570])).
% 9.30/3.12  tff(c_12516, plain, (![A_21244, B_21245]: (k4_xboole_0(k1_tarski(A_21244), B_21245)=k1_tarski(A_21244) | r2_hidden(A_21244, B_21245))), inference(resolution, [status(thm)], [c_78, c_2509])).
% 9.30/3.12  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.30/3.12  tff(c_169, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 9.30/3.12  tff(c_12618, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12516, c_169])).
% 9.30/3.12  tff(c_12678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_12618])).
% 9.30/3.12  tff(c_12679, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 9.30/3.12  tff(c_64, plain, (![A_58]: (k2_tarski(A_58, A_58)=k1_tarski(A_58))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.30/3.12  tff(c_12725, plain, (![A_21424, B_21425]: (k1_enumset1(A_21424, A_21424, B_21425)=k2_tarski(A_21424, B_21425))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.30/3.12  tff(c_38, plain, (![E_38, A_32, C_34]: (r2_hidden(E_38, k1_enumset1(A_32, E_38, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.30/3.12  tff(c_12743, plain, (![A_21426, B_21427]: (r2_hidden(A_21426, k2_tarski(A_21426, B_21427)))), inference(superposition, [status(thm), theory('equality')], [c_12725, c_38])).
% 9.30/3.12  tff(c_12752, plain, (![A_58]: (r2_hidden(A_58, k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_12743])).
% 9.30/3.12  tff(c_12680, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 9.30/3.12  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.30/3.12  tff(c_12836, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12680, c_88])).
% 9.30/3.12  tff(c_12840, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12836, c_22])).
% 9.30/3.12  tff(c_13145, plain, (![A_21455, B_21456, C_21457]: (~r1_xboole_0(A_21455, B_21456) | ~r2_hidden(C_21457, B_21456) | ~r2_hidden(C_21457, A_21455))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.12  tff(c_13263, plain, (![C_21463]: (~r2_hidden(C_21463, '#skF_7') | ~r2_hidden(C_21463, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_12840, c_13145])).
% 9.30/3.12  tff(c_13275, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12752, c_13263])).
% 9.30/3.12  tff(c_13281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12679, c_13275])).
% 9.30/3.12  tff(c_13282, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 9.30/3.12  tff(c_13321, plain, (![A_21477, B_21478]: (k1_enumset1(A_21477, A_21477, B_21478)=k2_tarski(A_21477, B_21478))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.30/3.12  tff(c_40, plain, (![E_38, B_33, C_34]: (r2_hidden(E_38, k1_enumset1(E_38, B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.30/3.12  tff(c_13339, plain, (![A_21479, B_21480]: (r2_hidden(A_21479, k2_tarski(A_21479, B_21480)))), inference(superposition, [status(thm), theory('equality')], [c_13321, c_40])).
% 9.30/3.12  tff(c_13348, plain, (![A_58]: (r2_hidden(A_58, k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_13339])).
% 9.30/3.12  tff(c_13283, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 9.30/3.12  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.30/3.12  tff(c_13350, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13283, c_90])).
% 9.30/3.12  tff(c_13354, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13350, c_22])).
% 9.30/3.12  tff(c_13822, plain, (![A_21516, B_21517, C_21518]: (~r1_xboole_0(A_21516, B_21517) | ~r2_hidden(C_21518, B_21517) | ~r2_hidden(C_21518, A_21516))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.12  tff(c_14043, plain, (![C_21526]: (~r2_hidden(C_21526, '#skF_7') | ~r2_hidden(C_21526, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_13354, c_13822])).
% 9.30/3.12  tff(c_14055, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_13348, c_14043])).
% 9.30/3.12  tff(c_14061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13282, c_14055])).
% 9.30/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.12  
% 9.30/3.12  Inference rules
% 9.30/3.12  ----------------------
% 9.30/3.12  #Ref     : 0
% 9.30/3.12  #Sup     : 2950
% 9.30/3.12  #Fact    : 18
% 9.30/3.12  #Define  : 0
% 9.30/3.12  #Split   : 2
% 9.30/3.12  #Chain   : 0
% 9.30/3.12  #Close   : 0
% 9.30/3.12  
% 9.30/3.12  Ordering : KBO
% 9.30/3.12  
% 9.30/3.12  Simplification rules
% 9.30/3.12  ----------------------
% 9.30/3.12  #Subsume      : 258
% 9.30/3.12  #Demod        : 2575
% 9.30/3.12  #Tautology    : 1623
% 9.30/3.12  #SimpNegUnit  : 11
% 9.30/3.12  #BackRed      : 3
% 9.30/3.12  
% 9.30/3.12  #Partial instantiations: 8001
% 9.30/3.12  #Strategies tried      : 1
% 9.30/3.12  
% 9.30/3.12  Timing (in seconds)
% 9.30/3.12  ----------------------
% 9.30/3.13  Preprocessing        : 0.38
% 9.30/3.13  Parsing              : 0.20
% 9.30/3.13  CNF conversion       : 0.03
% 9.30/3.13  Main loop            : 1.92
% 9.30/3.13  Inferencing          : 0.72
% 9.30/3.13  Reduction            : 0.80
% 9.30/3.13  Demodulation         : 0.68
% 9.30/3.13  BG Simplification    : 0.07
% 9.30/3.13  Subsumption          : 0.23
% 9.30/3.13  Abstraction          : 0.09
% 9.30/3.13  MUC search           : 0.00
% 9.30/3.13  Cooper               : 0.00
% 9.30/3.13  Total                : 2.34
% 9.30/3.13  Index Insertion      : 0.00
% 9.30/3.13  Index Deletion       : 0.00
% 9.30/3.13  Index Matching       : 0.00
% 9.30/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
