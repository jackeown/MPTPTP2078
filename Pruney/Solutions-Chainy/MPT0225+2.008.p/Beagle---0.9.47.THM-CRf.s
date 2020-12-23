%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:32 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 140 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 176 expanded)
%              Number of equality atoms :   55 ( 119 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_97,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6960,plain,(
    ! [A_355,B_356] :
      ( k3_xboole_0(A_355,B_356) = k1_xboole_0
      | ~ r1_xboole_0(A_355,B_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6968,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_6960])).

tff(c_7473,plain,(
    ! [A_385,B_386,C_387] :
      ( ~ r1_xboole_0(A_385,B_386)
      | ~ r2_hidden(C_387,k3_xboole_0(A_385,B_386)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7494,plain,(
    ! [A_19,B_20,C_387] :
      ( ~ r1_xboole_0(k4_xboole_0(A_19,B_20),B_20)
      | ~ r2_hidden(C_387,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6968,c_7473])).

tff(c_7515,plain,(
    ! [C_387] : ~ r2_hidden(C_387,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7494])).

tff(c_6431,plain,(
    ! [A_324,B_325] :
      ( k3_xboole_0(A_324,B_325) = k1_xboole_0
      | ~ r1_xboole_0(A_324,B_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6464,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_6431])).

tff(c_6824,plain,(
    ! [A_335,B_336,C_337] :
      ( ~ r1_xboole_0(A_335,B_336)
      | ~ r2_hidden(C_337,k3_xboole_0(A_335,B_336)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6848,plain,(
    ! [A_19,B_20,C_337] :
      ( ~ r1_xboole_0(k4_xboole_0(A_19,B_20),B_20)
      | ~ r2_hidden(C_337,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6464,c_6824])).

tff(c_6871,plain,(
    ! [C_337] : ~ r2_hidden(C_337,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6848])).

tff(c_66,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_357,plain,(
    ! [A_97,B_98] :
      ( r1_xboole_0(k1_tarski(A_97),k1_tarski(B_98))
      | B_98 = A_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2092,plain,(
    ! [A_226,B_227] :
      ( k3_xboole_0(k1_tarski(A_226),k1_tarski(B_227)) = k1_xboole_0
      | B_227 = A_226 ) ),
    inference(resolution,[status(thm)],[c_357,c_4])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2119,plain,(
    ! [A_226,B_227] :
      ( k4_xboole_0(k1_tarski(A_226),k1_tarski(B_227)) = k5_xboole_0(k1_tarski(A_226),k1_xboole_0)
      | B_227 = A_226 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2092,c_18])).

tff(c_6016,plain,(
    ! [A_291,B_292] :
      ( k4_xboole_0(k1_tarski(A_291),k1_tarski(B_292)) = k1_tarski(A_291)
      | B_292 = A_291 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2119])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_103,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6067,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6016,c_103])).

tff(c_6087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_6067])).

tff(c_6089,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6088,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6192,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6088,c_6088,c_68])).

tff(c_6193,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6192])).

tff(c_6411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6089,c_6193])).

tff(c_6412,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_6192])).

tff(c_6537,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6412,c_6464])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6652,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6537,c_8])).

tff(c_48,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6128,plain,(
    ! [A_298,B_299] : k1_enumset1(A_298,A_298,B_299) = k2_tarski(A_298,B_299) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6146,plain,(
    ! [A_300,B_301] : r2_hidden(A_300,k2_tarski(A_300,B_301)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6128,c_30])).

tff(c_6149,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6146])).

tff(c_6673,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6652,c_6149])).

tff(c_6874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6871,c_6673])).

tff(c_6875,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6876,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6952,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_6875,c_6876,c_70])).

tff(c_6956,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6952,c_22])).

tff(c_6967,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6956,c_6960])).

tff(c_6996,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6967,c_8])).

tff(c_7261,plain,(
    ! [A_372,B_373] : k1_enumset1(A_372,A_372,B_373) = k2_tarski(A_372,B_373) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7279,plain,(
    ! [A_374,B_375] : r2_hidden(A_374,k2_tarski(A_374,B_375)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7261,c_30])).

tff(c_7283,plain,(
    ! [A_376] : r2_hidden(A_376,k1_tarski(A_376)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_7279])).

tff(c_7286,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6996,c_7283])).

tff(c_7518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7515,c_7286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.35  
% 6.06/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.35  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 6.06/2.35  
% 6.06/2.35  %Foreground sorts:
% 6.06/2.35  
% 6.06/2.35  
% 6.06/2.35  %Background operators:
% 6.06/2.35  
% 6.06/2.35  
% 6.06/2.35  %Foreground operators:
% 6.06/2.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.06/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.06/2.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.06/2.35  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.06/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.06/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.35  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.06/2.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.06/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.06/2.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.35  tff('#skF_8', type, '#skF_8': $i).
% 6.06/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.06/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.35  
% 6.06/2.36  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.06/2.36  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.06/2.36  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.06/2.36  tff(f_103, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.06/2.36  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.06/2.36  tff(f_97, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.06/2.36  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.06/2.36  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.06/2.36  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.06/2.36  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.06/2.36  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.06/2.36  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.06/2.36  tff(c_6960, plain, (![A_355, B_356]: (k3_xboole_0(A_355, B_356)=k1_xboole_0 | ~r1_xboole_0(A_355, B_356))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.36  tff(c_6968, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_6960])).
% 6.06/2.36  tff(c_7473, plain, (![A_385, B_386, C_387]: (~r1_xboole_0(A_385, B_386) | ~r2_hidden(C_387, k3_xboole_0(A_385, B_386)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.06/2.36  tff(c_7494, plain, (![A_19, B_20, C_387]: (~r1_xboole_0(k4_xboole_0(A_19, B_20), B_20) | ~r2_hidden(C_387, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6968, c_7473])).
% 6.06/2.36  tff(c_7515, plain, (![C_387]: (~r2_hidden(C_387, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7494])).
% 6.06/2.36  tff(c_6431, plain, (![A_324, B_325]: (k3_xboole_0(A_324, B_325)=k1_xboole_0 | ~r1_xboole_0(A_324, B_325))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.36  tff(c_6464, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_6431])).
% 6.06/2.36  tff(c_6824, plain, (![A_335, B_336, C_337]: (~r1_xboole_0(A_335, B_336) | ~r2_hidden(C_337, k3_xboole_0(A_335, B_336)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.06/2.36  tff(c_6848, plain, (![A_19, B_20, C_337]: (~r1_xboole_0(k4_xboole_0(A_19, B_20), B_20) | ~r2_hidden(C_337, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6464, c_6824])).
% 6.06/2.36  tff(c_6871, plain, (![C_337]: (~r2_hidden(C_337, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6848])).
% 6.06/2.36  tff(c_66, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.06/2.36  tff(c_71, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 6.06/2.36  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.06/2.36  tff(c_357, plain, (![A_97, B_98]: (r1_xboole_0(k1_tarski(A_97), k1_tarski(B_98)) | B_98=A_97)), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.06/2.36  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.36  tff(c_2092, plain, (![A_226, B_227]: (k3_xboole_0(k1_tarski(A_226), k1_tarski(B_227))=k1_xboole_0 | B_227=A_226)), inference(resolution, [status(thm)], [c_357, c_4])).
% 6.06/2.36  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.06/2.36  tff(c_2119, plain, (![A_226, B_227]: (k4_xboole_0(k1_tarski(A_226), k1_tarski(B_227))=k5_xboole_0(k1_tarski(A_226), k1_xboole_0) | B_227=A_226)), inference(superposition, [status(thm), theory('equality')], [c_2092, c_18])).
% 6.06/2.36  tff(c_6016, plain, (![A_291, B_292]: (k4_xboole_0(k1_tarski(A_291), k1_tarski(B_292))=k1_tarski(A_291) | B_292=A_291)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2119])).
% 6.06/2.36  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.06/2.36  tff(c_103, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 6.06/2.36  tff(c_6067, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6016, c_103])).
% 6.06/2.36  tff(c_6087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_6067])).
% 6.06/2.36  tff(c_6089, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 6.06/2.36  tff(c_6088, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 6.06/2.36  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.06/2.36  tff(c_6192, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6088, c_6088, c_68])).
% 6.06/2.36  tff(c_6193, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_6192])).
% 6.06/2.36  tff(c_6411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6089, c_6193])).
% 6.06/2.36  tff(c_6412, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_6192])).
% 6.06/2.36  tff(c_6537, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6412, c_6464])).
% 6.06/2.36  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.36  tff(c_6652, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6537, c_8])).
% 6.06/2.36  tff(c_48, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.06/2.36  tff(c_6128, plain, (![A_298, B_299]: (k1_enumset1(A_298, A_298, B_299)=k2_tarski(A_298, B_299))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.06/2.36  tff(c_30, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.06/2.36  tff(c_6146, plain, (![A_300, B_301]: (r2_hidden(A_300, k2_tarski(A_300, B_301)))), inference(superposition, [status(thm), theory('equality')], [c_6128, c_30])).
% 6.06/2.36  tff(c_6149, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6146])).
% 6.06/2.36  tff(c_6673, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6652, c_6149])).
% 6.06/2.36  tff(c_6874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6871, c_6673])).
% 6.06/2.36  tff(c_6875, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.36  tff(c_6876, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.36  tff(c_70, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.06/2.36  tff(c_6952, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_6875, c_6876, c_70])).
% 6.06/2.36  tff(c_6956, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6952, c_22])).
% 6.06/2.36  tff(c_6967, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_6956, c_6960])).
% 6.06/2.36  tff(c_6996, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6967, c_8])).
% 6.06/2.36  tff(c_7261, plain, (![A_372, B_373]: (k1_enumset1(A_372, A_372, B_373)=k2_tarski(A_372, B_373))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.06/2.36  tff(c_7279, plain, (![A_374, B_375]: (r2_hidden(A_374, k2_tarski(A_374, B_375)))), inference(superposition, [status(thm), theory('equality')], [c_7261, c_30])).
% 6.06/2.36  tff(c_7283, plain, (![A_376]: (r2_hidden(A_376, k1_tarski(A_376)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_7279])).
% 6.06/2.36  tff(c_7286, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6996, c_7283])).
% 6.06/2.36  tff(c_7518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7515, c_7286])).
% 6.06/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.36  
% 6.06/2.36  Inference rules
% 6.06/2.36  ----------------------
% 6.06/2.36  #Ref     : 0
% 6.06/2.36  #Sup     : 1768
% 6.06/2.36  #Fact    : 18
% 6.06/2.36  #Define  : 0
% 6.06/2.36  #Split   : 4
% 6.06/2.36  #Chain   : 0
% 6.06/2.36  #Close   : 0
% 6.06/2.36  
% 6.06/2.36  Ordering : KBO
% 6.06/2.36  
% 6.06/2.36  Simplification rules
% 6.06/2.36  ----------------------
% 6.06/2.36  #Subsume      : 134
% 6.06/2.36  #Demod        : 1839
% 6.06/2.36  #Tautology    : 1117
% 6.06/2.36  #SimpNegUnit  : 104
% 6.06/2.36  #BackRed      : 11
% 6.06/2.36  
% 6.06/2.36  #Partial instantiations: 0
% 6.06/2.36  #Strategies tried      : 1
% 6.06/2.36  
% 6.06/2.36  Timing (in seconds)
% 6.06/2.36  ----------------------
% 6.42/2.37  Preprocessing        : 0.33
% 6.42/2.37  Parsing              : 0.17
% 6.42/2.37  CNF conversion       : 0.03
% 6.42/2.37  Main loop            : 1.28
% 6.42/2.37  Inferencing          : 0.38
% 6.42/2.37  Reduction            : 0.58
% 6.42/2.37  Demodulation         : 0.47
% 6.42/2.37  BG Simplification    : 0.05
% 6.42/2.37  Subsumption          : 0.19
% 6.42/2.37  Abstraction          : 0.08
% 6.42/2.37  MUC search           : 0.00
% 6.42/2.37  Cooper               : 0.00
% 6.42/2.37  Total                : 1.64
% 6.42/2.37  Index Insertion      : 0.00
% 6.42/2.37  Index Deletion       : 0.00
% 6.42/2.37  Index Matching       : 0.00
% 6.42/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
