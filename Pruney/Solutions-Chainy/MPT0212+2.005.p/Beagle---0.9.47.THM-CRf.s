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
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 56.42s
% Output     : CNFRefutation 56.42s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 208 expanded)
%              Number of equality atoms :   62 ( 146 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_77,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_151])).

tff(c_165,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [A_82] : k5_xboole_0(k1_xboole_0,A_82) = k2_xboole_0(k1_xboole_0,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_20])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_4] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_4)) = k4_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_6])).

tff(c_209,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_184])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_163,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_1666,plain,(
    ! [A_163,B_164] :
      ( r1_tarski('#skF_3'(A_163,B_164),A_163)
      | ~ r1_tarski('#skF_4'(A_163,B_164),A_163)
      | k1_zfmisc_1(A_163) = B_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1676,plain,(
    ! [B_165] :
      ( '#skF_3'(k1_xboole_0,B_165) = k1_xboole_0
      | ~ r1_tarski('#skF_4'(k1_xboole_0,B_165),k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = B_165 ) ),
    inference(resolution,[status(thm)],[c_1666,c_14])).

tff(c_1679,plain,(
    ! [B_165] :
      ( '#skF_3'(k1_xboole_0,B_165) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = B_165
      | k4_xboole_0('#skF_4'(k1_xboole_0,B_165),k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_1676])).

tff(c_1684,plain,(
    ! [B_166] :
      ( '#skF_3'(k1_xboole_0,B_166) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = B_166
      | '#skF_4'(k1_xboole_0,B_166) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1679])).

tff(c_1843,plain,(
    ! [B_166] :
      ( k1_tarski(k1_xboole_0) != B_166
      | '#skF_3'(k1_xboole_0,B_166) = k1_xboole_0
      | '#skF_4'(k1_xboole_0,B_166) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1684,c_60])).

tff(c_1862,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) != k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1843])).

tff(c_1864,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1862])).

tff(c_24,plain,(
    ! [C_22] : r2_hidden(C_22,k1_tarski(C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1499,plain,(
    ! [A_158,B_159] :
      ( r1_tarski('#skF_3'(A_158,B_159),A_158)
      | r2_hidden('#skF_4'(A_158,B_159),B_159)
      | k1_zfmisc_1(A_158) = B_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4900,plain,(
    ! [A_4718,A_4719] :
      ( '#skF_4'(A_4718,k1_tarski(A_4719)) = A_4719
      | r1_tarski('#skF_3'(A_4718,k1_tarski(A_4719)),A_4718)
      | k1_zfmisc_1(A_4718) = k1_tarski(A_4719) ) ),
    inference(resolution,[status(thm)],[c_1499,c_22])).

tff(c_4927,plain,(
    ! [A_4773] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(A_4773)) = k1_xboole_0
      | '#skF_4'(k1_xboole_0,k1_tarski(A_4773)) = A_4773
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_4773) ) ),
    inference(resolution,[status(thm)],[c_4900,c_14])).

tff(c_56,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_3'(A_51,B_52),B_52)
      | r2_hidden('#skF_4'(A_51,B_52),B_52)
      | k1_zfmisc_1(A_51) = B_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159123,plain,(
    ! [A_20206] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(A_20206))
      | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_20206)),k1_tarski(A_20206))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_20206)
      | '#skF_4'(k1_xboole_0,k1_tarski(A_20206)) = A_20206
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_20206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4927,c_56])).

tff(c_159149,plain,(
    ! [A_20260] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(A_20260))
      | '#skF_4'(k1_xboole_0,k1_tarski(A_20260)) = A_20260
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_20260) ) ),
    inference(resolution,[status(thm)],[c_159123,c_22])).

tff(c_159161,plain,
    ( '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_159149])).

tff(c_159165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1864,c_159161])).

tff(c_159167,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1862])).

tff(c_159166,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1862])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_3'(A_51,B_52),B_52)
      | ~ r1_tarski('#skF_4'(A_51,B_52),A_51)
      | k1_zfmisc_1(A_51) = B_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159177,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159166,c_52])).

tff(c_159191,plain,
    ( ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159177])).

tff(c_159192,plain,(
    ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_159191])).

tff(c_159214,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159167,c_159192])).

tff(c_159217,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_159214])).

tff(c_159221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_159217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.42/43.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/43.83  
% 56.42/43.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/43.83  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 56.42/43.83  
% 56.42/43.83  %Foreground sorts:
% 56.42/43.83  
% 56.42/43.83  
% 56.42/43.83  %Background operators:
% 56.42/43.83  
% 56.42/43.83  
% 56.42/43.83  %Foreground operators:
% 56.42/43.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.42/43.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 56.42/43.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 56.42/43.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.42/43.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 56.42/43.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 56.42/43.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 56.42/43.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 56.42/43.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.42/43.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 56.42/43.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 56.42/43.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 56.42/43.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 56.42/43.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.42/43.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 56.42/43.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.42/43.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.42/43.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 56.42/43.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 56.42/43.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 56.42/43.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 56.42/43.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 56.42/43.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 56.42/43.83  
% 56.42/43.85  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 56.42/43.85  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 56.42/43.85  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 56.42/43.85  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 56.42/43.85  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 56.42/43.85  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 56.42/43.85  tff(f_77, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 56.42/43.85  tff(f_75, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 56.42/43.85  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 56.42/43.85  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 56.42/43.85  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.42/43.85  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.42/43.85  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.42/43.85  tff(c_151, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.42/43.85  tff(c_160, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_151])).
% 56.42/43.85  tff(c_165, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 56.42/43.85  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.42/43.85  tff(c_177, plain, (![A_82]: (k5_xboole_0(k1_xboole_0, A_82)=k2_xboole_0(k1_xboole_0, A_82))), inference(superposition, [status(thm), theory('equality')], [c_165, c_20])).
% 56.42/43.85  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.42/43.85  tff(c_184, plain, (![B_4]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_4))=k4_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_177, c_6])).
% 56.42/43.85  tff(c_209, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_184])).
% 56.42/43.85  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.42/43.85  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 56.42/43.85  tff(c_163, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 56.42/43.85  tff(c_1666, plain, (![A_163, B_164]: (r1_tarski('#skF_3'(A_163, B_164), A_163) | ~r1_tarski('#skF_4'(A_163, B_164), A_163) | k1_zfmisc_1(A_163)=B_164)), inference(cnfTransformation, [status(thm)], [f_75])).
% 56.42/43.85  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.42/43.85  tff(c_1676, plain, (![B_165]: ('#skF_3'(k1_xboole_0, B_165)=k1_xboole_0 | ~r1_tarski('#skF_4'(k1_xboole_0, B_165), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=B_165)), inference(resolution, [status(thm)], [c_1666, c_14])).
% 56.42/43.85  tff(c_1679, plain, (![B_165]: ('#skF_3'(k1_xboole_0, B_165)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=B_165 | k4_xboole_0('#skF_4'(k1_xboole_0, B_165), k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1676])).
% 56.42/43.85  tff(c_1684, plain, (![B_166]: ('#skF_3'(k1_xboole_0, B_166)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=B_166 | '#skF_4'(k1_xboole_0, B_166)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1679])).
% 56.42/43.85  tff(c_1843, plain, (![B_166]: (k1_tarski(k1_xboole_0)!=B_166 | '#skF_3'(k1_xboole_0, B_166)=k1_xboole_0 | '#skF_4'(k1_xboole_0, B_166)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1684, c_60])).
% 56.42/43.85  tff(c_1862, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | '#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))!=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_1843])).
% 56.42/43.85  tff(c_1864, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1862])).
% 56.42/43.85  tff(c_24, plain, (![C_22]: (r2_hidden(C_22, k1_tarski(C_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 56.42/43.85  tff(c_1499, plain, (![A_158, B_159]: (r1_tarski('#skF_3'(A_158, B_159), A_158) | r2_hidden('#skF_4'(A_158, B_159), B_159) | k1_zfmisc_1(A_158)=B_159)), inference(cnfTransformation, [status(thm)], [f_75])).
% 56.42/43.85  tff(c_22, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 56.42/43.85  tff(c_4900, plain, (![A_4718, A_4719]: ('#skF_4'(A_4718, k1_tarski(A_4719))=A_4719 | r1_tarski('#skF_3'(A_4718, k1_tarski(A_4719)), A_4718) | k1_zfmisc_1(A_4718)=k1_tarski(A_4719))), inference(resolution, [status(thm)], [c_1499, c_22])).
% 56.42/43.85  tff(c_4927, plain, (![A_4773]: ('#skF_3'(k1_xboole_0, k1_tarski(A_4773))=k1_xboole_0 | '#skF_4'(k1_xboole_0, k1_tarski(A_4773))=A_4773 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_4773))), inference(resolution, [status(thm)], [c_4900, c_14])).
% 56.42/43.85  tff(c_56, plain, (![A_51, B_52]: (~r2_hidden('#skF_3'(A_51, B_52), B_52) | r2_hidden('#skF_4'(A_51, B_52), B_52) | k1_zfmisc_1(A_51)=B_52)), inference(cnfTransformation, [status(thm)], [f_75])).
% 56.42/43.85  tff(c_159123, plain, (![A_20206]: (~r2_hidden(k1_xboole_0, k1_tarski(A_20206)) | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_20206)), k1_tarski(A_20206)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_20206) | '#skF_4'(k1_xboole_0, k1_tarski(A_20206))=A_20206 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_20206))), inference(superposition, [status(thm), theory('equality')], [c_4927, c_56])).
% 56.42/43.85  tff(c_159149, plain, (![A_20260]: (~r2_hidden(k1_xboole_0, k1_tarski(A_20260)) | '#skF_4'(k1_xboole_0, k1_tarski(A_20260))=A_20260 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_20260))), inference(resolution, [status(thm)], [c_159123, c_22])).
% 56.42/43.85  tff(c_159161, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_159149])).
% 56.42/43.85  tff(c_159165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1864, c_159161])).
% 56.42/43.85  tff(c_159167, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1862])).
% 56.42/43.85  tff(c_159166, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1862])).
% 56.42/43.85  tff(c_52, plain, (![A_51, B_52]: (~r2_hidden('#skF_3'(A_51, B_52), B_52) | ~r1_tarski('#skF_4'(A_51, B_52), A_51) | k1_zfmisc_1(A_51)=B_52)), inference(cnfTransformation, [status(thm)], [f_75])).
% 56.42/43.85  tff(c_159177, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | ~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159166, c_52])).
% 56.42/43.85  tff(c_159191, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159177])).
% 56.42/43.85  tff(c_159192, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_60, c_159191])).
% 56.42/43.85  tff(c_159214, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_159167, c_159192])).
% 56.42/43.85  tff(c_159217, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_159214])).
% 56.42/43.85  tff(c_159221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_159217])).
% 56.42/43.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.42/43.85  
% 56.42/43.85  Inference rules
% 56.42/43.85  ----------------------
% 56.42/43.85  #Ref     : 1
% 56.42/43.85  #Sup     : 38184
% 56.42/43.85  #Fact    : 2
% 56.42/43.85  #Define  : 0
% 56.42/43.85  #Split   : 5
% 56.42/43.85  #Chain   : 0
% 56.42/43.85  #Close   : 0
% 56.42/43.85  
% 56.42/43.85  Ordering : KBO
% 56.42/43.85  
% 56.42/43.85  Simplification rules
% 56.42/43.85  ----------------------
% 56.42/43.85  #Subsume      : 3334
% 56.42/43.85  #Demod        : 67348
% 56.42/43.85  #Tautology    : 13971
% 56.42/43.85  #SimpNegUnit  : 74
% 56.42/43.85  #BackRed      : 0
% 56.42/43.85  
% 56.42/43.85  #Partial instantiations: 2548
% 56.42/43.85  #Strategies tried      : 1
% 56.42/43.85  
% 56.42/43.85  Timing (in seconds)
% 56.42/43.85  ----------------------
% 56.42/43.85  Preprocessing        : 0.35
% 56.42/43.85  Parsing              : 0.18
% 56.42/43.85  CNF conversion       : 0.02
% 56.42/43.85  Main loop            : 42.73
% 56.42/43.85  Inferencing          : 6.37
% 56.42/43.85  Reduction            : 27.28
% 56.42/43.85  Demodulation         : 25.21
% 56.42/43.85  BG Simplification    : 1.14
% 56.42/43.85  Subsumption          : 6.86
% 56.42/43.85  Abstraction          : 2.71
% 56.42/43.85  MUC search           : 0.00
% 56.42/43.85  Cooper               : 0.00
% 56.42/43.85  Total                : 43.12
% 56.42/43.85  Index Insertion      : 0.00
% 56.42/43.85  Index Deletion       : 0.00
% 56.42/43.85  Index Matching       : 0.00
% 56.42/43.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
