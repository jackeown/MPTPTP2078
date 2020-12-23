%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 187 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 393 expanded)
%              Number of equality atoms :   74 ( 285 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_52,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_73,plain,(
    ! [A_52,B_53] : r1_tarski(k4_xboole_0(A_52,B_53),A_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_55,plain,(
    ! [A_49] : k2_tarski(A_49,A_49) = k1_tarski(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_49] : r2_hidden(A_49,k1_tarski(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_50,plain,(
    ! [A_40,B_41] :
      ( r1_tarski('#skF_3'(A_40,B_41),A_40)
      | r2_hidden('#skF_4'(A_40,B_41),B_41)
      | k1_zfmisc_1(A_40) = B_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_6,B_7,C_8] :
      ( '#skF_1'(A_6,B_7,C_8) = B_7
      | '#skF_1'(A_6,B_7,C_8) = A_6
      | '#skF_2'(A_6,B_7,C_8) != B_7
      | k2_tarski(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_310,plain,(
    ! [B_7,C_8] :
      ( '#skF_2'(B_7,B_7,C_8) != B_7
      | k2_tarski(B_7,B_7) = C_8
      | '#skF_1'(B_7,B_7,C_8) = B_7 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_16])).

tff(c_692,plain,(
    ! [B_2098,C_2099] :
      ( '#skF_2'(B_2098,B_2098,C_2099) != B_2098
      | k1_tarski(B_2098) = C_2099
      | '#skF_1'(B_2098,B_2098,C_2099) = B_2098 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310])).

tff(c_118,plain,(
    ! [D_63,B_64,A_65] :
      ( D_63 = B_64
      | D_63 = A_65
      | ~ r2_hidden(D_63,k2_tarski(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_121,plain,(
    ! [D_63,A_12] :
      ( D_63 = A_12
      | D_63 = A_12
      | ~ r2_hidden(D_63,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_1639,plain,(
    ! [D_6558,B_6559,C_6560] :
      ( D_6558 = B_6559
      | D_6558 = B_6559
      | ~ r2_hidden(D_6558,C_6560)
      | '#skF_2'(B_6559,B_6559,C_6560) != B_6559
      | '#skF_1'(B_6559,B_6559,C_6560) = B_6559 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_121])).

tff(c_4538,plain,(
    ! [B_14467,A_14468,B_14469] :
      ( B_14467 = '#skF_4'(A_14468,B_14469)
      | '#skF_2'(B_14467,B_14467,B_14469) != B_14467
      | '#skF_1'(B_14467,B_14467,B_14469) = B_14467
      | r1_tarski('#skF_3'(A_14468,B_14469),A_14468)
      | k1_zfmisc_1(A_14468) = B_14469 ) ),
    inference(resolution,[status(thm)],[c_50,c_1639])).

tff(c_5616,plain,(
    ! [B_18286,B_18287] :
      ( '#skF_3'(k1_xboole_0,B_18286) = k1_xboole_0
      | B_18287 = '#skF_4'(k1_xboole_0,B_18286)
      | '#skF_2'(B_18287,B_18287,B_18286) != B_18287
      | '#skF_1'(B_18287,B_18287,B_18286) = B_18287
      | k1_zfmisc_1(k1_xboole_0) = B_18286 ) ),
    inference(resolution,[status(thm)],[c_4538,c_6])).

tff(c_6248,plain,(
    ! [B_18286,B_18287] :
      ( k1_tarski(k1_xboole_0) != B_18286
      | '#skF_3'(k1_xboole_0,B_18286) = k1_xboole_0
      | B_18287 = '#skF_4'(k1_xboole_0,B_18286)
      | '#skF_2'(B_18287,B_18287,B_18286) != B_18287
      | '#skF_1'(B_18287,B_18287,B_18286) = B_18287 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5616,c_52])).

tff(c_6377,plain,(
    ! [B_18287] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
      | B_18287 = '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0))
      | '#skF_2'(B_18287,B_18287,k1_tarski(k1_xboole_0)) != B_18287
      | '#skF_1'(B_18287,B_18287,k1_tarski(k1_xboole_0)) = B_18287 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6248])).

tff(c_7614,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6377])).

tff(c_48,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_3'(A_40,B_41),B_41)
      | r2_hidden('#skF_4'(A_40,B_41),B_41)
      | k1_zfmisc_1(A_40) = B_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7633,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7614,c_48])).

tff(c_7687,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_7633])).

tff(c_7688,plain,(
    r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7687])).

tff(c_7823,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7688,c_121])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_3'(A_40,B_41),B_41)
      | ~ r1_tarski('#skF_4'(A_40,B_41),A_40)
      | k1_zfmisc_1(A_40) = B_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7630,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7614,c_44])).

tff(c_7684,plain,
    ( ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_7630])).

tff(c_7685,plain,(
    ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7684])).

tff(c_7825,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7823,c_7685])).

tff(c_7829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7825])).

tff(c_7831,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6377])).

tff(c_183,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_3'(A_87,B_88),A_87)
      | r2_hidden('#skF_4'(A_87,B_88),B_88)
      | k1_zfmisc_1(A_87) = B_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_222,plain,(
    ! [A_101,A_102] :
      ( '#skF_4'(A_101,k1_tarski(A_102)) = A_102
      | r1_tarski('#skF_3'(A_101,k1_tarski(A_102)),A_101)
      | k1_zfmisc_1(A_101) = k1_tarski(A_102) ) ),
    inference(resolution,[status(thm)],[c_183,c_121])).

tff(c_227,plain,(
    ! [A_102] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(A_102)) = k1_xboole_0
      | '#skF_4'(k1_xboole_0,k1_tarski(A_102)) = A_102
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_102) ) ),
    inference(resolution,[status(thm)],[c_222,c_6])).

tff(c_7847,plain,
    ( '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_7831])).

tff(c_7850,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7847])).

tff(c_176,plain,(
    ! [A_84,B_85] :
      ( r1_tarski('#skF_3'(A_84,B_85),A_84)
      | ~ r1_tarski('#skF_4'(A_84,B_85),A_84)
      | k1_zfmisc_1(A_84) = B_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_181,plain,(
    ! [B_85] :
      ( '#skF_3'(k1_xboole_0,B_85) = k1_xboole_0
      | ~ r1_tarski('#skF_4'(k1_xboole_0,B_85),k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = B_85 ) ),
    inference(resolution,[status(thm)],[c_176,c_6])).

tff(c_7959,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7850,c_181])).

tff(c_8035,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7959])).

tff(c_8037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7831,c_8035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.43  
% 7.05/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.43  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 7.05/2.43  
% 7.05/2.43  %Foreground sorts:
% 7.05/2.43  
% 7.05/2.43  
% 7.05/2.43  %Background operators:
% 7.05/2.43  
% 7.05/2.43  
% 7.05/2.43  %Foreground operators:
% 7.05/2.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.05/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.05/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.05/2.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.05/2.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.05/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.05/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.05/2.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.05/2.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.05/2.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.05/2.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.05/2.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.05/2.43  
% 7.05/2.45  tff(f_65, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 7.05/2.45  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.05/2.45  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.05/2.45  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.05/2.45  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.05/2.45  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.05/2.45  tff(c_52, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.05/2.45  tff(c_73, plain, (![A_52, B_53]: (r1_tarski(k4_xboole_0(A_52, B_53), A_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.05/2.45  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.05/2.45  tff(c_79, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_6])).
% 7.05/2.45  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.05/2.45  tff(c_84, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 7.05/2.45  tff(c_55, plain, (![A_49]: (k2_tarski(A_49, A_49)=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.05/2.45  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.05/2.45  tff(c_61, plain, (![A_49]: (r2_hidden(A_49, k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 7.05/2.45  tff(c_50, plain, (![A_40, B_41]: (r1_tarski('#skF_3'(A_40, B_41), A_40) | r2_hidden('#skF_4'(A_40, B_41), B_41) | k1_zfmisc_1(A_40)=B_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.05/2.45  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.05/2.45  tff(c_16, plain, (![A_6, B_7, C_8]: ('#skF_1'(A_6, B_7, C_8)=B_7 | '#skF_1'(A_6, B_7, C_8)=A_6 | '#skF_2'(A_6, B_7, C_8)!=B_7 | k2_tarski(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.05/2.45  tff(c_310, plain, (![B_7, C_8]: ('#skF_2'(B_7, B_7, C_8)!=B_7 | k2_tarski(B_7, B_7)=C_8 | '#skF_1'(B_7, B_7, C_8)=B_7)), inference(factorization, [status(thm), theory('equality')], [c_16])).
% 7.05/2.45  tff(c_692, plain, (![B_2098, C_2099]: ('#skF_2'(B_2098, B_2098, C_2099)!=B_2098 | k1_tarski(B_2098)=C_2099 | '#skF_1'(B_2098, B_2098, C_2099)=B_2098)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_310])).
% 7.05/2.45  tff(c_118, plain, (![D_63, B_64, A_65]: (D_63=B_64 | D_63=A_65 | ~r2_hidden(D_63, k2_tarski(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.05/2.45  tff(c_121, plain, (![D_63, A_12]: (D_63=A_12 | D_63=A_12 | ~r2_hidden(D_63, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_118])).
% 7.05/2.45  tff(c_1639, plain, (![D_6558, B_6559, C_6560]: (D_6558=B_6559 | D_6558=B_6559 | ~r2_hidden(D_6558, C_6560) | '#skF_2'(B_6559, B_6559, C_6560)!=B_6559 | '#skF_1'(B_6559, B_6559, C_6560)=B_6559)), inference(superposition, [status(thm), theory('equality')], [c_692, c_121])).
% 7.05/2.45  tff(c_4538, plain, (![B_14467, A_14468, B_14469]: (B_14467='#skF_4'(A_14468, B_14469) | '#skF_2'(B_14467, B_14467, B_14469)!=B_14467 | '#skF_1'(B_14467, B_14467, B_14469)=B_14467 | r1_tarski('#skF_3'(A_14468, B_14469), A_14468) | k1_zfmisc_1(A_14468)=B_14469)), inference(resolution, [status(thm)], [c_50, c_1639])).
% 7.05/2.45  tff(c_5616, plain, (![B_18286, B_18287]: ('#skF_3'(k1_xboole_0, B_18286)=k1_xboole_0 | B_18287='#skF_4'(k1_xboole_0, B_18286) | '#skF_2'(B_18287, B_18287, B_18286)!=B_18287 | '#skF_1'(B_18287, B_18287, B_18286)=B_18287 | k1_zfmisc_1(k1_xboole_0)=B_18286)), inference(resolution, [status(thm)], [c_4538, c_6])).
% 7.05/2.45  tff(c_6248, plain, (![B_18286, B_18287]: (k1_tarski(k1_xboole_0)!=B_18286 | '#skF_3'(k1_xboole_0, B_18286)=k1_xboole_0 | B_18287='#skF_4'(k1_xboole_0, B_18286) | '#skF_2'(B_18287, B_18287, B_18286)!=B_18287 | '#skF_1'(B_18287, B_18287, B_18286)=B_18287)), inference(superposition, [status(thm), theory('equality')], [c_5616, c_52])).
% 7.05/2.45  tff(c_6377, plain, (![B_18287]: ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | B_18287='#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)) | '#skF_2'(B_18287, B_18287, k1_tarski(k1_xboole_0))!=B_18287 | '#skF_1'(B_18287, B_18287, k1_tarski(k1_xboole_0))=B_18287)), inference(reflexivity, [status(thm), theory('equality')], [c_6248])).
% 7.05/2.45  tff(c_7614, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6377])).
% 7.05/2.45  tff(c_48, plain, (![A_40, B_41]: (~r2_hidden('#skF_3'(A_40, B_41), B_41) | r2_hidden('#skF_4'(A_40, B_41), B_41) | k1_zfmisc_1(A_40)=B_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.05/2.45  tff(c_7633, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7614, c_48])).
% 7.05/2.45  tff(c_7687, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_7633])).
% 7.05/2.45  tff(c_7688, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_7687])).
% 7.05/2.45  tff(c_7823, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_7688, c_121])).
% 7.05/2.45  tff(c_44, plain, (![A_40, B_41]: (~r2_hidden('#skF_3'(A_40, B_41), B_41) | ~r1_tarski('#skF_4'(A_40, B_41), A_40) | k1_zfmisc_1(A_40)=B_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.05/2.45  tff(c_7630, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | ~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7614, c_44])).
% 7.05/2.45  tff(c_7684, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_7630])).
% 7.05/2.45  tff(c_7685, plain, (~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_7684])).
% 7.05/2.45  tff(c_7825, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7823, c_7685])).
% 7.05/2.45  tff(c_7829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_7825])).
% 7.05/2.45  tff(c_7831, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_6377])).
% 7.05/2.45  tff(c_183, plain, (![A_87, B_88]: (r1_tarski('#skF_3'(A_87, B_88), A_87) | r2_hidden('#skF_4'(A_87, B_88), B_88) | k1_zfmisc_1(A_87)=B_88)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.05/2.45  tff(c_222, plain, (![A_101, A_102]: ('#skF_4'(A_101, k1_tarski(A_102))=A_102 | r1_tarski('#skF_3'(A_101, k1_tarski(A_102)), A_101) | k1_zfmisc_1(A_101)=k1_tarski(A_102))), inference(resolution, [status(thm)], [c_183, c_121])).
% 7.05/2.45  tff(c_227, plain, (![A_102]: ('#skF_3'(k1_xboole_0, k1_tarski(A_102))=k1_xboole_0 | '#skF_4'(k1_xboole_0, k1_tarski(A_102))=A_102 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_102))), inference(resolution, [status(thm)], [c_222, c_6])).
% 7.05/2.45  tff(c_7847, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_7831])).
% 7.05/2.45  tff(c_7850, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_7847])).
% 7.05/2.45  tff(c_176, plain, (![A_84, B_85]: (r1_tarski('#skF_3'(A_84, B_85), A_84) | ~r1_tarski('#skF_4'(A_84, B_85), A_84) | k1_zfmisc_1(A_84)=B_85)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.05/2.45  tff(c_181, plain, (![B_85]: ('#skF_3'(k1_xboole_0, B_85)=k1_xboole_0 | ~r1_tarski('#skF_4'(k1_xboole_0, B_85), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=B_85)), inference(resolution, [status(thm)], [c_176, c_6])).
% 7.05/2.45  tff(c_7959, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7850, c_181])).
% 7.05/2.45  tff(c_8035, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7959])).
% 7.05/2.45  tff(c_8037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7831, c_8035])).
% 7.05/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.45  
% 7.05/2.45  Inference rules
% 7.05/2.45  ----------------------
% 7.05/2.45  #Ref     : 1
% 7.05/2.45  #Sup     : 1122
% 7.05/2.45  #Fact    : 18
% 7.05/2.45  #Define  : 0
% 7.05/2.45  #Split   : 1
% 7.05/2.45  #Chain   : 0
% 7.05/2.45  #Close   : 0
% 7.05/2.45  
% 7.05/2.45  Ordering : KBO
% 7.05/2.45  
% 7.05/2.45  Simplification rules
% 7.05/2.45  ----------------------
% 7.05/2.45  #Subsume      : 263
% 7.05/2.45  #Demod        : 243
% 7.05/2.45  #Tautology    : 253
% 7.05/2.45  #SimpNegUnit  : 10
% 7.05/2.45  #BackRed      : 2
% 7.05/2.45  
% 7.05/2.45  #Partial instantiations: 7360
% 7.05/2.45  #Strategies tried      : 1
% 7.05/2.45  
% 7.05/2.45  Timing (in seconds)
% 7.05/2.45  ----------------------
% 7.26/2.45  Preprocessing        : 0.31
% 7.26/2.45  Parsing              : 0.16
% 7.26/2.45  CNF conversion       : 0.02
% 7.26/2.45  Main loop            : 1.36
% 7.26/2.45  Inferencing          : 0.66
% 7.26/2.45  Reduction            : 0.26
% 7.26/2.45  Demodulation         : 0.18
% 7.26/2.45  BG Simplification    : 0.06
% 7.26/2.45  Subsumption          : 0.31
% 7.26/2.45  Abstraction          : 0.08
% 7.26/2.45  MUC search           : 0.00
% 7.26/2.45  Cooper               : 0.00
% 7.26/2.45  Total                : 1.70
% 7.26/2.45  Index Insertion      : 0.00
% 7.26/2.45  Index Deletion       : 0.00
% 7.26/2.45  Index Matching       : 0.00
% 7.26/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
