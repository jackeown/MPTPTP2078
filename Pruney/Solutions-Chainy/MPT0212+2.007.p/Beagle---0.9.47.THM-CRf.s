%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 113 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 221 expanded)
%              Number of equality atoms :   52 ( 131 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_57,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_52,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [B_33] : k4_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4])).

tff(c_30,plain,(
    ! [C_25,A_21] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_53,B_54] :
      ( '#skF_1'(A_53,B_54) = A_53
      | r2_hidden('#skF_2'(A_53,B_54),B_54)
      | k1_tarski(A_53) = B_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_235,plain,(
    ! [A_73,A_74] :
      ( r1_tarski('#skF_2'(A_73,k1_zfmisc_1(A_74)),A_74)
      | '#skF_1'(A_73,k1_zfmisc_1(A_74)) = A_73
      | k1_zfmisc_1(A_74) = k1_tarski(A_73) ) ),
    inference(resolution,[status(thm)],[c_128,c_28])).

tff(c_242,plain,(
    ! [A_75] :
      ( '#skF_2'(A_75,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | '#skF_1'(A_75,k1_zfmisc_1(k1_xboole_0)) = A_75
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_75) ) ),
    inference(resolution,[status(thm)],[c_235,c_6])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( '#skF_1'(A_6,B_7) = A_6
      | '#skF_2'(A_6,B_7) != A_6
      | k1_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_256,plain,(
    ! [A_75] :
      ( '#skF_1'(A_75,k1_zfmisc_1(k1_xboole_0)) = A_75
      | k1_xboole_0 != A_75
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_75)
      | '#skF_1'(A_75,k1_zfmisc_1(k1_xboole_0)) = A_75
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_14])).

tff(c_370,plain,(
    ! [A_93] :
      ( k1_xboole_0 != A_93
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_93)
      | '#skF_1'(A_93,k1_zfmisc_1(k1_xboole_0)) = A_93 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_256])).

tff(c_170,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden('#skF_1'(A_64,B_65),B_65)
      | r2_hidden('#skF_2'(A_64,B_65),B_65)
      | k1_tarski(A_64) = B_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_313,plain,(
    ! [A_87,A_88] :
      ( r1_tarski('#skF_2'(A_87,k1_zfmisc_1(A_88)),A_88)
      | ~ r2_hidden('#skF_1'(A_87,k1_zfmisc_1(A_88)),k1_zfmisc_1(A_88))
      | k1_zfmisc_1(A_88) = k1_tarski(A_87) ) ),
    inference(resolution,[status(thm)],[c_170,c_28])).

tff(c_319,plain,(
    ! [A_89,A_90] :
      ( r1_tarski('#skF_2'(A_89,k1_zfmisc_1(A_90)),A_90)
      | k1_zfmisc_1(A_90) = k1_tarski(A_89)
      | ~ r1_tarski('#skF_1'(A_89,k1_zfmisc_1(A_90)),A_90) ) ),
    inference(resolution,[status(thm)],[c_30,c_313])).

tff(c_327,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89)
      | ~ r1_tarski('#skF_1'(A_89,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_319,c_6])).

tff(c_376,plain,(
    ! [A_93] :
      ( '#skF_2'(A_93,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_93)
      | ~ r1_tarski(A_93,k1_xboole_0)
      | k1_xboole_0 != A_93
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_327])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( '#skF_1'(A_6,B_7) = A_6
      | r2_hidden('#skF_2'(A_6,B_7),B_7)
      | k1_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_254,plain,(
    ! [A_75] :
      ( '#skF_1'(A_75,k1_zfmisc_1(k1_xboole_0)) = A_75
      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_75)
      | '#skF_1'(A_75,k1_zfmisc_1(k1_xboole_0)) = A_75
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_18])).

tff(c_362,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_1'(A_6,B_7),B_7)
      | '#skF_2'(A_6,B_7) != A_6
      | k1_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_435,plain,(
    ! [A_97] :
      ( ~ r2_hidden(A_97,k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(A_97,k1_zfmisc_1(k1_xboole_0)) != A_97
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_97)
      | k1_xboole_0 != A_97
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_12])).

tff(c_438,plain,
    ( '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_362,c_435])).

tff(c_461,plain,(
    '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_438])).

tff(c_469,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_461])).

tff(c_475,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_469])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_475])).

tff(c_479,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_482,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_479])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.35  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.42/1.35  
% 2.42/1.35  %Foreground sorts:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Background operators:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Foreground operators:
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.42/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.42/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.42/1.35  
% 2.63/1.36  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.63/1.36  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.63/1.36  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.63/1.36  tff(f_57, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.63/1.36  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.63/1.36  tff(c_52, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.36  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.36  tff(c_64, plain, (![B_33]: (k4_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_6])).
% 2.63/1.36  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.36  tff(c_69, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_4])).
% 2.63/1.36  tff(c_30, plain, (![C_25, A_21]: (r2_hidden(C_25, k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.36  tff(c_40, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.36  tff(c_128, plain, (![A_53, B_54]: ('#skF_1'(A_53, B_54)=A_53 | r2_hidden('#skF_2'(A_53, B_54), B_54) | k1_tarski(A_53)=B_54)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.36  tff(c_28, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.36  tff(c_235, plain, (![A_73, A_74]: (r1_tarski('#skF_2'(A_73, k1_zfmisc_1(A_74)), A_74) | '#skF_1'(A_73, k1_zfmisc_1(A_74))=A_73 | k1_zfmisc_1(A_74)=k1_tarski(A_73))), inference(resolution, [status(thm)], [c_128, c_28])).
% 2.63/1.36  tff(c_242, plain, (![A_75]: ('#skF_2'(A_75, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | '#skF_1'(A_75, k1_zfmisc_1(k1_xboole_0))=A_75 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_75))), inference(resolution, [status(thm)], [c_235, c_6])).
% 2.63/1.36  tff(c_14, plain, (![A_6, B_7]: ('#skF_1'(A_6, B_7)=A_6 | '#skF_2'(A_6, B_7)!=A_6 | k1_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.36  tff(c_256, plain, (![A_75]: ('#skF_1'(A_75, k1_zfmisc_1(k1_xboole_0))=A_75 | k1_xboole_0!=A_75 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_75) | '#skF_1'(A_75, k1_zfmisc_1(k1_xboole_0))=A_75 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_75))), inference(superposition, [status(thm), theory('equality')], [c_242, c_14])).
% 2.63/1.36  tff(c_370, plain, (![A_93]: (k1_xboole_0!=A_93 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_93) | '#skF_1'(A_93, k1_zfmisc_1(k1_xboole_0))=A_93)), inference(factorization, [status(thm), theory('equality')], [c_256])).
% 2.63/1.36  tff(c_170, plain, (![A_64, B_65]: (~r2_hidden('#skF_1'(A_64, B_65), B_65) | r2_hidden('#skF_2'(A_64, B_65), B_65) | k1_tarski(A_64)=B_65)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.36  tff(c_313, plain, (![A_87, A_88]: (r1_tarski('#skF_2'(A_87, k1_zfmisc_1(A_88)), A_88) | ~r2_hidden('#skF_1'(A_87, k1_zfmisc_1(A_88)), k1_zfmisc_1(A_88)) | k1_zfmisc_1(A_88)=k1_tarski(A_87))), inference(resolution, [status(thm)], [c_170, c_28])).
% 2.63/1.36  tff(c_319, plain, (![A_89, A_90]: (r1_tarski('#skF_2'(A_89, k1_zfmisc_1(A_90)), A_90) | k1_zfmisc_1(A_90)=k1_tarski(A_89) | ~r1_tarski('#skF_1'(A_89, k1_zfmisc_1(A_90)), A_90))), inference(resolution, [status(thm)], [c_30, c_313])).
% 2.63/1.36  tff(c_327, plain, (![A_89]: ('#skF_2'(A_89, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89) | ~r1_tarski('#skF_1'(A_89, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0))), inference(resolution, [status(thm)], [c_319, c_6])).
% 2.63/1.36  tff(c_376, plain, (![A_93]: ('#skF_2'(A_93, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_93) | ~r1_tarski(A_93, k1_xboole_0) | k1_xboole_0!=A_93 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_93))), inference(superposition, [status(thm), theory('equality')], [c_370, c_327])).
% 2.63/1.36  tff(c_18, plain, (![A_6, B_7]: ('#skF_1'(A_6, B_7)=A_6 | r2_hidden('#skF_2'(A_6, B_7), B_7) | k1_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.36  tff(c_254, plain, (![A_75]: ('#skF_1'(A_75, k1_zfmisc_1(k1_xboole_0))=A_75 | r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_75) | '#skF_1'(A_75, k1_zfmisc_1(k1_xboole_0))=A_75 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_75))), inference(superposition, [status(thm), theory('equality')], [c_242, c_18])).
% 2.63/1.36  tff(c_362, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_254])).
% 2.63/1.36  tff(c_12, plain, (![A_6, B_7]: (~r2_hidden('#skF_1'(A_6, B_7), B_7) | '#skF_2'(A_6, B_7)!=A_6 | k1_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.36  tff(c_435, plain, (![A_97]: (~r2_hidden(A_97, k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(A_97, k1_zfmisc_1(k1_xboole_0))!=A_97 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_97) | k1_xboole_0!=A_97 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_97))), inference(superposition, [status(thm), theory('equality')], [c_370, c_12])).
% 2.63/1.36  tff(c_438, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_362, c_435])).
% 2.63/1.36  tff(c_461, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_438])).
% 2.63/1.36  tff(c_469, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_376, c_461])).
% 2.63/1.36  tff(c_475, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_469])).
% 2.63/1.36  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_475])).
% 2.63/1.36  tff(c_479, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_254])).
% 2.63/1.36  tff(c_482, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_479])).
% 2.63/1.36  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_482])).
% 2.63/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.36  
% 2.63/1.36  Inference rules
% 2.63/1.36  ----------------------
% 2.63/1.36  #Ref     : 0
% 2.63/1.36  #Sup     : 83
% 2.63/1.36  #Fact    : 2
% 2.63/1.36  #Define  : 0
% 2.63/1.36  #Split   : 1
% 2.63/1.36  #Chain   : 0
% 2.63/1.36  #Close   : 0
% 2.63/1.36  
% 2.63/1.36  Ordering : KBO
% 2.63/1.36  
% 2.63/1.36  Simplification rules
% 2.63/1.36  ----------------------
% 2.63/1.36  #Subsume      : 10
% 2.63/1.36  #Demod        : 13
% 2.63/1.36  #Tautology    : 39
% 2.63/1.36  #SimpNegUnit  : 2
% 2.63/1.36  #BackRed      : 0
% 2.63/1.36  
% 2.63/1.36  #Partial instantiations: 0
% 2.63/1.36  #Strategies tried      : 1
% 2.63/1.36  
% 2.63/1.36  Timing (in seconds)
% 2.63/1.36  ----------------------
% 2.63/1.36  Preprocessing        : 0.30
% 2.63/1.36  Parsing              : 0.15
% 2.63/1.36  CNF conversion       : 0.02
% 2.63/1.36  Main loop            : 0.30
% 2.63/1.36  Inferencing          : 0.13
% 2.63/1.36  Reduction            : 0.07
% 2.63/1.36  Demodulation         : 0.05
% 2.63/1.36  BG Simplification    : 0.02
% 2.63/1.36  Subsumption          : 0.06
% 2.63/1.36  Abstraction          : 0.02
% 2.63/1.37  MUC search           : 0.00
% 2.63/1.37  Cooper               : 0.00
% 2.63/1.37  Total                : 0.63
% 2.63/1.37  Index Insertion      : 0.00
% 2.63/1.37  Index Deletion       : 0.00
% 2.63/1.37  Index Matching       : 0.00
% 2.63/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
