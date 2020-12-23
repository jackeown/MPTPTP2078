%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   67 (  94 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 113 expanded)
%              Number of equality atoms :   35 (  74 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_40,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_193,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k4_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_193])).

tff(c_208,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_205])).

tff(c_58,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_218,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(k1_tarski(A_69),B_70) = k1_xboole_0
      | r2_hidden(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    ! [A_69,B_70] :
      ( k5_xboole_0(k1_tarski(A_69),k1_xboole_0) = k4_xboole_0(k1_tarski(A_69),B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_6])).

tff(c_262,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(k1_tarski(A_76),B_77) = k1_tarski(A_76)
      | r2_hidden(A_76,B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_224])).

tff(c_60,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_100,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_287,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_100])).

tff(c_38,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_287,c_38])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_295])).

tff(c_300,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_301,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_410,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_300,c_301,c_64])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_417,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_12])).

tff(c_56,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | ~ r1_xboole_0(k1_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_434,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_417,c_56])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_434])).

tff(c_440,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_441,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_520,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_440,c_441,c_66])).

tff(c_524,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_12])).

tff(c_531,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_524,c_56])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:27:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 2.44/1.34  
% 2.44/1.34  %Foreground sorts:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Background operators:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Foreground operators:
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.44/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.44/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.44/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.44/1.34  
% 2.44/1.35  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.44/1.35  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.44/1.35  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.44/1.35  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.44/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.44/1.35  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.44/1.35  tff(f_75, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.44/1.35  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.44/1.35  tff(f_70, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.44/1.35  tff(c_40, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.35  tff(c_62, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.35  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_62])).
% 2.44/1.35  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.35  tff(c_10, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.35  tff(c_150, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.35  tff(c_166, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_150])).
% 2.44/1.35  tff(c_193, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.35  tff(c_205, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k4_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_193])).
% 2.44/1.35  tff(c_208, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_205])).
% 2.44/1.35  tff(c_58, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.44/1.35  tff(c_218, plain, (![A_69, B_70]: (k3_xboole_0(k1_tarski(A_69), B_70)=k1_xboole_0 | r2_hidden(A_69, B_70))), inference(resolution, [status(thm)], [c_58, c_150])).
% 2.44/1.35  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.35  tff(c_224, plain, (![A_69, B_70]: (k5_xboole_0(k1_tarski(A_69), k1_xboole_0)=k4_xboole_0(k1_tarski(A_69), B_70) | r2_hidden(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_218, c_6])).
% 2.44/1.35  tff(c_262, plain, (![A_76, B_77]: (k4_xboole_0(k1_tarski(A_76), B_77)=k1_tarski(A_76) | r2_hidden(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_224])).
% 2.44/1.35  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.35  tff(c_100, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 2.44/1.35  tff(c_287, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_262, c_100])).
% 2.44/1.35  tff(c_38, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.35  tff(c_295, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_287, c_38])).
% 2.44/1.35  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_295])).
% 2.44/1.35  tff(c_300, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 2.44/1.35  tff(c_301, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.44/1.35  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.35  tff(c_410, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_300, c_301, c_64])).
% 2.44/1.35  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.35  tff(c_417, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_12])).
% 2.44/1.35  tff(c_56, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | ~r1_xboole_0(k1_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.35  tff(c_434, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_417, c_56])).
% 2.44/1.35  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_434])).
% 2.44/1.35  tff(c_440, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 2.44/1.35  tff(c_441, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_62])).
% 2.44/1.35  tff(c_66, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.35  tff(c_520, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_440, c_441, c_66])).
% 2.44/1.35  tff(c_524, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_12])).
% 2.44/1.35  tff(c_531, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_524, c_56])).
% 2.44/1.35  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_531])).
% 2.44/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  Inference rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Ref     : 0
% 2.44/1.35  #Sup     : 107
% 2.44/1.35  #Fact    : 0
% 2.44/1.35  #Define  : 0
% 2.44/1.35  #Split   : 2
% 2.44/1.35  #Chain   : 0
% 2.44/1.35  #Close   : 0
% 2.44/1.35  
% 2.44/1.35  Ordering : KBO
% 2.44/1.35  
% 2.44/1.35  Simplification rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Subsume      : 6
% 2.44/1.35  #Demod        : 28
% 2.44/1.35  #Tautology    : 73
% 2.44/1.35  #SimpNegUnit  : 5
% 2.44/1.35  #BackRed      : 0
% 2.44/1.35  
% 2.44/1.35  #Partial instantiations: 0
% 2.44/1.35  #Strategies tried      : 1
% 2.44/1.35  
% 2.44/1.35  Timing (in seconds)
% 2.44/1.35  ----------------------
% 2.44/1.35  Preprocessing        : 0.33
% 2.44/1.35  Parsing              : 0.17
% 2.44/1.35  CNF conversion       : 0.03
% 2.44/1.35  Main loop            : 0.25
% 2.44/1.35  Inferencing          : 0.09
% 2.44/1.35  Reduction            : 0.08
% 2.44/1.35  Demodulation         : 0.06
% 2.44/1.35  BG Simplification    : 0.02
% 2.44/1.35  Subsumption          : 0.04
% 2.44/1.35  Abstraction          : 0.01
% 2.44/1.35  MUC search           : 0.00
% 2.44/1.35  Cooper               : 0.00
% 2.44/1.35  Total                : 0.62
% 2.44/1.35  Index Insertion      : 0.00
% 2.44/1.35  Index Deletion       : 0.00
% 2.44/1.35  Index Matching       : 0.00
% 2.44/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
