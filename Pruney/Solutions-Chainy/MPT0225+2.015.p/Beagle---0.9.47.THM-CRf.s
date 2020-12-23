%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:32 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 115 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 163 expanded)
%              Number of equality atoms :   41 ( 104 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_54,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(k1_tarski(A_34),B_35)
      | r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_202,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(k1_tarski(A_76),B_77) = k1_tarski(A_76)
      | r2_hidden(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_72,c_148])).

tff(c_74,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_103,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_213,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_103])).

tff(c_52,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_217,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_213,c_52])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_217])).

tff(c_223,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_222,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_283,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_222,c_78])).

tff(c_284,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_284])).

tff(c_291,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_18,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_258,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_262,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(resolution,[status(thm)],[c_18,c_258])).

tff(c_302,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_311,plain,(
    ! [B_5] : k5_xboole_0(B_5,B_5) = k4_xboole_0(B_5,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_302])).

tff(c_339,plain,(
    ! [A_101,C_102,B_103] :
      ( ~ r2_hidden(A_101,C_102)
      | ~ r2_hidden(A_101,B_103)
      | ~ r2_hidden(A_101,k5_xboole_0(B_103,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_910,plain,(
    ! [A_1327,B_1328] :
      ( ~ r2_hidden(A_1327,B_1328)
      | ~ r2_hidden(A_1327,B_1328)
      | ~ r2_hidden(A_1327,k4_xboole_0(B_1328,B_1328)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_339])).

tff(c_1064,plain,(
    ! [A_1540] :
      ( ~ r2_hidden(A_1540,k1_tarski('#skF_8'))
      | ~ r2_hidden(A_1540,k1_tarski('#skF_8'))
      | ~ r2_hidden(A_1540,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_910])).

tff(c_1074,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_54,c_1064])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1074])).

tff(c_1080,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1081,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1082,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1082])).

tff(c_1093,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1161,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1080,c_1093])).

tff(c_1166,plain,(
    ! [A_1597,B_1598] :
      ( k3_xboole_0(A_1597,B_1598) = A_1597
      | ~ r1_tarski(A_1597,B_1598) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1170,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(resolution,[status(thm)],[c_18,c_1166])).

tff(c_1192,plain,(
    ! [A_1604,B_1605] : k5_xboole_0(A_1604,k3_xboole_0(A_1604,B_1605)) = k4_xboole_0(A_1604,B_1605) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1201,plain,(
    ! [B_5] : k5_xboole_0(B_5,B_5) = k4_xboole_0(B_5,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_1192])).

tff(c_1222,plain,(
    ! [A_1610,C_1611,B_1612] :
      ( ~ r2_hidden(A_1610,C_1611)
      | ~ r2_hidden(A_1610,B_1612)
      | ~ r2_hidden(A_1610,k5_xboole_0(B_1612,C_1611)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1720,plain,(
    ! [A_2789,B_2790] :
      ( ~ r2_hidden(A_2789,B_2790)
      | ~ r2_hidden(A_2789,B_2790)
      | ~ r2_hidden(A_2789,k4_xboole_0(B_2790,B_2790)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_1222])).

tff(c_1859,plain,(
    ! [A_2967] :
      ( ~ r2_hidden(A_2967,k1_tarski('#skF_8'))
      | ~ r2_hidden(A_2967,k1_tarski('#skF_8'))
      | ~ r2_hidden(A_2967,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_1720])).

tff(c_1869,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_54,c_1859])).

tff(c_1874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.59  
% 3.29/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.29/1.60  
% 3.29/1.60  %Foreground sorts:
% 3.29/1.60  
% 3.29/1.60  
% 3.29/1.60  %Background operators:
% 3.29/1.60  
% 3.29/1.60  
% 3.29/1.60  %Foreground operators:
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.29/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.29/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.29/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.29/1.60  
% 3.29/1.61  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.29/1.61  tff(f_89, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.29/1.61  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.29/1.61  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.29/1.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.61  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/1.61  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.61  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.29/1.61  tff(c_54, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.61  tff(c_76, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_83, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_76])).
% 3.29/1.61  tff(c_72, plain, (![A_34, B_35]: (r1_xboole_0(k1_tarski(A_34), B_35) | r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.61  tff(c_148, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.61  tff(c_202, plain, (![A_76, B_77]: (k4_xboole_0(k1_tarski(A_76), B_77)=k1_tarski(A_76) | r2_hidden(A_76, B_77))), inference(resolution, [status(thm)], [c_72, c_148])).
% 3.29/1.61  tff(c_74, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_103, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 3.29/1.61  tff(c_213, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_103])).
% 3.29/1.61  tff(c_52, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.61  tff(c_217, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_213, c_52])).
% 3.29/1.61  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_217])).
% 3.29/1.61  tff(c_223, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 3.29/1.61  tff(c_222, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 3.29/1.61  tff(c_78, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_283, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_222, c_78])).
% 3.29/1.61  tff(c_284, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_283])).
% 3.29/1.61  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_284])).
% 3.29/1.61  tff(c_291, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_283])).
% 3.29/1.61  tff(c_18, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.29/1.61  tff(c_258, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.29/1.61  tff(c_262, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(resolution, [status(thm)], [c_18, c_258])).
% 3.29/1.61  tff(c_302, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.61  tff(c_311, plain, (![B_5]: (k5_xboole_0(B_5, B_5)=k4_xboole_0(B_5, B_5))), inference(superposition, [status(thm), theory('equality')], [c_262, c_302])).
% 3.29/1.61  tff(c_339, plain, (![A_101, C_102, B_103]: (~r2_hidden(A_101, C_102) | ~r2_hidden(A_101, B_103) | ~r2_hidden(A_101, k5_xboole_0(B_103, C_102)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.61  tff(c_910, plain, (![A_1327, B_1328]: (~r2_hidden(A_1327, B_1328) | ~r2_hidden(A_1327, B_1328) | ~r2_hidden(A_1327, k4_xboole_0(B_1328, B_1328)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_339])).
% 3.29/1.61  tff(c_1064, plain, (![A_1540]: (~r2_hidden(A_1540, k1_tarski('#skF_8')) | ~r2_hidden(A_1540, k1_tarski('#skF_8')) | ~r2_hidden(A_1540, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_291, c_910])).
% 3.29/1.61  tff(c_1074, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_1064])).
% 3.29/1.61  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1074])).
% 3.29/1.61  tff(c_1080, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_76])).
% 3.29/1.61  tff(c_1081, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 3.29/1.61  tff(c_80, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_1082, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_80])).
% 3.29/1.61  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1082])).
% 3.29/1.61  tff(c_1093, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 3.29/1.61  tff(c_1161, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1080, c_1093])).
% 3.29/1.61  tff(c_1166, plain, (![A_1597, B_1598]: (k3_xboole_0(A_1597, B_1598)=A_1597 | ~r1_tarski(A_1597, B_1598))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.29/1.61  tff(c_1170, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(resolution, [status(thm)], [c_18, c_1166])).
% 3.29/1.61  tff(c_1192, plain, (![A_1604, B_1605]: (k5_xboole_0(A_1604, k3_xboole_0(A_1604, B_1605))=k4_xboole_0(A_1604, B_1605))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.61  tff(c_1201, plain, (![B_5]: (k5_xboole_0(B_5, B_5)=k4_xboole_0(B_5, B_5))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_1192])).
% 3.29/1.61  tff(c_1222, plain, (![A_1610, C_1611, B_1612]: (~r2_hidden(A_1610, C_1611) | ~r2_hidden(A_1610, B_1612) | ~r2_hidden(A_1610, k5_xboole_0(B_1612, C_1611)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.61  tff(c_1720, plain, (![A_2789, B_2790]: (~r2_hidden(A_2789, B_2790) | ~r2_hidden(A_2789, B_2790) | ~r2_hidden(A_2789, k4_xboole_0(B_2790, B_2790)))), inference(superposition, [status(thm), theory('equality')], [c_1201, c_1222])).
% 3.29/1.61  tff(c_1859, plain, (![A_2967]: (~r2_hidden(A_2967, k1_tarski('#skF_8')) | ~r2_hidden(A_2967, k1_tarski('#skF_8')) | ~r2_hidden(A_2967, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1161, c_1720])).
% 3.29/1.61  tff(c_1869, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_1859])).
% 3.29/1.61  tff(c_1874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1869])).
% 3.29/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.61  
% 3.29/1.61  Inference rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Ref     : 0
% 3.29/1.61  #Sup     : 254
% 3.29/1.61  #Fact    : 0
% 3.29/1.61  #Define  : 0
% 3.29/1.61  #Split   : 7
% 3.29/1.61  #Chain   : 0
% 3.29/1.61  #Close   : 0
% 3.29/1.61  
% 3.29/1.61  Ordering : KBO
% 3.29/1.61  
% 3.29/1.61  Simplification rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Subsume      : 7
% 3.29/1.61  #Demod        : 110
% 3.29/1.61  #Tautology    : 124
% 3.29/1.61  #SimpNegUnit  : 1
% 3.29/1.61  #BackRed      : 0
% 3.29/1.61  
% 3.29/1.61  #Partial instantiations: 1328
% 3.29/1.61  #Strategies tried      : 1
% 3.29/1.61  
% 3.29/1.61  Timing (in seconds)
% 3.29/1.61  ----------------------
% 3.29/1.61  Preprocessing        : 0.34
% 3.29/1.61  Parsing              : 0.17
% 3.29/1.61  CNF conversion       : 0.03
% 3.29/1.61  Main loop            : 0.48
% 3.29/1.61  Inferencing          : 0.24
% 3.29/1.61  Reduction            : 0.12
% 3.29/1.61  Demodulation         : 0.08
% 3.29/1.61  BG Simplification    : 0.03
% 3.29/1.61  Subsumption          : 0.07
% 3.29/1.61  Abstraction          : 0.02
% 3.29/1.61  MUC search           : 0.00
% 3.29/1.61  Cooper               : 0.00
% 3.29/1.61  Total                : 0.85
% 3.29/1.61  Index Insertion      : 0.00
% 3.29/1.61  Index Deletion       : 0.00
% 3.29/1.61  Index Matching       : 0.00
% 3.29/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
