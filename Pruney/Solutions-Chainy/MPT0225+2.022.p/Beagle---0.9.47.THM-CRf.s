%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 130 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 161 expanded)
%              Number of equality atoms :   50 ( 113 expanded)
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

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_983,plain,(
    ! [A_1073,B_1074] :
      ( ~ r2_hidden(A_1073,B_1074)
      | ~ r1_xboole_0(k1_tarski(A_1073),B_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_988,plain,(
    ! [A_1073] : ~ r2_hidden(A_1073,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_983])).

tff(c_971,plain,(
    ! [A_1070,B_1071] :
      ( k3_xboole_0(A_1070,B_1071) = k1_xboole_0
      | ~ r1_xboole_0(A_1070,B_1071) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_975,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_971])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1039,plain,(
    ! [A_1086,B_1087] : k4_xboole_0(A_1086,k4_xboole_0(A_1086,B_1087)) = k3_xboole_0(A_1086,B_1087) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1057,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1039])).

tff(c_1061,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_1057])).

tff(c_109,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | ~ r1_xboole_0(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,(
    ! [A_49] : ~ r2_hidden(A_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_97,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_857,plain,(
    ! [A_1053,B_1054] : k4_xboole_0(A_1053,k4_xboole_0(A_1053,B_1054)) = k3_xboole_0(A_1053,B_1054) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_878,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_857])).

tff(c_882,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_878])).

tff(c_62,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_205,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_205])).

tff(c_217,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_214])).

tff(c_116,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_280,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(k1_tarski(A_73),B_74) = k1_xboole_0
      | r2_hidden(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_293,plain,(
    ! [A_73,B_74] :
      ( k5_xboole_0(k1_tarski(A_73),k1_xboole_0) = k4_xboole_0(k1_tarski(A_73),B_74)
      | r2_hidden(A_73,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_6])).

tff(c_330,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),B_79) = k1_tarski(A_78)
      | r2_hidden(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_293])).

tff(c_60,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_149,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_371,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_149])).

tff(c_38,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_760,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_371,c_38])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_760])).

tff(c_808,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_807,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_818,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_64])).

tff(c_819,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_818])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_819])).

tff(c_836,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_818])).

tff(c_883,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_836])).

tff(c_40,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_922,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_40])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_922])).

tff(c_927,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_928,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_965,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_927,c_928,c_66])).

tff(c_1062,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_965])).

tff(c_1096,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_40])).

tff(c_1100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_988,c_1096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.28  % Computer   : n006.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 15:21:52 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.19  
% 2.26/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.19  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 2.26/1.19  
% 2.26/1.19  %Foreground sorts:
% 2.26/1.19  
% 2.26/1.19  
% 2.26/1.19  %Background operators:
% 2.26/1.19  
% 2.26/1.19  
% 2.26/1.19  %Foreground operators:
% 2.26/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.19  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.19  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.26/1.19  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.19  tff('#skF_8', type, '#skF_8': $i).
% 2.26/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.26/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.26/1.19  
% 2.26/1.20  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.26/1.20  tff(f_70, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.26/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.26/1.20  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.26/1.20  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.26/1.20  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.26/1.20  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.26/1.20  tff(f_75, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.26/1.20  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.26/1.20  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.20  tff(c_983, plain, (![A_1073, B_1074]: (~r2_hidden(A_1073, B_1074) | ~r1_xboole_0(k1_tarski(A_1073), B_1074))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.20  tff(c_988, plain, (![A_1073]: (~r2_hidden(A_1073, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_983])).
% 2.26/1.20  tff(c_971, plain, (![A_1070, B_1071]: (k3_xboole_0(A_1070, B_1071)=k1_xboole_0 | ~r1_xboole_0(A_1070, B_1071))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.20  tff(c_975, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_971])).
% 2.26/1.20  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.20  tff(c_1039, plain, (![A_1086, B_1087]: (k4_xboole_0(A_1086, k4_xboole_0(A_1086, B_1087))=k3_xboole_0(A_1086, B_1087))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.20  tff(c_1057, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1039])).
% 2.26/1.20  tff(c_1061, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_975, c_1057])).
% 2.26/1.20  tff(c_109, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | ~r1_xboole_0(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.20  tff(c_114, plain, (![A_49]: (~r2_hidden(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_109])).
% 2.26/1.20  tff(c_97, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.20  tff(c_101, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_97])).
% 2.26/1.20  tff(c_857, plain, (![A_1053, B_1054]: (k4_xboole_0(A_1053, k4_xboole_0(A_1053, B_1054))=k3_xboole_0(A_1053, B_1054))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.20  tff(c_878, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_857])).
% 2.26/1.20  tff(c_882, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_878])).
% 2.26/1.20  tff(c_62, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.20  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_62])).
% 2.26/1.20  tff(c_205, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.20  tff(c_214, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_101, c_205])).
% 2.26/1.20  tff(c_217, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_214])).
% 2.26/1.20  tff(c_116, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.20  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.20  tff(c_280, plain, (![A_73, B_74]: (k3_xboole_0(k1_tarski(A_73), B_74)=k1_xboole_0 | r2_hidden(A_73, B_74))), inference(resolution, [status(thm)], [c_116, c_2])).
% 2.26/1.20  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.20  tff(c_293, plain, (![A_73, B_74]: (k5_xboole_0(k1_tarski(A_73), k1_xboole_0)=k4_xboole_0(k1_tarski(A_73), B_74) | r2_hidden(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_280, c_6])).
% 2.26/1.20  tff(c_330, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), B_79)=k1_tarski(A_78) | r2_hidden(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_293])).
% 2.26/1.20  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.20  tff(c_149, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 2.26/1.20  tff(c_371, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_149])).
% 2.26/1.20  tff(c_38, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.20  tff(c_760, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_371, c_38])).
% 2.26/1.20  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_760])).
% 2.26/1.20  tff(c_808, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.26/1.20  tff(c_807, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 2.26/1.20  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.20  tff(c_818, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_64])).
% 2.26/1.20  tff(c_819, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_818])).
% 2.26/1.20  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_808, c_819])).
% 2.26/1.20  tff(c_836, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_818])).
% 2.26/1.20  tff(c_883, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_882, c_836])).
% 2.26/1.20  tff(c_40, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.20  tff(c_922, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_883, c_40])).
% 2.26/1.20  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_922])).
% 2.26/1.20  tff(c_927, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 2.26/1.20  tff(c_928, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_62])).
% 2.26/1.20  tff(c_66, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.20  tff(c_965, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_927, c_927, c_928, c_66])).
% 2.26/1.20  tff(c_1062, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_965])).
% 2.26/1.20  tff(c_1096, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1062, c_40])).
% 2.26/1.20  tff(c_1100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_988, c_1096])).
% 2.26/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.20  
% 2.26/1.20  Inference rules
% 2.26/1.20  ----------------------
% 2.26/1.20  #Ref     : 0
% 2.26/1.20  #Sup     : 186
% 2.26/1.20  #Fact    : 0
% 2.26/1.20  #Define  : 0
% 2.26/1.20  #Split   : 3
% 2.26/1.20  #Chain   : 0
% 2.26/1.20  #Close   : 0
% 2.26/1.20  
% 2.26/1.20  Ordering : KBO
% 2.26/1.20  
% 2.26/1.20  Simplification rules
% 2.26/1.20  ----------------------
% 2.26/1.20  #Subsume      : 6
% 2.26/1.20  #Demod        : 37
% 2.26/1.20  #Tautology    : 98
% 2.26/1.20  #SimpNegUnit  : 12
% 2.26/1.20  #BackRed      : 2
% 2.26/1.20  
% 2.26/1.20  #Partial instantiations: 528
% 2.26/1.20  #Strategies tried      : 1
% 2.26/1.20  
% 2.26/1.20  Timing (in seconds)
% 2.26/1.20  ----------------------
% 2.26/1.21  Preprocessing        : 0.28
% 2.26/1.21  Parsing              : 0.14
% 2.26/1.21  CNF conversion       : 0.02
% 2.26/1.21  Main loop            : 0.32
% 2.26/1.21  Inferencing          : 0.15
% 2.26/1.21  Reduction            : 0.09
% 2.26/1.21  Demodulation         : 0.06
% 2.26/1.21  BG Simplification    : 0.02
% 2.26/1.21  Subsumption          : 0.04
% 2.26/1.21  Abstraction          : 0.01
% 2.26/1.21  MUC search           : 0.00
% 2.26/1.21  Cooper               : 0.00
% 2.26/1.21  Total                : 0.63
% 2.26/1.21  Index Insertion      : 0.00
% 2.26/1.21  Index Deletion       : 0.00
% 2.26/1.21  Index Matching       : 0.00
% 2.26/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
