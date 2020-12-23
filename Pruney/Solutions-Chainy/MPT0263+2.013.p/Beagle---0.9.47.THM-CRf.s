%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:15 EST 2020

% Result     : Theorem 24.44s
% Output     : CNFRefutation 24.51s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 209 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  110 ( 458 expanded)
%              Number of equality atoms :   46 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_30,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_319,plain,(
    ! [A_82,B_83] :
      ( '#skF_4'(A_82,B_83) = A_82
      | r2_hidden('#skF_5'(A_82,B_83),B_83)
      | k1_tarski(A_82) = B_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5600,plain,(
    ! [A_289,A_290,B_291] :
      ( r2_hidden('#skF_5'(A_289,k3_xboole_0(A_290,B_291)),B_291)
      | '#skF_4'(A_289,k3_xboole_0(A_290,B_291)) = A_289
      | k3_xboole_0(A_290,B_291) = k1_tarski(A_289) ) ),
    inference(resolution,[status(thm)],[c_319,c_6])).

tff(c_28,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55826,plain,(
    ! [A_1116,A_1117,A_1118] :
      ( '#skF_5'(A_1116,k3_xboole_0(A_1117,k1_tarski(A_1118))) = A_1118
      | '#skF_4'(A_1116,k3_xboole_0(A_1117,k1_tarski(A_1118))) = A_1116
      | k3_xboole_0(A_1117,k1_tarski(A_1118)) = k1_tarski(A_1116) ) ),
    inference(resolution,[status(thm)],[c_5600,c_28])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( '#skF_4'(A_16,B_17) = A_16
      | '#skF_5'(A_16,B_17) != A_16
      | k1_tarski(A_16) = B_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67191,plain,(
    ! [A_1243,A_1244] :
      ( '#skF_4'(A_1243,k3_xboole_0(A_1244,k1_tarski(A_1243))) = A_1243
      | k3_xboole_0(A_1244,k1_tarski(A_1243)) = k1_tarski(A_1243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55826,c_34])).

tff(c_48,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_3'(A_52,B_53),k3_xboole_0(A_52,B_53))
      | r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_211,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_3'(A_60,B_61),A_60)
      | r1_xboole_0(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_345,plain,(
    ! [A_84,B_85] :
      ( '#skF_3'(k1_tarski(A_84),B_85) = A_84
      | r1_xboole_0(k1_tarski(A_84),B_85) ) ),
    inference(resolution,[status(thm)],[c_211,c_28])).

tff(c_355,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_345,c_48])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),k3_xboole_0(A_9,B_10))
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_365,plain,
    ( r2_hidden('#skF_6',k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_22])).

tff(c_371,plain,
    ( r2_hidden('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_365])).

tff(c_372,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_371])).

tff(c_277,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,k3_xboole_0(A_75,B_76))
      | ~ r2_hidden(D_74,B_76)
      | ~ r2_hidden(D_74,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_299,plain,(
    ! [A_75,B_76,D_74] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(D_74,B_76)
      | ~ r2_hidden(D_74,A_75) ) ),
    inference(resolution,[status(thm)],[c_277,c_24])).

tff(c_11316,plain,(
    ! [D_432,B_433,A_434] :
      ( ~ r2_hidden(D_432,B_433)
      | ~ r2_hidden(D_432,k1_tarski(A_434))
      | '#skF_3'(k1_tarski(A_434),B_433) = A_434 ) ),
    inference(resolution,[status(thm)],[c_345,c_299])).

tff(c_11767,plain,(
    ! [A_442] :
      ( ~ r2_hidden('#skF_6',k1_tarski(A_442))
      | '#skF_3'(k1_tarski(A_442),k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) = A_442 ) ),
    inference(resolution,[status(thm)],[c_372,c_11316])).

tff(c_181,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_3'(A_52,B_53),B_53)
      | r1_xboole_0(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_160,c_6])).

tff(c_12935,plain,(
    ! [A_462] :
      ( r2_hidden(A_462,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | r1_xboole_0(k1_tarski(A_462),k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden('#skF_6',k1_tarski(A_462)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11767,c_181])).

tff(c_28966,plain,(
    ! [D_718,A_719] :
      ( ~ r2_hidden(D_718,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden(D_718,k1_tarski(A_719))
      | r2_hidden(A_719,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden('#skF_6',k1_tarski(A_719)) ) ),
    inference(resolution,[status(thm)],[c_12935,c_299])).

tff(c_29190,plain,(
    ! [A_720] :
      ( r2_hidden(A_720,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden('#skF_6',k1_tarski(A_720)) ) ),
    inference(resolution,[status(thm)],[c_372,c_28966])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden('#skF_4'(A_16,B_17),B_17)
      | '#skF_5'(A_16,B_17) != A_16
      | k1_tarski(A_16) = B_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29256,plain,(
    ! [A_16] :
      ( '#skF_5'(A_16,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) != A_16
      | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski(A_16)
      | ~ r2_hidden('#skF_6',k1_tarski('#skF_4'(A_16,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))))) ) ),
    inference(resolution,[status(thm)],[c_29190,c_32])).

tff(c_67223,plain,
    ( '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) != '#skF_6'
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6')
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_67191,c_29256])).

tff(c_67315,plain,
    ( '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) != '#skF_6'
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_67223])).

tff(c_67316,plain,(
    '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_67315])).

tff(c_446,plain,(
    ! [A_92,B_93] :
      ( ~ r2_hidden('#skF_4'(A_92,B_93),B_93)
      | r2_hidden('#skF_5'(A_92,B_93),B_93)
      | k1_tarski(A_92) = B_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_469,plain,(
    ! [A_92,A_3,B_4] :
      ( r2_hidden('#skF_5'(A_92,k3_xboole_0(A_3,B_4)),B_4)
      | ~ r2_hidden('#skF_4'(A_92,k3_xboole_0(A_3,B_4)),k3_xboole_0(A_3,B_4))
      | k3_xboole_0(A_3,B_4) = k1_tarski(A_92) ) ),
    inference(resolution,[status(thm)],[c_446,c_6])).

tff(c_31244,plain,(
    ! [A_760] :
      ( r2_hidden('#skF_5'(A_760,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))),k1_tarski('#skF_6'))
      | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski(A_760)
      | ~ r2_hidden('#skF_6',k1_tarski('#skF_4'(A_760,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))))) ) ),
    inference(resolution,[status(thm)],[c_29190,c_469])).

tff(c_31254,plain,(
    ! [A_760] :
      ( '#skF_5'(A_760,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) = '#skF_6'
      | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski(A_760)
      | ~ r2_hidden('#skF_6',k1_tarski('#skF_4'(A_760,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))))) ) ),
    inference(resolution,[status(thm)],[c_31244,c_28])).

tff(c_67215,plain,
    ( '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) = '#skF_6'
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6')
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_67191,c_31254])).

tff(c_67309,plain,
    ( '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) = '#skF_6'
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_67215])).

tff(c_67310,plain,(
    '#skF_5'('#skF_6',k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_67309])).

tff(c_67335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67316,c_67310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.44/14.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.46/14.82  
% 24.46/14.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.46/14.82  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 24.46/14.82  
% 24.46/14.82  %Foreground sorts:
% 24.46/14.82  
% 24.46/14.82  
% 24.46/14.82  %Background operators:
% 24.46/14.82  
% 24.46/14.82  
% 24.46/14.82  %Foreground operators:
% 24.46/14.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 24.46/14.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.46/14.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.46/14.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.46/14.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.46/14.82  tff('#skF_7', type, '#skF_7': $i).
% 24.46/14.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 24.46/14.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 24.46/14.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.46/14.82  tff('#skF_6', type, '#skF_6': $i).
% 24.46/14.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.46/14.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.46/14.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.46/14.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.46/14.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.46/14.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.46/14.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 24.46/14.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 24.46/14.82  
% 24.51/14.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.51/14.83  tff(f_70, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 24.51/14.83  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 24.51/14.83  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 24.51/14.83  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 24.51/14.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.51/14.83  tff(c_46, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.51/14.83  tff(c_49, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 24.51/14.83  tff(c_30, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_319, plain, (![A_82, B_83]: ('#skF_4'(A_82, B_83)=A_82 | r2_hidden('#skF_5'(A_82, B_83), B_83) | k1_tarski(A_82)=B_83)), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 24.51/14.83  tff(c_5600, plain, (![A_289, A_290, B_291]: (r2_hidden('#skF_5'(A_289, k3_xboole_0(A_290, B_291)), B_291) | '#skF_4'(A_289, k3_xboole_0(A_290, B_291))=A_289 | k3_xboole_0(A_290, B_291)=k1_tarski(A_289))), inference(resolution, [status(thm)], [c_319, c_6])).
% 24.51/14.83  tff(c_28, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_55826, plain, (![A_1116, A_1117, A_1118]: ('#skF_5'(A_1116, k3_xboole_0(A_1117, k1_tarski(A_1118)))=A_1118 | '#skF_4'(A_1116, k3_xboole_0(A_1117, k1_tarski(A_1118)))=A_1116 | k3_xboole_0(A_1117, k1_tarski(A_1118))=k1_tarski(A_1116))), inference(resolution, [status(thm)], [c_5600, c_28])).
% 24.51/14.83  tff(c_34, plain, (![A_16, B_17]: ('#skF_4'(A_16, B_17)=A_16 | '#skF_5'(A_16, B_17)!=A_16 | k1_tarski(A_16)=B_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_67191, plain, (![A_1243, A_1244]: ('#skF_4'(A_1243, k3_xboole_0(A_1244, k1_tarski(A_1243)))=A_1243 | k3_xboole_0(A_1244, k1_tarski(A_1243))=k1_tarski(A_1243))), inference(superposition, [status(thm), theory('equality')], [c_55826, c_34])).
% 24.51/14.83  tff(c_48, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.51/14.83  tff(c_160, plain, (![A_52, B_53]: (r2_hidden('#skF_3'(A_52, B_53), k3_xboole_0(A_52, B_53)) | r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.51/14.83  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 24.51/14.83  tff(c_211, plain, (![A_60, B_61]: (r2_hidden('#skF_3'(A_60, B_61), A_60) | r1_xboole_0(A_60, B_61))), inference(resolution, [status(thm)], [c_160, c_8])).
% 24.51/14.83  tff(c_345, plain, (![A_84, B_85]: ('#skF_3'(k1_tarski(A_84), B_85)=A_84 | r1_xboole_0(k1_tarski(A_84), B_85))), inference(resolution, [status(thm)], [c_211, c_28])).
% 24.51/14.83  tff(c_355, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_345, c_48])).
% 24.51/14.83  tff(c_22, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), k3_xboole_0(A_9, B_10)) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.51/14.83  tff(c_365, plain, (r2_hidden('#skF_6', k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_355, c_22])).
% 24.51/14.83  tff(c_371, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_365])).
% 24.51/14.83  tff(c_372, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_48, c_371])).
% 24.51/14.83  tff(c_277, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, k3_xboole_0(A_75, B_76)) | ~r2_hidden(D_74, B_76) | ~r2_hidden(D_74, A_75))), inference(cnfTransformation, [status(thm)], [f_36])).
% 24.51/14.83  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.51/14.83  tff(c_299, plain, (![A_75, B_76, D_74]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(D_74, B_76) | ~r2_hidden(D_74, A_75))), inference(resolution, [status(thm)], [c_277, c_24])).
% 24.51/14.83  tff(c_11316, plain, (![D_432, B_433, A_434]: (~r2_hidden(D_432, B_433) | ~r2_hidden(D_432, k1_tarski(A_434)) | '#skF_3'(k1_tarski(A_434), B_433)=A_434)), inference(resolution, [status(thm)], [c_345, c_299])).
% 24.51/14.83  tff(c_11767, plain, (![A_442]: (~r2_hidden('#skF_6', k1_tarski(A_442)) | '#skF_3'(k1_tarski(A_442), k3_xboole_0('#skF_7', k1_tarski('#skF_6')))=A_442)), inference(resolution, [status(thm)], [c_372, c_11316])).
% 24.51/14.83  tff(c_181, plain, (![A_52, B_53]: (r2_hidden('#skF_3'(A_52, B_53), B_53) | r1_xboole_0(A_52, B_53))), inference(resolution, [status(thm)], [c_160, c_6])).
% 24.51/14.83  tff(c_12935, plain, (![A_462]: (r2_hidden(A_462, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | r1_xboole_0(k1_tarski(A_462), k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_6', k1_tarski(A_462)))), inference(superposition, [status(thm), theory('equality')], [c_11767, c_181])).
% 24.51/14.83  tff(c_28966, plain, (![D_718, A_719]: (~r2_hidden(D_718, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden(D_718, k1_tarski(A_719)) | r2_hidden(A_719, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_6', k1_tarski(A_719)))), inference(resolution, [status(thm)], [c_12935, c_299])).
% 24.51/14.83  tff(c_29190, plain, (![A_720]: (r2_hidden(A_720, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_6', k1_tarski(A_720)))), inference(resolution, [status(thm)], [c_372, c_28966])).
% 24.51/14.83  tff(c_32, plain, (![A_16, B_17]: (~r2_hidden('#skF_4'(A_16, B_17), B_17) | '#skF_5'(A_16, B_17)!=A_16 | k1_tarski(A_16)=B_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_29256, plain, (![A_16]: ('#skF_5'(A_16, k3_xboole_0('#skF_7', k1_tarski('#skF_6')))!=A_16 | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski(A_16) | ~r2_hidden('#skF_6', k1_tarski('#skF_4'(A_16, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))))))), inference(resolution, [status(thm)], [c_29190, c_32])).
% 24.51/14.83  tff(c_67223, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))!='#skF_6' | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6') | ~r2_hidden('#skF_6', k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_67191, c_29256])).
% 24.51/14.83  tff(c_67315, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))!='#skF_6' | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_67223])).
% 24.51/14.83  tff(c_67316, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_49, c_67315])).
% 24.51/14.83  tff(c_446, plain, (![A_92, B_93]: (~r2_hidden('#skF_4'(A_92, B_93), B_93) | r2_hidden('#skF_5'(A_92, B_93), B_93) | k1_tarski(A_92)=B_93)), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.51/14.83  tff(c_469, plain, (![A_92, A_3, B_4]: (r2_hidden('#skF_5'(A_92, k3_xboole_0(A_3, B_4)), B_4) | ~r2_hidden('#skF_4'(A_92, k3_xboole_0(A_3, B_4)), k3_xboole_0(A_3, B_4)) | k3_xboole_0(A_3, B_4)=k1_tarski(A_92))), inference(resolution, [status(thm)], [c_446, c_6])).
% 24.51/14.83  tff(c_31244, plain, (![A_760]: (r2_hidden('#skF_5'(A_760, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski(A_760) | ~r2_hidden('#skF_6', k1_tarski('#skF_4'(A_760, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))))))), inference(resolution, [status(thm)], [c_29190, c_469])).
% 24.51/14.83  tff(c_31254, plain, (![A_760]: ('#skF_5'(A_760, k3_xboole_0('#skF_7', k1_tarski('#skF_6')))='#skF_6' | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski(A_760) | ~r2_hidden('#skF_6', k1_tarski('#skF_4'(A_760, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))))))), inference(resolution, [status(thm)], [c_31244, c_28])).
% 24.51/14.83  tff(c_67215, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))='#skF_6' | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6') | ~r2_hidden('#skF_6', k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_67191, c_31254])).
% 24.51/14.83  tff(c_67309, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))='#skF_6' | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_67215])).
% 24.51/14.83  tff(c_67310, plain, ('#skF_5'('#skF_6', k3_xboole_0('#skF_7', k1_tarski('#skF_6')))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_49, c_67309])).
% 24.51/14.83  tff(c_67335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67316, c_67310])).
% 24.51/14.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.51/14.83  
% 24.51/14.83  Inference rules
% 24.51/14.83  ----------------------
% 24.51/14.83  #Ref     : 0
% 24.51/14.83  #Sup     : 17350
% 24.51/14.83  #Fact    : 0
% 24.51/14.83  #Define  : 0
% 24.51/14.83  #Split   : 7
% 24.51/14.83  #Chain   : 0
% 24.51/14.83  #Close   : 0
% 24.51/14.83  
% 24.51/14.83  Ordering : KBO
% 24.51/14.83  
% 24.51/14.83  Simplification rules
% 24.51/14.83  ----------------------
% 24.51/14.83  #Subsume      : 5511
% 24.51/14.83  #Demod        : 2160
% 24.51/14.83  #Tautology    : 728
% 24.51/14.83  #SimpNegUnit  : 28
% 24.51/14.83  #BackRed      : 0
% 24.51/14.83  
% 24.51/14.83  #Partial instantiations: 0
% 24.51/14.83  #Strategies tried      : 1
% 24.51/14.83  
% 24.51/14.83  Timing (in seconds)
% 24.51/14.83  ----------------------
% 24.51/14.84  Preprocessing        : 0.33
% 24.51/14.84  Parsing              : 0.17
% 24.51/14.84  CNF conversion       : 0.02
% 24.51/14.84  Main loop            : 13.67
% 24.51/14.84  Inferencing          : 1.74
% 24.51/14.84  Reduction            : 3.14
% 24.51/14.84  Demodulation         : 2.63
% 24.51/14.84  BG Simplification    : 0.26
% 24.51/14.84  Subsumption          : 7.67
% 24.51/14.84  Abstraction          : 0.40
% 24.51/14.84  MUC search           : 0.00
% 24.51/14.84  Cooper               : 0.00
% 24.51/14.84  Total                : 14.03
% 24.51/14.84  Index Insertion      : 0.00
% 24.51/14.84  Index Deletion       : 0.00
% 24.51/14.84  Index Matching       : 0.00
% 24.51/14.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
