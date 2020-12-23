%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 184 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_51,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_58,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_96,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_36,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_313,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,k4_xboole_0(A_79,B_80))
      | r2_hidden(D_78,B_80)
      | ~ r2_hidden(D_78,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_342,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k1_xboole_0)
      | r2_hidden(D_85,'#skF_8')
      | ~ r2_hidden(D_85,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_313])).

tff(c_346,plain,
    ( r2_hidden('#skF_7',k1_xboole_0)
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_342])).

tff(c_349,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_346])).

tff(c_26,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_188,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k4_xboole_0(A_67,B_68),C_69)
      | ~ r1_tarski(A_67,k2_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( r2_xboole_0(A_47,B_48)
      | B_48 = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_13] : ~ r2_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ r1_tarski(A_47,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_106,c_30])).

tff(c_192,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_tarski(A_67,k2_xboole_0(B_68,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_188,c_123])).

tff(c_208,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_192])).

tff(c_225,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_208])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [D_6,A_73] :
      ( ~ r2_hidden(D_6,A_73)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_4])).

tff(c_351,plain,(
    ~ r2_hidden('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_349,c_236])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_351])).

tff(c_364,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_367,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(k1_tarski(A_89),B_90) = B_90
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_373,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k1_tarski(A_89),B_90)
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_32])).

tff(c_404,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k4_xboole_0(A_97,B_98),C_99)
      | ~ r1_tarski(A_97,k2_xboole_0(B_98,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_408,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_tarski(A_97,k2_xboole_0(B_98,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_404,c_123])).

tff(c_411,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = k1_xboole_0
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_408])).

tff(c_867,plain,(
    ! [A_1123,B_1124] :
      ( k4_xboole_0(k1_tarski(A_1123),B_1124) = k1_xboole_0
      | ~ r2_hidden(A_1123,B_1124) ) ),
    inference(resolution,[status(thm)],[c_373,c_411])).

tff(c_365,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_394,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_60])).

tff(c_887,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_394])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_887])).

tff(c_968,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_981,plain,(
    ! [A_1159,B_1160] :
      ( k2_xboole_0(k1_tarski(A_1159),B_1160) = B_1160
      | ~ r2_hidden(A_1159,B_1160) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_987,plain,(
    ! [A_1159,B_1160] :
      ( r1_tarski(k1_tarski(A_1159),B_1160)
      | ~ r2_hidden(A_1159,B_1160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_32])).

tff(c_1045,plain,(
    ! [A_1173,B_1174,C_1175] :
      ( r1_tarski(k4_xboole_0(A_1173,B_1174),C_1175)
      | ~ r1_tarski(A_1173,k2_xboole_0(B_1174,C_1175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1002,plain,(
    ! [A_1162,B_1163] :
      ( r2_xboole_0(A_1162,B_1163)
      | B_1163 = A_1162
      | ~ r1_tarski(A_1162,B_1163) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1019,plain,(
    ! [A_1162] :
      ( k1_xboole_0 = A_1162
      | ~ r1_tarski(A_1162,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1002,c_30])).

tff(c_1049,plain,(
    ! [A_1173,B_1174] :
      ( k4_xboole_0(A_1173,B_1174) = k1_xboole_0
      | ~ r1_tarski(A_1173,k2_xboole_0(B_1174,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1045,c_1019])).

tff(c_1052,plain,(
    ! [A_1176,B_1177] :
      ( k4_xboole_0(A_1176,B_1177) = k1_xboole_0
      | ~ r1_tarski(A_1176,B_1177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1049])).

tff(c_1498,plain,(
    ! [A_2208,B_2209] :
      ( k4_xboole_0(k1_tarski(A_2208),B_2209) = k1_xboole_0
      | ~ r2_hidden(A_2208,B_2209) ) ),
    inference(resolution,[status(thm)],[c_987,c_1052])).

tff(c_969,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1034,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_56])).

tff(c_1521,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_1034])).

tff(c_1595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.55  
% 3.16/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  %$ r2_xboole_0 > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 3.16/1.56  
% 3.16/1.56  %Foreground sorts:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Background operators:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Foreground operators:
% 3.16/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.56  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.16/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.16/1.56  
% 3.16/1.57  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.16/1.57  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.16/1.57  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.16/1.57  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.16/1.57  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.16/1.57  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.16/1.57  tff(f_42, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.16/1.57  tff(f_51, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 3.16/1.57  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.16/1.57  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.57  tff(c_96, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_58])).
% 3.16/1.57  tff(c_36, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.57  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.57  tff(c_132, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 3.16/1.57  tff(c_313, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, k4_xboole_0(A_79, B_80)) | r2_hidden(D_78, B_80) | ~r2_hidden(D_78, A_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.57  tff(c_342, plain, (![D_85]: (r2_hidden(D_85, k1_xboole_0) | r2_hidden(D_85, '#skF_8') | ~r2_hidden(D_85, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_313])).
% 3.16/1.57  tff(c_346, plain, (r2_hidden('#skF_7', k1_xboole_0) | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_342])).
% 3.16/1.57  tff(c_349, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_96, c_346])).
% 3.16/1.57  tff(c_26, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.57  tff(c_75, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.57  tff(c_78, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_26, c_75])).
% 3.16/1.57  tff(c_188, plain, (![A_67, B_68, C_69]: (r1_tarski(k4_xboole_0(A_67, B_68), C_69) | ~r1_tarski(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.57  tff(c_106, plain, (![A_47, B_48]: (r2_xboole_0(A_47, B_48) | B_48=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.57  tff(c_30, plain, (![A_13]: (~r2_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.57  tff(c_123, plain, (![A_47]: (k1_xboole_0=A_47 | ~r1_tarski(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_106, c_30])).
% 3.16/1.57  tff(c_192, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_tarski(A_67, k2_xboole_0(B_68, k1_xboole_0)))), inference(resolution, [status(thm)], [c_188, c_123])).
% 3.16/1.57  tff(c_208, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_tarski(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_192])).
% 3.16/1.57  tff(c_225, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_208])).
% 3.16/1.57  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.57  tff(c_236, plain, (![D_6, A_73]: (~r2_hidden(D_6, A_73) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_225, c_4])).
% 3.16/1.57  tff(c_351, plain, (~r2_hidden('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_349, c_236])).
% 3.16/1.57  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_351])).
% 3.16/1.57  tff(c_364, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 3.16/1.57  tff(c_367, plain, (![A_89, B_90]: (k2_xboole_0(k1_tarski(A_89), B_90)=B_90 | ~r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.57  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.57  tff(c_373, plain, (![A_89, B_90]: (r1_tarski(k1_tarski(A_89), B_90) | ~r2_hidden(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_367, c_32])).
% 3.16/1.57  tff(c_404, plain, (![A_97, B_98, C_99]: (r1_tarski(k4_xboole_0(A_97, B_98), C_99) | ~r1_tarski(A_97, k2_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.57  tff(c_408, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_tarski(A_97, k2_xboole_0(B_98, k1_xboole_0)))), inference(resolution, [status(thm)], [c_404, c_123])).
% 3.16/1.57  tff(c_411, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=k1_xboole_0 | ~r1_tarski(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_408])).
% 3.16/1.57  tff(c_867, plain, (![A_1123, B_1124]: (k4_xboole_0(k1_tarski(A_1123), B_1124)=k1_xboole_0 | ~r2_hidden(A_1123, B_1124))), inference(resolution, [status(thm)], [c_373, c_411])).
% 3.16/1.57  tff(c_365, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 3.16/1.57  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.57  tff(c_394, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_365, c_60])).
% 3.16/1.57  tff(c_887, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_867, c_394])).
% 3.16/1.57  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_364, c_887])).
% 3.16/1.57  tff(c_968, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.57  tff(c_981, plain, (![A_1159, B_1160]: (k2_xboole_0(k1_tarski(A_1159), B_1160)=B_1160 | ~r2_hidden(A_1159, B_1160))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.57  tff(c_987, plain, (![A_1159, B_1160]: (r1_tarski(k1_tarski(A_1159), B_1160) | ~r2_hidden(A_1159, B_1160))), inference(superposition, [status(thm), theory('equality')], [c_981, c_32])).
% 3.16/1.57  tff(c_1045, plain, (![A_1173, B_1174, C_1175]: (r1_tarski(k4_xboole_0(A_1173, B_1174), C_1175) | ~r1_tarski(A_1173, k2_xboole_0(B_1174, C_1175)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.57  tff(c_1002, plain, (![A_1162, B_1163]: (r2_xboole_0(A_1162, B_1163) | B_1163=A_1162 | ~r1_tarski(A_1162, B_1163))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.57  tff(c_1019, plain, (![A_1162]: (k1_xboole_0=A_1162 | ~r1_tarski(A_1162, k1_xboole_0))), inference(resolution, [status(thm)], [c_1002, c_30])).
% 3.16/1.57  tff(c_1049, plain, (![A_1173, B_1174]: (k4_xboole_0(A_1173, B_1174)=k1_xboole_0 | ~r1_tarski(A_1173, k2_xboole_0(B_1174, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1045, c_1019])).
% 3.16/1.57  tff(c_1052, plain, (![A_1176, B_1177]: (k4_xboole_0(A_1176, B_1177)=k1_xboole_0 | ~r1_tarski(A_1176, B_1177))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1049])).
% 3.16/1.57  tff(c_1498, plain, (![A_2208, B_2209]: (k4_xboole_0(k1_tarski(A_2208), B_2209)=k1_xboole_0 | ~r2_hidden(A_2208, B_2209))), inference(resolution, [status(thm)], [c_987, c_1052])).
% 3.16/1.57  tff(c_969, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.57  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.57  tff(c_1034, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_969, c_56])).
% 3.16/1.57  tff(c_1521, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1498, c_1034])).
% 3.16/1.57  tff(c_1595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_968, c_1521])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 260
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 2
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 30
% 3.16/1.57  #Demod        : 34
% 3.16/1.57  #Tautology    : 107
% 3.16/1.57  #SimpNegUnit  : 5
% 3.16/1.57  #BackRed      : 0
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 1120
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.33
% 3.16/1.57  Parsing              : 0.17
% 3.16/1.57  CNF conversion       : 0.02
% 3.16/1.57  Main loop            : 0.40
% 3.16/1.57  Inferencing          : 0.20
% 3.16/1.57  Reduction            : 0.10
% 3.16/1.57  Demodulation         : 0.07
% 3.16/1.57  BG Simplification    : 0.02
% 3.16/1.57  Subsumption          : 0.06
% 3.16/1.57  Abstraction          : 0.02
% 3.16/1.57  MUC search           : 0.00
% 3.16/1.57  Cooper               : 0.00
% 3.16/1.57  Total                : 0.76
% 3.16/1.57  Index Insertion      : 0.00
% 3.16/1.57  Index Deletion       : 0.00
% 3.16/1.57  Index Matching       : 0.00
% 3.16/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
