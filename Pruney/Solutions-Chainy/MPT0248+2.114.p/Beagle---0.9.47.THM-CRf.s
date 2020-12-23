%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 164 expanded)
%              Number of leaves         :   34 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  131 ( 343 expanded)
%              Number of equality atoms :   59 ( 244 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_66,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_32])).

tff(c_1028,plain,(
    ! [B_115,A_116] :
      ( k1_tarski(B_115) = A_116
      | k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k1_tarski(B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1039,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_85,c_1028])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_73,c_1039])).

tff(c_1057,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1059,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_24])).

tff(c_36,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [C_24] : ~ v1_xboole_0(k1_tarski(C_24)) ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_1081,plain,(
    ! [A_121] :
      ( v1_xboole_0(A_121)
      | r2_hidden('#skF_1'(A_121),A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1085,plain,(
    ! [A_20] :
      ( '#skF_1'(k1_tarski(A_20)) = A_20
      | v1_xboole_0(k1_tarski(A_20)) ) ),
    inference(resolution,[status(thm)],[c_1081,c_34])).

tff(c_1091,plain,(
    ! [A_20] : '#skF_1'(k1_tarski(A_20)) = A_20 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1085])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1056,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1107,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | A_11 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_26])).

tff(c_54,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(k1_tarski(A_35),B_36) = B_36
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    ! [B_38] : r1_tarski(k1_xboole_0,k1_tarski(B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1058,plain,(
    ! [B_38] : r1_tarski('#skF_8',k1_tarski(B_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_60])).

tff(c_1124,plain,(
    ! [A_125,B_126] :
      ( k2_xboole_0(A_125,B_126) = B_126
      | ~ r1_tarski(A_125,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1134,plain,(
    ! [B_38] : k2_xboole_0('#skF_8',k1_tarski(B_38)) = k1_tarski(B_38) ),
    inference(resolution,[status(thm)],[c_1058,c_1124])).

tff(c_1320,plain,(
    ! [A_151,C_152,B_153] :
      ( r1_tarski(A_151,C_152)
      | ~ r1_tarski(k2_xboole_0(A_151,B_153),C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1478,plain,(
    ! [A_160,B_161,B_162] : r1_tarski(A_160,k2_xboole_0(k2_xboole_0(A_160,B_161),B_162)) ),
    inference(resolution,[status(thm)],[c_32,c_1320])).

tff(c_1518,plain,(
    ! [B_163,B_164] : r1_tarski('#skF_8',k2_xboole_0(k1_tarski(B_163),B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_1478])).

tff(c_1533,plain,(
    ! [B_165,A_166] :
      ( r1_tarski('#skF_8',B_165)
      | ~ r2_hidden(A_166,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1518])).

tff(c_1556,plain,(
    ! [A_167] :
      ( r1_tarski('#skF_8',A_167)
      | A_167 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1107,c_1533])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1594,plain,(
    ! [A_172] :
      ( k2_xboole_0('#skF_8',A_172) = A_172
      | A_172 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1556,c_30])).

tff(c_1620,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1594,c_70])).

tff(c_1639,plain,(
    '#skF_9' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1056,c_1620])).

tff(c_1645,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1639,c_70])).

tff(c_2432,plain,(
    ! [D_207,B_208,A_209] :
      ( r2_hidden(D_207,B_208)
      | r2_hidden(D_207,A_209)
      | ~ r2_hidden(D_207,k2_xboole_0(A_209,B_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2575,plain,(
    ! [D_216] :
      ( r2_hidden(D_216,'#skF_8')
      | r2_hidden(D_216,'#skF_8')
      | ~ r2_hidden(D_216,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_2432])).

tff(c_2587,plain,
    ( r2_hidden('#skF_1'(k1_tarski('#skF_7')),'#skF_8')
    | v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_2575])).

tff(c_2597,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1091,c_2587])).

tff(c_2598,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2597])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2607,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2598,c_2])).

tff(c_2613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_2607])).

tff(c_2615,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2678,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2615,c_68])).

tff(c_2638,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_70])).

tff(c_2614,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3257,plain,(
    ! [D_268,B_269,A_270] :
      ( ~ r2_hidden(D_268,B_269)
      | r2_hidden(D_268,k2_xboole_0(A_270,B_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3303,plain,(
    ! [D_271] :
      ( ~ r2_hidden(D_271,'#skF_9')
      | r2_hidden(D_271,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2638,c_3257])).

tff(c_3311,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26,c_3303])).

tff(c_3315,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2614,c_3311])).

tff(c_2684,plain,(
    ! [C_227,A_228] :
      ( C_227 = A_228
      | ~ r2_hidden(C_227,k1_tarski(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2695,plain,(
    ! [C_227] :
      ( C_227 = '#skF_7'
      | ~ r2_hidden(C_227,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2615,c_2684])).

tff(c_3327,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3315,c_2695])).

tff(c_3334,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_3327,c_26])).

tff(c_3337,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2614,c_3334])).

tff(c_2890,plain,(
    ! [A_240,B_241] :
      ( k2_xboole_0(k1_tarski(A_240),B_241) = B_241
      | ~ r2_hidden(A_240,B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2910,plain,(
    ! [B_241] :
      ( k2_xboole_0('#skF_8',B_241) = B_241
      | ~ r2_hidden('#skF_7',B_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2615,c_2890])).

tff(c_3350,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3337,c_2910])).

tff(c_3359,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2638,c_3350])).

tff(c_3361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2678,c_3359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.72  
% 4.27/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.72  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 4.27/1.72  
% 4.27/1.72  %Foreground sorts:
% 4.27/1.72  
% 4.27/1.72  
% 4.27/1.72  %Background operators:
% 4.27/1.72  
% 4.27/1.72  
% 4.27/1.72  %Foreground operators:
% 4.27/1.72  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.27/1.72  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.27/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.27/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.27/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.27/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.27/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.27/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.27/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.27/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.27/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.27/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.27/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.27/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.27/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.27/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.27/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.27/1.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.27/1.72  
% 4.27/1.74  tff(f_105, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.27/1.74  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.27/1.74  tff(f_84, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.27/1.74  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.27/1.74  tff(f_66, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.27/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.27/1.74  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.27/1.74  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 4.27/1.74  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.27/1.74  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.27/1.74  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.27/1.74  tff(c_66, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.27/1.74  tff(c_89, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_66])).
% 4.27/1.74  tff(c_64, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.27/1.74  tff(c_73, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_64])).
% 4.27/1.74  tff(c_70, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.27/1.74  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.27/1.74  tff(c_85, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_32])).
% 4.27/1.74  tff(c_1028, plain, (![B_115, A_116]: (k1_tarski(B_115)=A_116 | k1_xboole_0=A_116 | ~r1_tarski(A_116, k1_tarski(B_115)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.27/1.74  tff(c_1039, plain, (k1_tarski('#skF_7')='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_85, c_1028])).
% 4.27/1.74  tff(c_1055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_73, c_1039])).
% 4.27/1.74  tff(c_1057, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 4.27/1.74  tff(c_24, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.74  tff(c_1059, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_24])).
% 4.27/1.74  tff(c_36, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.74  tff(c_74, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.74  tff(c_78, plain, (![C_24]: (~v1_xboole_0(k1_tarski(C_24)))), inference(resolution, [status(thm)], [c_36, c_74])).
% 4.27/1.74  tff(c_1081, plain, (![A_121]: (v1_xboole_0(A_121) | r2_hidden('#skF_1'(A_121), A_121))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.74  tff(c_34, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.74  tff(c_1085, plain, (![A_20]: ('#skF_1'(k1_tarski(A_20))=A_20 | v1_xboole_0(k1_tarski(A_20)))), inference(resolution, [status(thm)], [c_1081, c_34])).
% 4.27/1.74  tff(c_1091, plain, (![A_20]: ('#skF_1'(k1_tarski(A_20))=A_20)), inference(negUnitSimplification, [status(thm)], [c_78, c_1085])).
% 4.27/1.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.74  tff(c_1056, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_66])).
% 4.27/1.74  tff(c_26, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.27/1.74  tff(c_1107, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | A_11='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_26])).
% 4.27/1.74  tff(c_54, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), B_36)=B_36 | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.74  tff(c_60, plain, (![B_38]: (r1_tarski(k1_xboole_0, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.27/1.74  tff(c_1058, plain, (![B_38]: (r1_tarski('#skF_8', k1_tarski(B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_60])).
% 4.27/1.74  tff(c_1124, plain, (![A_125, B_126]: (k2_xboole_0(A_125, B_126)=B_126 | ~r1_tarski(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.27/1.74  tff(c_1134, plain, (![B_38]: (k2_xboole_0('#skF_8', k1_tarski(B_38))=k1_tarski(B_38))), inference(resolution, [status(thm)], [c_1058, c_1124])).
% 4.27/1.74  tff(c_1320, plain, (![A_151, C_152, B_153]: (r1_tarski(A_151, C_152) | ~r1_tarski(k2_xboole_0(A_151, B_153), C_152))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.27/1.74  tff(c_1478, plain, (![A_160, B_161, B_162]: (r1_tarski(A_160, k2_xboole_0(k2_xboole_0(A_160, B_161), B_162)))), inference(resolution, [status(thm)], [c_32, c_1320])).
% 4.27/1.74  tff(c_1518, plain, (![B_163, B_164]: (r1_tarski('#skF_8', k2_xboole_0(k1_tarski(B_163), B_164)))), inference(superposition, [status(thm), theory('equality')], [c_1134, c_1478])).
% 4.27/1.74  tff(c_1533, plain, (![B_165, A_166]: (r1_tarski('#skF_8', B_165) | ~r2_hidden(A_166, B_165))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1518])).
% 4.27/1.74  tff(c_1556, plain, (![A_167]: (r1_tarski('#skF_8', A_167) | A_167='#skF_8')), inference(resolution, [status(thm)], [c_1107, c_1533])).
% 4.27/1.74  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.27/1.74  tff(c_1594, plain, (![A_172]: (k2_xboole_0('#skF_8', A_172)=A_172 | A_172='#skF_8')), inference(resolution, [status(thm)], [c_1556, c_30])).
% 4.27/1.74  tff(c_1620, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1594, c_70])).
% 4.27/1.74  tff(c_1639, plain, ('#skF_9'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1056, c_1620])).
% 4.27/1.74  tff(c_1645, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1639, c_70])).
% 4.27/1.74  tff(c_2432, plain, (![D_207, B_208, A_209]: (r2_hidden(D_207, B_208) | r2_hidden(D_207, A_209) | ~r2_hidden(D_207, k2_xboole_0(A_209, B_208)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.27/1.74  tff(c_2575, plain, (![D_216]: (r2_hidden(D_216, '#skF_8') | r2_hidden(D_216, '#skF_8') | ~r2_hidden(D_216, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_2432])).
% 4.27/1.74  tff(c_2587, plain, (r2_hidden('#skF_1'(k1_tarski('#skF_7')), '#skF_8') | v1_xboole_0(k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_2575])).
% 4.27/1.74  tff(c_2597, plain, (r2_hidden('#skF_7', '#skF_8') | v1_xboole_0(k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1091, c_2587])).
% 4.27/1.74  tff(c_2598, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_2597])).
% 4.27/1.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.74  tff(c_2607, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2598, c_2])).
% 4.27/1.74  tff(c_2613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1059, c_2607])).
% 4.27/1.74  tff(c_2615, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 4.27/1.74  tff(c_68, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.27/1.74  tff(c_2678, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2615, c_68])).
% 4.27/1.74  tff(c_2638, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_70])).
% 4.27/1.74  tff(c_2614, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 4.27/1.74  tff(c_3257, plain, (![D_268, B_269, A_270]: (~r2_hidden(D_268, B_269) | r2_hidden(D_268, k2_xboole_0(A_270, B_269)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.27/1.74  tff(c_3303, plain, (![D_271]: (~r2_hidden(D_271, '#skF_9') | r2_hidden(D_271, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2638, c_3257])).
% 4.27/1.74  tff(c_3311, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_26, c_3303])).
% 4.27/1.74  tff(c_3315, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2614, c_3311])).
% 4.27/1.74  tff(c_2684, plain, (![C_227, A_228]: (C_227=A_228 | ~r2_hidden(C_227, k1_tarski(A_228)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.74  tff(c_2695, plain, (![C_227]: (C_227='#skF_7' | ~r2_hidden(C_227, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2615, c_2684])).
% 4.27/1.74  tff(c_3327, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_3315, c_2695])).
% 4.27/1.74  tff(c_3334, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_3327, c_26])).
% 4.27/1.74  tff(c_3337, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2614, c_3334])).
% 4.27/1.74  tff(c_2890, plain, (![A_240, B_241]: (k2_xboole_0(k1_tarski(A_240), B_241)=B_241 | ~r2_hidden(A_240, B_241))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.74  tff(c_2910, plain, (![B_241]: (k2_xboole_0('#skF_8', B_241)=B_241 | ~r2_hidden('#skF_7', B_241))), inference(superposition, [status(thm), theory('equality')], [c_2615, c_2890])).
% 4.27/1.74  tff(c_3350, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_3337, c_2910])).
% 4.27/1.74  tff(c_3359, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2638, c_3350])).
% 4.27/1.74  tff(c_3361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2678, c_3359])).
% 4.27/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.74  
% 4.27/1.74  Inference rules
% 4.27/1.74  ----------------------
% 4.27/1.74  #Ref     : 0
% 4.27/1.74  #Sup     : 783
% 4.27/1.74  #Fact    : 0
% 4.27/1.74  #Define  : 0
% 4.27/1.74  #Split   : 5
% 4.27/1.74  #Chain   : 0
% 4.27/1.74  #Close   : 0
% 4.27/1.74  
% 4.27/1.74  Ordering : KBO
% 4.27/1.74  
% 4.27/1.74  Simplification rules
% 4.27/1.74  ----------------------
% 4.27/1.74  #Subsume      : 79
% 4.27/1.74  #Demod        : 386
% 4.27/1.74  #Tautology    : 439
% 4.27/1.74  #SimpNegUnit  : 38
% 4.27/1.74  #BackRed      : 37
% 4.27/1.74  
% 4.27/1.74  #Partial instantiations: 0
% 4.27/1.74  #Strategies tried      : 1
% 4.27/1.74  
% 4.27/1.74  Timing (in seconds)
% 4.27/1.74  ----------------------
% 4.27/1.74  Preprocessing        : 0.33
% 4.27/1.74  Parsing              : 0.17
% 4.27/1.74  CNF conversion       : 0.03
% 4.27/1.74  Main loop            : 0.64
% 4.27/1.74  Inferencing          : 0.23
% 4.27/1.74  Reduction            : 0.22
% 4.27/1.74  Demodulation         : 0.16
% 4.27/1.74  BG Simplification    : 0.03
% 4.27/1.74  Subsumption          : 0.10
% 4.27/1.74  Abstraction          : 0.03
% 4.27/1.74  MUC search           : 0.00
% 4.27/1.74  Cooper               : 0.00
% 4.27/1.74  Total                : 1.01
% 4.27/1.74  Index Insertion      : 0.00
% 4.27/1.74  Index Deletion       : 0.00
% 4.27/1.74  Index Matching       : 0.00
% 4.27/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
