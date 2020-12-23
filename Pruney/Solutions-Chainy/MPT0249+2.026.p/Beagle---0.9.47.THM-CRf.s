%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:27 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 184 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 337 expanded)
%              Number of equality atoms :   35 ( 156 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_62,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    ! [A_38,B_39] : r1_tarski(A_38,k2_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_81])).

tff(c_201,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_211,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_201])).

tff(c_217,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    ! [D_59,A_60,B_61] :
      ( ~ r2_hidden(D_59,A_60)
      | r2_hidden(D_59,k2_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [D_62] :
      ( ~ r2_hidden(D_62,'#skF_8')
      | r2_hidden(D_62,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_218])).

tff(c_36,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_240,plain,(
    ! [D_63] :
      ( D_63 = '#skF_7'
      | ~ r2_hidden(D_63,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_230,c_36])).

tff(c_244,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_240])).

tff(c_247,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_244])).

tff(c_251,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_26])).

tff(c_254,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_251])).

tff(c_261,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_599,plain,(
    ! [A_99,B_100] :
      ( '#skF_1'(k1_tarski(A_99),B_100) = A_99
      | r1_tarski(k1_tarski(A_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_261,c_36])).

tff(c_623,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_599,c_217])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_631,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_4])).

tff(c_637,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_631])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_637])).

tff(c_640,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_158,plain,(
    ! [D_52,B_53,A_54] :
      ( ~ r2_hidden(D_52,B_53)
      | r2_hidden(D_52,k2_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,'#skF_9')
      | r2_hidden(D_55,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_158])).

tff(c_178,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_1,k1_tarski('#skF_7')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_787,plain,(
    ! [A_112] :
      ( r1_tarski(A_112,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_112,'#skF_8'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_640,c_178])).

tff(c_792,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_787])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_794,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_792,c_28])).

tff(c_797,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_794])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,(
    ! [D_56] :
      ( D_56 = '#skF_7'
      | ~ r2_hidden(D_56,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_170,c_36])).

tff(c_184,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26,c_180])).

tff(c_187,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_184])).

tff(c_191,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_26])).

tff(c_194,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_191])).

tff(c_710,plain,(
    ! [C_104] :
      ( C_104 = '#skF_7'
      | ~ r2_hidden(C_104,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_36])).

tff(c_722,plain,(
    ! [B_2] :
      ( '#skF_1'('#skF_8',B_2) = '#skF_7'
      | r1_tarski('#skF_8',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_710])).

tff(c_801,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_722,c_797])).

tff(c_808,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_4])).

tff(c_814,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_808])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_797,c_814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:46:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.44  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 2.63/1.44  
% 2.63/1.44  %Foreground sorts:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Background operators:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Foreground operators:
% 2.63/1.44  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.63/1.44  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.63/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.63/1.44  
% 2.93/1.45  tff(f_87, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.93/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.93/1.45  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.93/1.45  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.45  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.93/1.45  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.93/1.45  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.93/1.45  tff(c_62, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.93/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.45  tff(c_64, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.93/1.45  tff(c_81, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.93/1.45  tff(c_84, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_81])).
% 2.93/1.45  tff(c_201, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.45  tff(c_211, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_84, c_201])).
% 2.93/1.45  tff(c_217, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_211])).
% 2.93/1.45  tff(c_60, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.93/1.45  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.45  tff(c_218, plain, (![D_59, A_60, B_61]: (~r2_hidden(D_59, A_60) | r2_hidden(D_59, k2_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.45  tff(c_230, plain, (![D_62]: (~r2_hidden(D_62, '#skF_8') | r2_hidden(D_62, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_218])).
% 2.93/1.45  tff(c_36, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.93/1.45  tff(c_240, plain, (![D_63]: (D_63='#skF_7' | ~r2_hidden(D_63, '#skF_8'))), inference(resolution, [status(thm)], [c_230, c_36])).
% 2.93/1.45  tff(c_244, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_240])).
% 2.93/1.45  tff(c_247, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_60, c_244])).
% 2.93/1.45  tff(c_251, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_247, c_26])).
% 2.93/1.45  tff(c_254, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_60, c_251])).
% 2.93/1.45  tff(c_261, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.45  tff(c_599, plain, (![A_99, B_100]: ('#skF_1'(k1_tarski(A_99), B_100)=A_99 | r1_tarski(k1_tarski(A_99), B_100))), inference(resolution, [status(thm)], [c_261, c_36])).
% 2.93/1.45  tff(c_623, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_599, c_217])).
% 2.93/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.45  tff(c_631, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_623, c_4])).
% 2.93/1.45  tff(c_637, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_631])).
% 2.93/1.45  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_637])).
% 2.93/1.45  tff(c_640, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_211])).
% 2.93/1.45  tff(c_158, plain, (![D_52, B_53, A_54]: (~r2_hidden(D_52, B_53) | r2_hidden(D_52, k2_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.45  tff(c_170, plain, (![D_55]: (~r2_hidden(D_55, '#skF_9') | r2_hidden(D_55, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_158])).
% 2.93/1.45  tff(c_178, plain, (![A_1]: (r1_tarski(A_1, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_1, k1_tarski('#skF_7')), '#skF_9'))), inference(resolution, [status(thm)], [c_170, c_4])).
% 2.93/1.45  tff(c_787, plain, (![A_112]: (r1_tarski(A_112, '#skF_8') | ~r2_hidden('#skF_1'(A_112, '#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_640, c_178])).
% 2.93/1.45  tff(c_792, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_6, c_787])).
% 2.93/1.45  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.45  tff(c_794, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_792, c_28])).
% 2.93/1.45  tff(c_797, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_62, c_794])).
% 2.93/1.45  tff(c_58, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.93/1.45  tff(c_180, plain, (![D_56]: (D_56='#skF_7' | ~r2_hidden(D_56, '#skF_9'))), inference(resolution, [status(thm)], [c_170, c_36])).
% 2.93/1.45  tff(c_184, plain, ('#skF_4'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_26, c_180])).
% 2.93/1.45  tff(c_187, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_184])).
% 2.93/1.45  tff(c_191, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_187, c_26])).
% 2.93/1.45  tff(c_194, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_58, c_191])).
% 2.93/1.45  tff(c_710, plain, (![C_104]: (C_104='#skF_7' | ~r2_hidden(C_104, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_36])).
% 2.93/1.45  tff(c_722, plain, (![B_2]: ('#skF_1'('#skF_8', B_2)='#skF_7' | r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_710])).
% 2.93/1.45  tff(c_801, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_722, c_797])).
% 2.93/1.45  tff(c_808, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_801, c_4])).
% 2.93/1.45  tff(c_814, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_808])).
% 2.93/1.45  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_797, c_814])).
% 2.93/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  Inference rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Ref     : 0
% 2.93/1.45  #Sup     : 165
% 2.93/1.45  #Fact    : 0
% 2.93/1.45  #Define  : 0
% 2.93/1.45  #Split   : 3
% 2.93/1.45  #Chain   : 0
% 2.93/1.45  #Close   : 0
% 2.93/1.45  
% 2.93/1.45  Ordering : KBO
% 2.93/1.45  
% 2.93/1.45  Simplification rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Subsume      : 9
% 2.93/1.45  #Demod        : 45
% 2.93/1.45  #Tautology    : 78
% 2.93/1.45  #SimpNegUnit  : 21
% 2.93/1.45  #BackRed      : 4
% 2.93/1.45  
% 2.93/1.45  #Partial instantiations: 0
% 2.93/1.45  #Strategies tried      : 1
% 2.93/1.45  
% 2.93/1.45  Timing (in seconds)
% 2.93/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.32
% 2.93/1.45  Parsing              : 0.16
% 2.93/1.45  CNF conversion       : 0.03
% 2.93/1.45  Main loop            : 0.36
% 2.93/1.45  Inferencing          : 0.13
% 2.93/1.45  Reduction            : 0.11
% 2.93/1.45  Demodulation         : 0.08
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.07
% 2.93/1.45  Abstraction          : 0.02
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.72
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.46  Index Deletion       : 0.00
% 2.93/1.46  Index Matching       : 0.00
% 2.93/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
