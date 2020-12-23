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
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 164 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 289 expanded)
%              Number of equality atoms :   38 ( 135 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_103,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_141,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_xboole_0(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_48,B_49,A_50] :
      ( r1_xboole_0(A_48,B_49)
      | ~ r1_tarski(A_48,k1_tarski(A_50))
      | r2_hidden(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_28,c_141])).

tff(c_223,plain,(
    ! [B_57] :
      ( r1_xboole_0('#skF_3',B_57)
      | r2_hidden('#skF_4',B_57) ) ),
    inference(resolution,[status(thm)],[c_103,c_179])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_tarski(A_18),B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_69,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_108,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_105])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_236,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_223,c_112])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_241,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_236,c_14])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_241])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_249,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_250,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_89])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_250])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_258,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_8])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_89])).

tff(c_267,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_315,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_xboole_0(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_411,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_xboole_0(A_77,B_78)
      | ~ r1_tarski(A_77,k1_tarski(A_79))
      | r2_hidden(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_28,c_315])).

tff(c_461,plain,(
    ! [B_82] :
      ( r1_xboole_0('#skF_3',B_82)
      | r2_hidden('#skF_4',B_82) ) ),
    inference(resolution,[status(thm)],[c_267,c_411])).

tff(c_269,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_273,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_267,c_269])).

tff(c_283,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_273])).

tff(c_294,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_283])).

tff(c_474,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_461,c_294])).

tff(c_479,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_474,c_14])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_479])).

tff(c_486,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_533,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_32])).

tff(c_534,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_537,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_8])).

tff(c_485,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_485])).

tff(c_546,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_549,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_485])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_549])).

tff(c_554,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_577,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_554,c_36])).

tff(c_578,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_556,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_8])).

tff(c_581,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_556])).

tff(c_553,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_553])).

tff(c_594,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_596,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_553])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.42  
% 2.65/1.42  %Foreground sorts:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Background operators:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Foreground operators:
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.42  
% 2.65/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.44  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.65/1.44  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.65/1.44  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.65/1.44  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.65/1.44  tff(f_51, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.65/1.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.44  tff(c_34, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_59, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.65/1.44  tff(c_40, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_103, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.65/1.44  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.44  tff(c_141, plain, (![A_42, C_43, B_44]: (r1_xboole_0(A_42, C_43) | ~r1_xboole_0(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.44  tff(c_179, plain, (![A_48, B_49, A_50]: (r1_xboole_0(A_48, B_49) | ~r1_tarski(A_48, k1_tarski(A_50)) | r2_hidden(A_50, B_49))), inference(resolution, [status(thm)], [c_28, c_141])).
% 2.65/1.44  tff(c_223, plain, (![B_57]: (r1_xboole_0('#skF_3', B_57) | r2_hidden('#skF_4', B_57))), inference(resolution, [status(thm)], [c_103, c_179])).
% 2.65/1.44  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.44  tff(c_30, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_69, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.65/1.44  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.44  tff(c_105, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_103, c_2])).
% 2.65/1.44  tff(c_108, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_69, c_105])).
% 2.65/1.44  tff(c_112, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_108])).
% 2.65/1.44  tff(c_236, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_223, c_112])).
% 2.65/1.44  tff(c_14, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.44  tff(c_241, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_236, c_14])).
% 2.65/1.44  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_241])).
% 2.65/1.44  tff(c_247, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.65/1.44  tff(c_249, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_247])).
% 2.65/1.44  tff(c_38, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_89, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.65/1.44  tff(c_250, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_89])).
% 2.65/1.44  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_250])).
% 2.65/1.44  tff(c_254, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_247])).
% 2.65/1.44  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.44  tff(c_258, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_8])).
% 2.65/1.44  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_89])).
% 2.65/1.44  tff(c_267, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 2.65/1.44  tff(c_315, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, C_63) | ~r1_xboole_0(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.44  tff(c_411, plain, (![A_77, B_78, A_79]: (r1_xboole_0(A_77, B_78) | ~r1_tarski(A_77, k1_tarski(A_79)) | r2_hidden(A_79, B_78))), inference(resolution, [status(thm)], [c_28, c_315])).
% 2.65/1.44  tff(c_461, plain, (![B_82]: (r1_xboole_0('#skF_3', B_82) | r2_hidden('#skF_4', B_82))), inference(resolution, [status(thm)], [c_267, c_411])).
% 2.65/1.44  tff(c_269, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.44  tff(c_273, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_267, c_269])).
% 2.65/1.44  tff(c_283, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_69, c_273])).
% 2.65/1.44  tff(c_294, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_283])).
% 2.65/1.44  tff(c_474, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_461, c_294])).
% 2.65/1.44  tff(c_479, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_474, c_14])).
% 2.65/1.44  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_479])).
% 2.65/1.44  tff(c_486, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.65/1.44  tff(c_32, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_533, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_32])).
% 2.65/1.44  tff(c_534, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_533])).
% 2.65/1.44  tff(c_537, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_8])).
% 2.65/1.44  tff(c_485, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 2.65/1.44  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_537, c_485])).
% 2.65/1.44  tff(c_546, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_533])).
% 2.65/1.44  tff(c_549, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_485])).
% 2.65/1.44  tff(c_552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_549])).
% 2.65/1.44  tff(c_554, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.65/1.44  tff(c_36, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.44  tff(c_577, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_554, c_554, c_36])).
% 2.65/1.44  tff(c_578, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_577])).
% 2.65/1.44  tff(c_556, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_8])).
% 2.65/1.44  tff(c_581, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_556])).
% 2.65/1.44  tff(c_553, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 2.65/1.44  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_553])).
% 2.65/1.44  tff(c_594, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_577])).
% 2.65/1.44  tff(c_596, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_553])).
% 2.65/1.44  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_596])).
% 2.65/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.44  
% 2.65/1.44  Inference rules
% 2.65/1.44  ----------------------
% 2.65/1.44  #Ref     : 0
% 2.65/1.44  #Sup     : 111
% 2.65/1.44  #Fact    : 0
% 2.65/1.44  #Define  : 0
% 2.65/1.44  #Split   : 11
% 2.65/1.44  #Chain   : 0
% 2.65/1.44  #Close   : 0
% 2.65/1.44  
% 2.65/1.44  Ordering : KBO
% 2.65/1.44  
% 2.65/1.44  Simplification rules
% 2.65/1.44  ----------------------
% 2.65/1.44  #Subsume      : 12
% 2.65/1.44  #Demod        : 51
% 2.65/1.44  #Tautology    : 49
% 2.65/1.44  #SimpNegUnit  : 6
% 2.65/1.44  #BackRed      : 21
% 2.65/1.44  
% 2.65/1.44  #Partial instantiations: 0
% 2.65/1.44  #Strategies tried      : 1
% 2.65/1.44  
% 2.65/1.44  Timing (in seconds)
% 2.65/1.44  ----------------------
% 2.75/1.44  Preprocessing        : 0.32
% 2.75/1.44  Parsing              : 0.17
% 2.75/1.44  CNF conversion       : 0.02
% 2.75/1.44  Main loop            : 0.29
% 2.75/1.44  Inferencing          : 0.10
% 2.75/1.44  Reduction            : 0.08
% 2.75/1.44  Demodulation         : 0.06
% 2.75/1.44  BG Simplification    : 0.02
% 2.75/1.44  Subsumption          : 0.06
% 2.75/1.44  Abstraction          : 0.01
% 2.75/1.44  MUC search           : 0.00
% 2.75/1.44  Cooper               : 0.00
% 2.75/1.44  Total                : 0.65
% 2.75/1.44  Index Insertion      : 0.00
% 2.75/1.44  Index Deletion       : 0.00
% 2.75/1.44  Index Matching       : 0.00
% 2.75/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
