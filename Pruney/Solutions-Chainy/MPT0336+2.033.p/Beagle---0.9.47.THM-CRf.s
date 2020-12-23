%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   71 (  91 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 130 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_66,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_306,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(B_79) = A_80
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,k1_tarski(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_328,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_306])).

tff(c_448,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_132,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_494,plain,(
    ! [A_96,B_97,C_98] :
      ( k3_xboole_0(A_96,k2_xboole_0(B_97,C_98)) = k3_xboole_0(A_96,C_98)
      | ~ r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_227,plain,(
    ! [A_60,B_61] :
      ( r1_xboole_0(A_60,B_61)
      | k3_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_233,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_227,c_60])).

tff(c_236,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_503,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_236])).

tff(c_540,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2,c_503])).

tff(c_552,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_540])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_2,c_552])).

tff(c_558,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_81,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [B_45,A_46] : r1_tarski(k3_xboole_0(B_45,A_46),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_570,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_96])).

tff(c_46,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_237,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [E_25,B_20,C_21] : r2_hidden(E_25,k1_enumset1(E_25,B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_255,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_28])).

tff(c_258,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_255])).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_411,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,k3_xboole_0(B_91,C_92))
      | ~ r1_tarski(A_90,C_92)
      | r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_425,plain,(
    ! [A_90] :
      ( ~ r1_xboole_0(A_90,k1_xboole_0)
      | ~ r1_tarski(A_90,'#skF_5')
      | r1_xboole_0(A_90,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_411])).

tff(c_577,plain,(
    ! [A_99] :
      ( ~ r1_tarski(A_99,'#skF_5')
      | r1_xboole_0(A_99,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_425])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1058,plain,(
    ! [C_126,A_127] :
      ( ~ r2_hidden(C_126,'#skF_6')
      | ~ r2_hidden(C_126,A_127)
      | ~ r1_tarski(A_127,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_577,c_8])).

tff(c_1070,plain,(
    ! [A_128] :
      ( ~ r2_hidden('#skF_7',A_128)
      | ~ r1_tarski(A_128,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1058])).

tff(c_1078,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_258,c_1070])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_1078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.44  
% 2.70/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.70/1.44  
% 2.70/1.44  %Foreground sorts:
% 2.70/1.44  
% 2.70/1.44  
% 2.70/1.44  %Background operators:
% 2.70/1.44  
% 2.70/1.44  
% 2.70/1.44  %Foreground operators:
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.70/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.70/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.70/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.44  
% 3.06/1.46  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.06/1.46  tff(f_92, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.06/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.06/1.46  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.06/1.46  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.06/1.46  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.06/1.46  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.46  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.06/1.46  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.06/1.46  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.06/1.46  tff(f_61, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.06/1.46  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.06/1.46  tff(c_66, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.46  tff(c_306, plain, (![B_79, A_80]: (k1_tarski(B_79)=A_80 | k1_xboole_0=A_80 | ~r1_tarski(A_80, k1_tarski(B_79)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.06/1.46  tff(c_328, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_306])).
% 3.06/1.46  tff(c_448, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_328])).
% 3.06/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.46  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.46  tff(c_62, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.46  tff(c_132, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.46  tff(c_140, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_132])).
% 3.06/1.46  tff(c_494, plain, (![A_96, B_97, C_98]: (k3_xboole_0(A_96, k2_xboole_0(B_97, C_98))=k3_xboole_0(A_96, C_98) | ~r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.46  tff(c_227, plain, (![A_60, B_61]: (r1_xboole_0(A_60, B_61) | k3_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.46  tff(c_60, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.46  tff(c_233, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_227, c_60])).
% 3.06/1.46  tff(c_236, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_233])).
% 3.06/1.46  tff(c_503, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_494, c_236])).
% 3.06/1.46  tff(c_540, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2, c_503])).
% 3.06/1.46  tff(c_552, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_540])).
% 3.06/1.46  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_2, c_552])).
% 3.06/1.46  tff(c_558, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_328])).
% 3.06/1.46  tff(c_81, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.46  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.06/1.46  tff(c_96, plain, (![B_45, A_46]: (r1_tarski(k3_xboole_0(B_45, A_46), A_46))), inference(superposition, [status(thm), theory('equality')], [c_81, c_14])).
% 3.06/1.46  tff(c_570, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_558, c_96])).
% 3.06/1.46  tff(c_46, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.06/1.46  tff(c_237, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.46  tff(c_28, plain, (![E_25, B_20, C_21]: (r2_hidden(E_25, k1_enumset1(E_25, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.46  tff(c_255, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_237, c_28])).
% 3.06/1.46  tff(c_258, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_255])).
% 3.06/1.46  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.46  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.46  tff(c_411, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, k3_xboole_0(B_91, C_92)) | ~r1_tarski(A_90, C_92) | r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.46  tff(c_425, plain, (![A_90]: (~r1_xboole_0(A_90, k1_xboole_0) | ~r1_tarski(A_90, '#skF_5') | r1_xboole_0(A_90, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_411])).
% 3.06/1.46  tff(c_577, plain, (![A_99]: (~r1_tarski(A_99, '#skF_5') | r1_xboole_0(A_99, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_425])).
% 3.06/1.46  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.46  tff(c_1058, plain, (![C_126, A_127]: (~r2_hidden(C_126, '#skF_6') | ~r2_hidden(C_126, A_127) | ~r1_tarski(A_127, '#skF_5'))), inference(resolution, [status(thm)], [c_577, c_8])).
% 3.06/1.46  tff(c_1070, plain, (![A_128]: (~r2_hidden('#skF_7', A_128) | ~r1_tarski(A_128, '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1058])).
% 3.06/1.46  tff(c_1078, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_258, c_1070])).
% 3.06/1.46  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_570, c_1078])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 0
% 3.06/1.46  #Sup     : 242
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 1
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 6
% 3.06/1.46  #Demod        : 121
% 3.06/1.46  #Tautology    : 150
% 3.06/1.46  #SimpNegUnit  : 0
% 3.06/1.46  #BackRed      : 3
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.32
% 3.06/1.46  Parsing              : 0.17
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.36
% 3.06/1.46  Inferencing          : 0.13
% 3.06/1.46  Reduction            : 0.13
% 3.06/1.46  Demodulation         : 0.10
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.07
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.71
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
