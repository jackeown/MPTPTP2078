%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 201 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 346 expanded)
%              Number of equality atoms :   40 ( 151 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_44,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_199,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_199,c_10])).

tff(c_207,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_201])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_207])).

tff(c_60,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_34,A_33] :
      ( r1_xboole_0(B_34,k1_tarski(A_33))
      | r2_hidden(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_199,c_16])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_216,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6'))
      | ~ r2_hidden(C_7,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_244,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_247,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_244])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_247])).

tff(c_254,plain,(
    ! [C_62] : ~ r2_hidden(C_62,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_258])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_265,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_180])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_266])).

tff(c_270,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_277,plain,(
    ! [A_14] : r1_tarski('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_18])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_180])).

tff(c_285,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_295,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_285,c_10])).

tff(c_301,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_295])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_301])).

tff(c_302,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_285,c_16])).

tff(c_325,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6'))
      | ~ r2_hidden(C_7,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_6])).

tff(c_591,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_602,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_591])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_602])).

tff(c_609,plain,(
    ! [C_87] : ~ r2_hidden(C_87,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_617,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_609])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_617])).

tff(c_624,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_733,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_36])).

tff(c_734,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_738,plain,(
    ! [A_14] : r1_tarski('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_18])).

tff(c_623,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_623])).

tff(c_746,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_748,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_623])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_748])).

tff(c_753,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_763,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_753,c_40])).

tff(c_764,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_755,plain,(
    ! [A_14] : r1_tarski('#skF_5',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_18])).

tff(c_766,plain,(
    ! [A_14] : r1_tarski('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_755])).

tff(c_752,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_752])).

tff(c_779,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_781,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_752])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.32  
% 2.60/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.60/1.33  
% 2.60/1.33  %Foreground sorts:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Background operators:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Foreground operators:
% 2.60/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.33  
% 2.60/1.34  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.34  tff(f_87, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.60/1.34  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.60/1.34  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.60/1.34  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.60/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.60/1.34  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.60/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.34  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.34  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.34  tff(c_38, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_59, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_38])).
% 2.60/1.34  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.34  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.34  tff(c_34, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_70, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_34])).
% 2.60/1.34  tff(c_44, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_199, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.60/1.34  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.34  tff(c_201, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_199, c_10])).
% 2.60/1.34  tff(c_207, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_201])).
% 2.60/1.34  tff(c_212, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_207])).
% 2.60/1.34  tff(c_60, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.34  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.34  tff(c_63, plain, (![B_34, A_33]: (r1_xboole_0(B_34, k1_tarski(A_33)) | r2_hidden(A_33, B_34))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.60/1.34  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.34  tff(c_208, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_199, c_16])).
% 2.60/1.34  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.34  tff(c_216, plain, (![C_7]: (~r1_xboole_0('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden(C_7, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 2.60/1.34  tff(c_244, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_216])).
% 2.60/1.34  tff(c_247, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_63, c_244])).
% 2.60/1.34  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_247])).
% 2.60/1.34  tff(c_254, plain, (![C_62]: (~r2_hidden(C_62, '#skF_5'))), inference(splitRight, [status(thm)], [c_216])).
% 2.60/1.34  tff(c_258, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_254])).
% 2.60/1.34  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_258])).
% 2.60/1.34  tff(c_263, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.60/1.34  tff(c_265, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_263])).
% 2.60/1.34  tff(c_42, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4')) | r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_180, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.60/1.34  tff(c_266, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_180])).
% 2.60/1.34  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_266])).
% 2.60/1.34  tff(c_270, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_263])).
% 2.60/1.34  tff(c_18, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.34  tff(c_277, plain, (![A_14]: (r1_tarski('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_18])).
% 2.60/1.34  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_180])).
% 2.60/1.34  tff(c_285, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_42])).
% 2.60/1.34  tff(c_295, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_285, c_10])).
% 2.60/1.34  tff(c_301, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_295])).
% 2.60/1.34  tff(c_314, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_301])).
% 2.60/1.34  tff(c_302, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_285, c_16])).
% 2.60/1.34  tff(c_325, plain, (![C_7]: (~r1_xboole_0('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden(C_7, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_302, c_6])).
% 2.60/1.34  tff(c_591, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_325])).
% 2.60/1.34  tff(c_602, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_63, c_591])).
% 2.60/1.34  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_602])).
% 2.60/1.34  tff(c_609, plain, (![C_87]: (~r2_hidden(C_87, '#skF_5'))), inference(splitRight, [status(thm)], [c_325])).
% 2.60/1.34  tff(c_617, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_609])).
% 2.60/1.34  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_617])).
% 2.60/1.34  tff(c_624, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 2.60/1.34  tff(c_36, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_733, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_36])).
% 2.60/1.34  tff(c_734, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_733])).
% 2.60/1.34  tff(c_738, plain, (![A_14]: (r1_tarski('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_18])).
% 2.60/1.34  tff(c_623, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 2.60/1.34  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_623])).
% 2.60/1.34  tff(c_746, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_733])).
% 2.60/1.34  tff(c_748, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_746, c_623])).
% 2.60/1.34  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_748])).
% 2.60/1.34  tff(c_753, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 2.60/1.34  tff(c_40, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.60/1.34  tff(c_763, plain, (k1_tarski('#skF_4')='#skF_3' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_753, c_40])).
% 2.60/1.34  tff(c_764, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_763])).
% 2.60/1.34  tff(c_755, plain, (![A_14]: (r1_tarski('#skF_5', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_18])).
% 2.60/1.34  tff(c_766, plain, (![A_14]: (r1_tarski('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_755])).
% 2.60/1.34  tff(c_752, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 2.60/1.34  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_766, c_752])).
% 2.60/1.34  tff(c_779, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_763])).
% 2.60/1.34  tff(c_781, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_752])).
% 2.60/1.34  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_781])).
% 2.60/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  Inference rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Ref     : 0
% 2.60/1.34  #Sup     : 152
% 2.60/1.34  #Fact    : 0
% 2.60/1.34  #Define  : 0
% 2.60/1.34  #Split   : 13
% 2.60/1.34  #Chain   : 0
% 2.60/1.34  #Close   : 0
% 2.60/1.34  
% 2.60/1.34  Ordering : KBO
% 2.60/1.34  
% 2.60/1.34  Simplification rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Subsume      : 18
% 2.60/1.34  #Demod        : 67
% 2.60/1.34  #Tautology    : 87
% 2.60/1.34  #SimpNegUnit  : 12
% 2.60/1.34  #BackRed      : 30
% 2.60/1.34  
% 2.60/1.34  #Partial instantiations: 0
% 2.60/1.34  #Strategies tried      : 1
% 2.60/1.34  
% 2.60/1.34  Timing (in seconds)
% 2.60/1.34  ----------------------
% 2.60/1.34  Preprocessing        : 0.29
% 2.60/1.34  Parsing              : 0.16
% 2.60/1.34  CNF conversion       : 0.02
% 2.60/1.34  Main loop            : 0.29
% 2.60/1.34  Inferencing          : 0.11
% 2.60/1.34  Reduction            : 0.09
% 2.60/1.34  Demodulation         : 0.06
% 2.60/1.34  BG Simplification    : 0.02
% 2.60/1.34  Subsumption          : 0.05
% 2.60/1.34  Abstraction          : 0.01
% 2.60/1.34  MUC search           : 0.00
% 2.60/1.34  Cooper               : 0.00
% 2.60/1.34  Total                : 0.62
% 2.60/1.34  Index Insertion      : 0.00
% 2.60/1.34  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
