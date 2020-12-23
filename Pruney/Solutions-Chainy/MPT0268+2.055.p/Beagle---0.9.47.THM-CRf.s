%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 169 expanded)
%              Number of equality atoms :   40 (  76 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_60,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_216,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_1'(A_105,B_106,C_107),A_105)
      | r2_hidden('#skF_2'(A_105,B_106,C_107),C_107)
      | k4_xboole_0(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_264,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106,A_105),A_105)
      | k4_xboole_0(A_105,B_106) = A_105 ) ),
    inference(resolution,[status(thm)],[c_216,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1308,plain,(
    ! [A_173,B_174,C_175] :
      ( ~ r2_hidden('#skF_1'(A_173,B_174,C_175),C_175)
      | r2_hidden('#skF_2'(A_173,B_174,C_175),B_174)
      | ~ r2_hidden('#skF_2'(A_173,B_174,C_175),A_173)
      | k4_xboole_0(A_173,B_174) = C_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2626,plain,(
    ! [A_222,B_223] :
      ( r2_hidden('#skF_2'(A_222,B_223,A_222),B_223)
      | ~ r2_hidden('#skF_2'(A_222,B_223,A_222),A_222)
      | k4_xboole_0(A_222,B_223) = A_222 ) ),
    inference(resolution,[status(thm)],[c_12,c_1308])).

tff(c_2649,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_2'(A_224,B_225,A_224),B_225)
      | k4_xboole_0(A_224,B_225) = A_224 ) ),
    inference(resolution,[status(thm)],[c_264,c_2626])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [E_79,C_80,B_81,A_82] :
      ( E_79 = C_80
      | E_79 = B_81
      | E_79 = A_82
      | ~ r2_hidden(E_79,k1_enumset1(A_82,B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_167,plain,(
    ! [E_83,B_84,A_85] :
      ( E_83 = B_84
      | E_83 = A_85
      | E_83 = A_85
      | ~ r2_hidden(E_83,k2_tarski(A_85,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_148])).

tff(c_176,plain,(
    ! [E_83,A_16] :
      ( E_83 = A_16
      | E_83 = A_16
      | E_83 = A_16
      | ~ r2_hidden(E_83,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_167])).

tff(c_15231,plain,(
    ! [A_381,A_382] :
      ( '#skF_2'(A_381,k1_tarski(A_382),A_381) = A_382
      | k4_xboole_0(A_381,k1_tarski(A_382)) = A_381 ) ),
    inference(resolution,[status(thm)],[c_2649,c_176])).

tff(c_15620,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15231,c_103])).

tff(c_15634,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_15620,c_264])).

tff(c_15644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_76,c_15634])).

tff(c_15645,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_80,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,(
    ! [B_56,A_57] : r2_hidden(B_56,k2_tarski(A_57,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_101,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_98])).

tff(c_15646,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15681,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15646,c_64])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15692,plain,(
    ! [D_394] :
      ( ~ r2_hidden(D_394,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_394,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15681,c_4])).

tff(c_15696,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_15692])).

tff(c_15700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15645,c_15696])).

tff(c_15701,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_15706,plain,(
    ! [A_404,B_405] : k1_enumset1(A_404,A_404,B_405) = k2_tarski(A_404,B_405) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15724,plain,(
    ! [B_406,A_407] : r2_hidden(B_406,k2_tarski(A_407,B_406)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15706,c_24])).

tff(c_15727,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_15724])).

tff(c_15702,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15748,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15702,c_66])).

tff(c_15759,plain,(
    ! [D_419] :
      ( ~ r2_hidden(D_419,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_419,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15748,c_4])).

tff(c_15763,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_15727,c_15759])).

tff(c_15767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15701,c_15763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:17:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.48  
% 10.38/3.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.48  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 10.38/3.48  
% 10.38/3.48  %Foreground sorts:
% 10.38/3.48  
% 10.38/3.48  
% 10.38/3.48  %Background operators:
% 10.38/3.48  
% 10.38/3.48  
% 10.38/3.48  %Foreground operators:
% 10.38/3.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.38/3.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/3.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/3.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.38/3.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.38/3.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.38/3.48  tff('#skF_7', type, '#skF_7': $i).
% 10.38/3.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.38/3.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.38/3.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.38/3.48  tff('#skF_5', type, '#skF_5': $i).
% 10.38/3.48  tff('#skF_6', type, '#skF_6': $i).
% 10.38/3.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.38/3.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.38/3.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.38/3.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.38/3.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.38/3.48  tff('#skF_8', type, '#skF_8': $i).
% 10.38/3.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/3.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/3.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.38/3.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.38/3.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.38/3.48  
% 10.38/3.49  tff(f_72, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.38/3.49  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.38/3.49  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.38/3.49  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.38/3.49  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 10.38/3.49  tff(c_60, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/3.49  tff(c_103, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_60])).
% 10.38/3.49  tff(c_62, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/3.49  tff(c_76, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 10.38/3.49  tff(c_216, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_1'(A_105, B_106, C_107), A_105) | r2_hidden('#skF_2'(A_105, B_106, C_107), C_107) | k4_xboole_0(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/3.49  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/3.49  tff(c_264, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106, A_105), A_105) | k4_xboole_0(A_105, B_106)=A_105)), inference(resolution, [status(thm)], [c_216, c_14])).
% 10.38/3.49  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/3.49  tff(c_1308, plain, (![A_173, B_174, C_175]: (~r2_hidden('#skF_1'(A_173, B_174, C_175), C_175) | r2_hidden('#skF_2'(A_173, B_174, C_175), B_174) | ~r2_hidden('#skF_2'(A_173, B_174, C_175), A_173) | k4_xboole_0(A_173, B_174)=C_175)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/3.49  tff(c_2626, plain, (![A_222, B_223]: (r2_hidden('#skF_2'(A_222, B_223, A_222), B_223) | ~r2_hidden('#skF_2'(A_222, B_223, A_222), A_222) | k4_xboole_0(A_222, B_223)=A_222)), inference(resolution, [status(thm)], [c_12, c_1308])).
% 10.38/3.49  tff(c_2649, plain, (![A_224, B_225]: (r2_hidden('#skF_2'(A_224, B_225, A_224), B_225) | k4_xboole_0(A_224, B_225)=A_224)), inference(resolution, [status(thm)], [c_264, c_2626])).
% 10.38/3.49  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.38/3.49  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.38/3.49  tff(c_148, plain, (![E_79, C_80, B_81, A_82]: (E_79=C_80 | E_79=B_81 | E_79=A_82 | ~r2_hidden(E_79, k1_enumset1(A_82, B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.38/3.49  tff(c_167, plain, (![E_83, B_84, A_85]: (E_83=B_84 | E_83=A_85 | E_83=A_85 | ~r2_hidden(E_83, k2_tarski(A_85, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_148])).
% 10.38/3.49  tff(c_176, plain, (![E_83, A_16]: (E_83=A_16 | E_83=A_16 | E_83=A_16 | ~r2_hidden(E_83, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_167])).
% 10.38/3.49  tff(c_15231, plain, (![A_381, A_382]: ('#skF_2'(A_381, k1_tarski(A_382), A_381)=A_382 | k4_xboole_0(A_381, k1_tarski(A_382))=A_381)), inference(resolution, [status(thm)], [c_2649, c_176])).
% 10.38/3.49  tff(c_15620, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15231, c_103])).
% 10.38/3.49  tff(c_15634, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_15620, c_264])).
% 10.38/3.49  tff(c_15644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_76, c_15634])).
% 10.38/3.49  tff(c_15645, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 10.38/3.49  tff(c_80, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.38/3.49  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.38/3.49  tff(c_98, plain, (![B_56, A_57]: (r2_hidden(B_56, k2_tarski(A_57, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_24])).
% 10.38/3.49  tff(c_101, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_98])).
% 10.38/3.49  tff(c_15646, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 10.38/3.49  tff(c_64, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/3.49  tff(c_15681, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15646, c_64])).
% 10.38/3.49  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/3.49  tff(c_15692, plain, (![D_394]: (~r2_hidden(D_394, k1_tarski('#skF_8')) | ~r2_hidden(D_394, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15681, c_4])).
% 10.38/3.49  tff(c_15696, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_101, c_15692])).
% 10.38/3.49  tff(c_15700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15645, c_15696])).
% 10.38/3.49  tff(c_15701, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 10.38/3.49  tff(c_15706, plain, (![A_404, B_405]: (k1_enumset1(A_404, A_404, B_405)=k2_tarski(A_404, B_405))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.38/3.49  tff(c_15724, plain, (![B_406, A_407]: (r2_hidden(B_406, k2_tarski(A_407, B_406)))), inference(superposition, [status(thm), theory('equality')], [c_15706, c_24])).
% 10.38/3.49  tff(c_15727, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_15724])).
% 10.38/3.49  tff(c_15702, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 10.38/3.49  tff(c_66, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/3.49  tff(c_15748, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15702, c_66])).
% 10.38/3.49  tff(c_15759, plain, (![D_419]: (~r2_hidden(D_419, k1_tarski('#skF_8')) | ~r2_hidden(D_419, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15748, c_4])).
% 10.38/3.49  tff(c_15763, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_15727, c_15759])).
% 10.38/3.49  tff(c_15767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15701, c_15763])).
% 10.38/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.49  
% 10.38/3.49  Inference rules
% 10.38/3.49  ----------------------
% 10.38/3.49  #Ref     : 0
% 10.38/3.49  #Sup     : 4255
% 10.38/3.49  #Fact    : 0
% 10.38/3.49  #Define  : 0
% 10.38/3.49  #Split   : 2
% 10.38/3.49  #Chain   : 0
% 10.38/3.49  #Close   : 0
% 10.38/3.49  
% 10.38/3.49  Ordering : KBO
% 10.38/3.49  
% 10.38/3.49  Simplification rules
% 10.38/3.49  ----------------------
% 10.38/3.49  #Subsume      : 2228
% 10.38/3.49  #Demod        : 1880
% 10.38/3.49  #Tautology    : 754
% 10.38/3.49  #SimpNegUnit  : 213
% 10.38/3.49  #BackRed      : 3
% 10.38/3.49  
% 10.38/3.49  #Partial instantiations: 0
% 10.38/3.49  #Strategies tried      : 1
% 10.38/3.49  
% 10.38/3.49  Timing (in seconds)
% 10.38/3.50  ----------------------
% 10.38/3.50  Preprocessing        : 0.31
% 10.38/3.50  Parsing              : 0.15
% 10.38/3.50  CNF conversion       : 0.02
% 10.38/3.50  Main loop            : 2.43
% 10.38/3.50  Inferencing          : 0.62
% 10.38/3.50  Reduction            : 1.16
% 10.38/3.50  Demodulation         : 0.97
% 10.38/3.50  BG Simplification    : 0.08
% 10.38/3.50  Subsumption          : 0.46
% 10.38/3.50  Abstraction          : 0.14
% 10.38/3.50  MUC search           : 0.00
% 10.38/3.50  Cooper               : 0.00
% 10.38/3.50  Total                : 2.77
% 10.38/3.50  Index Insertion      : 0.00
% 10.38/3.50  Index Deletion       : 0.00
% 10.38/3.50  Index Matching       : 0.00
% 10.38/3.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
