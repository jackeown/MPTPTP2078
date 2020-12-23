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
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 18.73s
% Output     : CNFRefutation 18.81s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 205 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_tarski('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_66])).

tff(c_42,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_308,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_443,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,A_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_308])).

tff(c_568,plain,(
    ! [D_83] :
      ( r2_hidden(D_83,'#skF_8')
      | ~ r2_hidden(D_83,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_443])).

tff(c_588,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_568])).

tff(c_64,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1340,plain,(
    ! [D_111,A_112,B_113] :
      ( r2_hidden(D_111,k4_xboole_0(A_112,B_113))
      | r2_hidden(D_111,B_113)
      | ~ r2_hidden(D_111,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16414,plain,(
    ! [D_287,A_288,B_289] :
      ( r2_hidden(D_287,k4_xboole_0(A_288,B_289))
      | r2_hidden(D_287,k3_xboole_0(A_288,B_289))
      | ~ r2_hidden(D_287,A_288) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1340])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46715,plain,(
    ! [D_643,B_644,A_645] :
      ( ~ r2_hidden(D_643,B_644)
      | r2_hidden(D_643,k3_xboole_0(A_645,B_644))
      | ~ r2_hidden(D_643,A_645) ) ),
    inference(resolution,[status(thm)],[c_16414,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    k3_xboole_0('#skF_6','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    k3_xboole_0('#skF_8','#skF_6') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_68,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_162,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_153])).

tff(c_769,plain,(
    ! [A_94,B_95,C_96] : k3_xboole_0(k3_xboole_0(A_94,B_95),C_96) = k3_xboole_0(A_94,k3_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_891,plain,(
    ! [C_98] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_7',C_98)) = k3_xboole_0('#skF_6',C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_769])).

tff(c_948,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_9')) = k3_xboole_0('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_891])).

tff(c_964,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_9')) = k3_xboole_0('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_948])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15083,plain,(
    ! [A_267,B_268,B_269] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_267,B_268),B_269),A_267)
      | r1_tarski(k4_xboole_0(A_267,B_268),B_269) ) ),
    inference(resolution,[status(thm)],[c_8,c_308])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15259,plain,(
    ! [A_270,B_271] : r1_tarski(k4_xboole_0(A_270,B_271),A_270) ),
    inference(resolution,[status(thm)],[c_15083,c_6])).

tff(c_15328,plain,(
    ! [A_272,B_273] : r1_tarski(k3_xboole_0(A_272,B_273),A_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_15259])).

tff(c_15553,plain,(
    ! [A_274,B_275] : r1_tarski(k3_xboole_0(A_274,B_275),B_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15328])).

tff(c_15691,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_6'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_15553])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17026,plain,
    ( k3_xboole_0('#skF_8','#skF_6') = k1_tarski('#skF_9')
    | ~ r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_15691,c_30])).

tff(c_17038,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_17026])).

tff(c_263,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_268,plain,(
    ! [A_27,B_55] :
      ( '#skF_1'(k1_tarski(A_27),B_55) = A_27
      | r1_tarski(k1_tarski(A_27),B_55) ) ),
    inference(resolution,[status(thm)],[c_263,c_44])).

tff(c_17045,plain,(
    '#skF_1'(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_268,c_17038])).

tff(c_24170,plain,
    ( ~ r2_hidden('#skF_9',k3_xboole_0('#skF_8','#skF_6'))
    | r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17045,c_6])).

tff(c_24186,plain,(
    ~ r2_hidden('#skF_9',k3_xboole_0('#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_17038,c_24170])).

tff(c_46746,plain,
    ( ~ r2_hidden('#skF_9','#skF_6')
    | ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_46715,c_24186])).

tff(c_47033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_64,c_46746])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.73/9.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.73/9.89  
% 18.73/9.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.73/9.89  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 18.73/9.89  
% 18.73/9.89  %Foreground sorts:
% 18.73/9.89  
% 18.73/9.89  
% 18.73/9.89  %Background operators:
% 18.73/9.89  
% 18.73/9.89  
% 18.73/9.89  %Foreground operators:
% 18.73/9.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.73/9.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.73/9.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.73/9.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.73/9.89  tff('#skF_7', type, '#skF_7': $i).
% 18.73/9.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.73/9.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.73/9.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.73/9.89  tff('#skF_6', type, '#skF_6': $i).
% 18.73/9.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.73/9.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.73/9.89  tff('#skF_9', type, '#skF_9': $i).
% 18.73/9.89  tff('#skF_8', type, '#skF_8': $i).
% 18.73/9.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.73/9.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.73/9.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.73/9.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.73/9.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.73/9.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 18.73/9.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.73/9.89  
% 18.81/9.90  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 18.81/9.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.81/9.90  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 18.81/9.90  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.81/9.90  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.81/9.90  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 18.81/9.90  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.81/9.90  tff(f_54, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 18.81/9.90  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.81/9.90  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.81/9.90  tff(c_46, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.81/9.90  tff(c_101, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.81/9.90  tff(c_66, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.81/9.90  tff(c_116, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_tarski('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_101, c_66])).
% 18.81/9.90  tff(c_42, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.81/9.90  tff(c_308, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k4_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.81/9.90  tff(c_443, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, A_71) | ~r2_hidden(D_70, k3_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_308])).
% 18.81/9.90  tff(c_568, plain, (![D_83]: (r2_hidden(D_83, '#skF_8') | ~r2_hidden(D_83, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_116, c_443])).
% 18.81/9.90  tff(c_588, plain, (r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_46, c_568])).
% 18.81/9.90  tff(c_64, plain, (r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.81/9.90  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.81/9.90  tff(c_1340, plain, (![D_111, A_112, B_113]: (r2_hidden(D_111, k4_xboole_0(A_112, B_113)) | r2_hidden(D_111, B_113) | ~r2_hidden(D_111, A_112))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.81/9.90  tff(c_16414, plain, (![D_287, A_288, B_289]: (r2_hidden(D_287, k4_xboole_0(A_288, B_289)) | r2_hidden(D_287, k3_xboole_0(A_288, B_289)) | ~r2_hidden(D_287, A_288))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1340])).
% 18.81/9.90  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.81/9.90  tff(c_46715, plain, (![D_643, B_644, A_645]: (~r2_hidden(D_643, B_644) | r2_hidden(D_643, k3_xboole_0(A_645, B_644)) | ~r2_hidden(D_643, A_645))), inference(resolution, [status(thm)], [c_16414, c_12])).
% 18.81/9.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.81/9.90  tff(c_62, plain, (k3_xboole_0('#skF_6', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.81/9.90  tff(c_70, plain, (k3_xboole_0('#skF_8', '#skF_6')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 18.81/9.90  tff(c_68, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.81/9.90  tff(c_153, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.81/9.90  tff(c_162, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_68, c_153])).
% 18.81/9.90  tff(c_769, plain, (![A_94, B_95, C_96]: (k3_xboole_0(k3_xboole_0(A_94, B_95), C_96)=k3_xboole_0(A_94, k3_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.81/9.90  tff(c_891, plain, (![C_98]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_7', C_98))=k3_xboole_0('#skF_6', C_98))), inference(superposition, [status(thm), theory('equality')], [c_162, c_769])).
% 18.81/9.90  tff(c_948, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_9'))=k3_xboole_0('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_66, c_891])).
% 18.81/9.90  tff(c_964, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_9'))=k3_xboole_0('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_948])).
% 18.81/9.90  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.81/9.90  tff(c_15083, plain, (![A_267, B_268, B_269]: (r2_hidden('#skF_1'(k4_xboole_0(A_267, B_268), B_269), A_267) | r1_tarski(k4_xboole_0(A_267, B_268), B_269))), inference(resolution, [status(thm)], [c_8, c_308])).
% 18.81/9.90  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.81/9.90  tff(c_15259, plain, (![A_270, B_271]: (r1_tarski(k4_xboole_0(A_270, B_271), A_270))), inference(resolution, [status(thm)], [c_15083, c_6])).
% 18.81/9.90  tff(c_15328, plain, (![A_272, B_273]: (r1_tarski(k3_xboole_0(A_272, B_273), A_272))), inference(superposition, [status(thm), theory('equality')], [c_42, c_15259])).
% 18.81/9.90  tff(c_15553, plain, (![A_274, B_275]: (r1_tarski(k3_xboole_0(A_274, B_275), B_275))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15328])).
% 18.81/9.90  tff(c_15691, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_6'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_964, c_15553])).
% 18.81/9.90  tff(c_30, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.81/9.90  tff(c_17026, plain, (k3_xboole_0('#skF_8', '#skF_6')=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_15691, c_30])).
% 18.81/9.90  tff(c_17038, plain, (~r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_17026])).
% 18.81/9.90  tff(c_263, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.81/9.90  tff(c_44, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.81/9.90  tff(c_268, plain, (![A_27, B_55]: ('#skF_1'(k1_tarski(A_27), B_55)=A_27 | r1_tarski(k1_tarski(A_27), B_55))), inference(resolution, [status(thm)], [c_263, c_44])).
% 18.81/9.90  tff(c_17045, plain, ('#skF_1'(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))='#skF_9'), inference(resolution, [status(thm)], [c_268, c_17038])).
% 18.81/9.90  tff(c_24170, plain, (~r2_hidden('#skF_9', k3_xboole_0('#skF_8', '#skF_6')) | r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_17045, c_6])).
% 18.81/9.90  tff(c_24186, plain, (~r2_hidden('#skF_9', k3_xboole_0('#skF_8', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_17038, c_24170])).
% 18.81/9.90  tff(c_46746, plain, (~r2_hidden('#skF_9', '#skF_6') | ~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_46715, c_24186])).
% 18.81/9.90  tff(c_47033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_588, c_64, c_46746])).
% 18.81/9.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.81/9.90  
% 18.81/9.90  Inference rules
% 18.81/9.90  ----------------------
% 18.81/9.90  #Ref     : 0
% 18.81/9.90  #Sup     : 11646
% 18.81/9.90  #Fact    : 0
% 18.81/9.90  #Define  : 0
% 18.81/9.90  #Split   : 4
% 18.81/9.90  #Chain   : 0
% 18.81/9.90  #Close   : 0
% 18.81/9.90  
% 18.81/9.90  Ordering : KBO
% 18.81/9.90  
% 18.81/9.90  Simplification rules
% 18.81/9.90  ----------------------
% 18.81/9.90  #Subsume      : 2083
% 18.81/9.90  #Demod        : 11558
% 18.81/9.90  #Tautology    : 3951
% 18.81/9.90  #SimpNegUnit  : 56
% 18.81/9.90  #BackRed      : 19
% 18.81/9.90  
% 18.81/9.90  #Partial instantiations: 0
% 18.81/9.90  #Strategies tried      : 1
% 18.81/9.90  
% 18.81/9.90  Timing (in seconds)
% 18.81/9.90  ----------------------
% 18.81/9.91  Preprocessing        : 0.30
% 18.81/9.91  Parsing              : 0.15
% 18.81/9.91  CNF conversion       : 0.02
% 18.81/9.91  Main loop            : 8.78
% 18.81/9.91  Inferencing          : 1.17
% 18.81/9.91  Reduction            : 5.16
% 18.81/9.91  Demodulation         : 4.59
% 18.81/9.91  BG Simplification    : 0.16
% 18.81/9.91  Subsumption          : 1.88
% 18.81/9.91  Abstraction          : 0.23
% 18.81/9.91  MUC search           : 0.00
% 18.81/9.91  Cooper               : 0.00
% 18.81/9.91  Total                : 9.11
% 18.81/9.91  Index Insertion      : 0.00
% 18.81/9.91  Index Deletion       : 0.00
% 18.81/9.91  Index Matching       : 0.00
% 18.81/9.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
