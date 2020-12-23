%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 226 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :   68 ( 315 expanded)
%              Number of equality atoms :   45 ( 194 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_158,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_158])).

tff(c_1030,plain,(
    ! [A_77,B_78,C_79] : k3_xboole_0(k3_xboole_0(A_77,B_78),C_79) = k3_xboole_0(A_77,k3_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1122,plain,(
    ! [B_2,A_77,B_78] : k3_xboole_0(B_2,k3_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,k3_xboole_0(B_78,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1030])).

tff(c_42,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1882,plain,(
    ! [A_98,B_99,C_100] : r1_tarski(k3_xboole_0(A_98,k3_xboole_0(B_99,C_100)),k3_xboole_0(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_12])).

tff(c_2025,plain,(
    ! [C_100] : r1_tarski(k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_100)),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1882])).

tff(c_2659,plain,(
    ! [C_111] : r1_tarski(k3_xboole_0('#skF_3',k3_xboole_0(C_111,'#skF_2')),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_2025])).

tff(c_2683,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2659])).

tff(c_2699,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2683])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( k1_tarski(B_27) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2703,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2699,c_28])).

tff(c_2709,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2703])).

tff(c_183,plain,(
    ! [A_10,B_11] : k3_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_2752,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_183])).

tff(c_2770,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_2752])).

tff(c_2843,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2770])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2755,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_8])).

tff(c_354,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_396,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_2806,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2770,c_396])).

tff(c_4319,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2755,c_2806])).

tff(c_153,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_16])).

tff(c_4326,plain,
    ( k4_xboole_0('#skF_1','#skF_3') = '#skF_1'
    | k3_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4319,c_157])).

tff(c_4334,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_4326])).

tff(c_5353,plain,(
    ! [A_129,B_130,C_131] : k5_xboole_0(k3_xboole_0(A_129,B_130),k3_xboole_0(A_129,k3_xboole_0(B_130,C_131))) = k4_xboole_0(k3_xboole_0(A_129,B_130),C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_8])).

tff(c_5688,plain,(
    ! [A_132] : k5_xboole_0(k3_xboole_0(A_132,'#skF_2'),k3_xboole_0(A_132,k1_tarski('#skF_4'))) = k4_xboole_0(k3_xboole_0(A_132,'#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5353])).

tff(c_5774,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1',k1_tarski('#skF_4'))) = k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_5688])).

tff(c_5816,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4334,c_8,c_186,c_5774])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( ~ r2_hidden(B_29,A_28)
      | k4_xboole_0(A_28,k1_tarski(B_29)) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5832,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5816,c_34])).

tff(c_5851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5832])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.39  
% 6.49/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.49/2.39  
% 6.49/2.39  %Foreground sorts:
% 6.49/2.39  
% 6.49/2.39  
% 6.49/2.39  %Background operators:
% 6.49/2.39  
% 6.49/2.39  
% 6.49/2.39  %Foreground operators:
% 6.49/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.49/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.49/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.49/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.49/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.49/2.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.49/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.49/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.49/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.49/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.49/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.49/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.49/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.49/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.49/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.49/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.49/2.39  
% 6.58/2.41  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.58/2.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.58/2.41  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.58/2.41  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.58/2.41  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.58/2.41  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.58/2.41  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.58/2.41  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.58/2.41  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.58/2.41  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.58/2.41  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.58/2.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.58/2.41  tff(c_38, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.58/2.41  tff(c_44, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.58/2.41  tff(c_158, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.58/2.41  tff(c_186, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_44, c_158])).
% 6.58/2.41  tff(c_1030, plain, (![A_77, B_78, C_79]: (k3_xboole_0(k3_xboole_0(A_77, B_78), C_79)=k3_xboole_0(A_77, k3_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.58/2.41  tff(c_1122, plain, (![B_2, A_77, B_78]: (k3_xboole_0(B_2, k3_xboole_0(A_77, B_78))=k3_xboole_0(A_77, k3_xboole_0(B_78, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1030])).
% 6.58/2.41  tff(c_42, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.58/2.41  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.58/2.41  tff(c_1882, plain, (![A_98, B_99, C_100]: (r1_tarski(k3_xboole_0(A_98, k3_xboole_0(B_99, C_100)), k3_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_12])).
% 6.58/2.41  tff(c_2025, plain, (![C_100]: (r1_tarski(k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_100)), k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1882])).
% 6.58/2.41  tff(c_2659, plain, (![C_111]: (r1_tarski(k3_xboole_0('#skF_3', k3_xboole_0(C_111, '#skF_2')), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_2025])).
% 6.58/2.41  tff(c_2683, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2659])).
% 6.58/2.41  tff(c_2699, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2683])).
% 6.58/2.41  tff(c_28, plain, (![B_27, A_26]: (k1_tarski(B_27)=A_26 | k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.58/2.41  tff(c_2703, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2699, c_28])).
% 6.58/2.41  tff(c_2709, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_38, c_2703])).
% 6.58/2.41  tff(c_183, plain, (![A_10, B_11]: (k3_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_158])).
% 6.58/2.41  tff(c_2752, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2709, c_183])).
% 6.58/2.41  tff(c_2770, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_2752])).
% 6.58/2.41  tff(c_2843, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_2770])).
% 6.58/2.41  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.58/2.41  tff(c_2755, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2709, c_8])).
% 6.58/2.41  tff(c_354, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.58/2.41  tff(c_396, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 6.58/2.41  tff(c_2806, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2770, c_396])).
% 6.58/2.41  tff(c_4319, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2755, c_2806])).
% 6.58/2.41  tff(c_153, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.58/2.41  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.58/2.41  tff(c_157, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_16])).
% 6.58/2.41  tff(c_4326, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1' | k3_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4319, c_157])).
% 6.58/2.41  tff(c_4334, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_4326])).
% 6.58/2.41  tff(c_5353, plain, (![A_129, B_130, C_131]: (k5_xboole_0(k3_xboole_0(A_129, B_130), k3_xboole_0(A_129, k3_xboole_0(B_130, C_131)))=k4_xboole_0(k3_xboole_0(A_129, B_130), C_131))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_8])).
% 6.58/2.41  tff(c_5688, plain, (![A_132]: (k5_xboole_0(k3_xboole_0(A_132, '#skF_2'), k3_xboole_0(A_132, k1_tarski('#skF_4')))=k4_xboole_0(k3_xboole_0(A_132, '#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5353])).
% 6.58/2.41  tff(c_5774, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', k1_tarski('#skF_4')))=k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_186, c_5688])).
% 6.58/2.41  tff(c_5816, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4334, c_8, c_186, c_5774])).
% 6.58/2.41  tff(c_34, plain, (![B_29, A_28]: (~r2_hidden(B_29, A_28) | k4_xboole_0(A_28, k1_tarski(B_29))!=A_28)), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.58/2.41  tff(c_5832, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5816, c_34])).
% 6.58/2.41  tff(c_5851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_5832])).
% 6.58/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.41  
% 6.58/2.41  Inference rules
% 6.58/2.41  ----------------------
% 6.58/2.41  #Ref     : 0
% 6.58/2.41  #Sup     : 1504
% 6.58/2.41  #Fact    : 1
% 6.58/2.41  #Define  : 0
% 6.58/2.41  #Split   : 4
% 6.58/2.41  #Chain   : 0
% 6.58/2.41  #Close   : 0
% 6.58/2.41  
% 6.58/2.41  Ordering : KBO
% 6.58/2.41  
% 6.58/2.41  Simplification rules
% 6.58/2.41  ----------------------
% 6.58/2.41  #Subsume      : 15
% 6.58/2.41  #Demod        : 1417
% 6.58/2.41  #Tautology    : 788
% 6.58/2.41  #SimpNegUnit  : 11
% 6.58/2.41  #BackRed      : 13
% 6.58/2.41  
% 6.58/2.41  #Partial instantiations: 0
% 6.58/2.41  #Strategies tried      : 1
% 6.58/2.41  
% 6.58/2.41  Timing (in seconds)
% 6.58/2.41  ----------------------
% 6.58/2.41  Preprocessing        : 0.34
% 6.58/2.41  Parsing              : 0.18
% 6.58/2.41  CNF conversion       : 0.02
% 6.58/2.41  Main loop            : 1.25
% 6.58/2.41  Inferencing          : 0.31
% 6.58/2.41  Reduction            : 0.64
% 6.58/2.41  Demodulation         : 0.55
% 6.58/2.41  BG Simplification    : 0.04
% 6.58/2.41  Subsumption          : 0.17
% 6.58/2.41  Abstraction          : 0.06
% 6.58/2.41  MUC search           : 0.00
% 6.58/2.41  Cooper               : 0.00
% 6.58/2.42  Total                : 1.63
% 6.58/2.42  Index Insertion      : 0.00
% 6.58/2.42  Index Deletion       : 0.00
% 6.58/2.42  Index Matching       : 0.00
% 6.58/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
