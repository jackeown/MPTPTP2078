%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:06 EST 2020

% Result     : Theorem 20.81s
% Output     : CNFRefutation 20.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 168 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 172 expanded)
%              Number of equality atoms :   28 (  96 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_56,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_492,plain,(
    ! [D_141,C_142,B_143,A_144] : k2_enumset1(D_141,C_142,B_143,A_144) = k2_enumset1(A_144,B_143,C_142,D_141) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_512,plain,(
    ! [A_144,B_143,C_142] : k2_enumset1(A_144,B_143,C_142,C_142) = k1_enumset1(C_142,B_143,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_38])).

tff(c_40,plain,(
    ! [A_61,B_62,C_63,D_64] : k3_enumset1(A_61,A_61,B_62,C_63,D_64) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] : k4_enumset1(A_65,A_65,B_66,C_67,D_68,E_69) = k3_enumset1(A_65,B_66,C_67,D_68,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1272,plain,(
    ! [A_181,E_178,C_177,D_182,F_180,B_179] : k2_xboole_0(k3_enumset1(A_181,B_179,C_177,D_182,E_178),k1_tarski(F_180)) = k4_enumset1(A_181,B_179,C_177,D_182,E_178,F_180) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10394,plain,(
    ! [C_293,F_296,E_298,A_295,B_294,D_297] : r1_tarski(k3_enumset1(A_295,B_294,C_293,D_297,E_298),k4_enumset1(A_295,B_294,C_293,D_297,E_298,F_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_16])).

tff(c_10402,plain,(
    ! [A_61,B_62,C_63,F_296,D_64] : r1_tarski(k2_enumset1(A_61,B_62,C_63,D_64),k4_enumset1(A_61,A_61,B_62,C_63,D_64,F_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10394])).

tff(c_45627,plain,(
    ! [C_546,B_548,A_549,D_547,F_545] : r1_tarski(k2_enumset1(A_549,B_548,C_546,D_547),k3_enumset1(A_549,B_548,C_546,D_547,F_545)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10402])).

tff(c_45644,plain,(
    ! [A_58,B_59,C_60,F_545] : r1_tarski(k1_enumset1(A_58,B_59,C_60),k3_enumset1(A_58,A_58,B_59,C_60,F_545)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_45627])).

tff(c_45652,plain,(
    ! [A_550,B_551,C_552,F_553] : r1_tarski(k1_enumset1(A_550,B_551,C_552),k2_enumset1(A_550,B_551,C_552,F_553)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45644])).

tff(c_45663,plain,(
    ! [A_144,B_143,C_142] : r1_tarski(k1_enumset1(A_144,B_143,C_142),k1_enumset1(C_142,B_143,A_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_45652])).

tff(c_45817,plain,(
    ! [A_570,B_571,C_572] : r1_tarski(k1_enumset1(A_570,B_571,C_572),k1_enumset1(C_572,B_571,A_570)) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_45652])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45819,plain,(
    ! [C_572,B_571,A_570] :
      ( k1_enumset1(C_572,B_571,A_570) = k1_enumset1(A_570,B_571,C_572)
      | ~ r1_tarski(k1_enumset1(C_572,B_571,A_570),k1_enumset1(A_570,B_571,C_572)) ) ),
    inference(resolution,[status(thm)],[c_45817,c_8])).

tff(c_45846,plain,(
    ! [C_573,B_574,A_575] : k1_enumset1(C_573,B_574,A_575) = k1_enumset1(A_575,B_574,C_573) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45663,c_45819])).

tff(c_45971,plain,(
    ! [B_57,A_56] : k1_enumset1(B_57,A_56,A_56) = k2_tarski(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_45846])).

tff(c_1814,plain,(
    ! [A_222,B_223,C_224] : k2_enumset1(A_222,B_223,C_224,C_224) = k1_enumset1(C_224,B_223,A_222) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_38])).

tff(c_1836,plain,(
    ! [C_224,B_223] : k1_enumset1(C_224,B_223,B_223) = k1_enumset1(B_223,C_224,C_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_38])).

tff(c_46795,plain,(
    ! [C_583,B_584] : k2_tarski(C_583,B_584) = k2_tarski(B_584,C_583) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45971,c_45971,c_1836])).

tff(c_48,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48624,plain,(
    ! [C_595,B_596] : k3_tarski(k2_tarski(C_595,B_596)) = k2_xboole_0(B_596,C_595) ),
    inference(superposition,[status(thm),theory(equality)],[c_46795,c_48])).

tff(c_48630,plain,(
    ! [C_595,B_596] : k2_xboole_0(C_595,B_596) = k2_xboole_0(B_596,C_595) ),
    inference(superposition,[status(thm),theory(equality)],[c_48624,c_48])).

tff(c_58,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_187,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_48653,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48630,c_222])).

tff(c_48658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48653])).

tff(c_48659,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_48666,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48659,c_16])).

tff(c_54,plain,(
    ! [A_85,C_87,B_86] :
      ( r2_hidden(A_85,C_87)
      | ~ r1_tarski(k2_tarski(A_85,B_86),C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48675,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48666,c_54])).

tff(c_48680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_48675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.81/13.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.81/13.44  
% 20.81/13.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.81/13.45  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 20.81/13.45  
% 20.81/13.45  %Foreground sorts:
% 20.81/13.45  
% 20.81/13.45  
% 20.81/13.45  %Background operators:
% 20.81/13.45  
% 20.81/13.45  
% 20.81/13.45  %Foreground operators:
% 20.81/13.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.81/13.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.81/13.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.81/13.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.81/13.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.81/13.45  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.81/13.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.81/13.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.81/13.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.81/13.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.81/13.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.81/13.45  tff('#skF_2', type, '#skF_2': $i).
% 20.81/13.45  tff('#skF_3', type, '#skF_3': $i).
% 20.81/13.45  tff('#skF_1', type, '#skF_1': $i).
% 20.81/13.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.81/13.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.81/13.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.81/13.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.81/13.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.81/13.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.81/13.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.81/13.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.81/13.45  
% 20.81/13.46  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 20.81/13.46  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.81/13.46  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 20.81/13.46  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 20.81/13.46  tff(f_63, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 20.81/13.46  tff(f_65, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 20.81/13.46  tff(f_67, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 20.81/13.46  tff(f_57, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 20.81/13.46  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.81/13.46  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.81/13.46  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 20.81/13.46  tff(c_56, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.81/13.46  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.81/13.46  tff(c_36, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 20.81/13.46  tff(c_492, plain, (![D_141, C_142, B_143, A_144]: (k2_enumset1(D_141, C_142, B_143, A_144)=k2_enumset1(A_144, B_143, C_142, D_141))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.81/13.46  tff(c_38, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.81/13.46  tff(c_512, plain, (![A_144, B_143, C_142]: (k2_enumset1(A_144, B_143, C_142, C_142)=k1_enumset1(C_142, B_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_492, c_38])).
% 20.81/13.46  tff(c_40, plain, (![A_61, B_62, C_63, D_64]: (k3_enumset1(A_61, A_61, B_62, C_63, D_64)=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.81/13.46  tff(c_42, plain, (![B_66, A_65, C_67, D_68, E_69]: (k4_enumset1(A_65, A_65, B_66, C_67, D_68, E_69)=k3_enumset1(A_65, B_66, C_67, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.81/13.46  tff(c_1272, plain, (![A_181, E_178, C_177, D_182, F_180, B_179]: (k2_xboole_0(k3_enumset1(A_181, B_179, C_177, D_182, E_178), k1_tarski(F_180))=k4_enumset1(A_181, B_179, C_177, D_182, E_178, F_180))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.81/13.46  tff(c_10394, plain, (![C_293, F_296, E_298, A_295, B_294, D_297]: (r1_tarski(k3_enumset1(A_295, B_294, C_293, D_297, E_298), k4_enumset1(A_295, B_294, C_293, D_297, E_298, F_296)))), inference(superposition, [status(thm), theory('equality')], [c_1272, c_16])).
% 20.81/13.46  tff(c_10402, plain, (![A_61, B_62, C_63, F_296, D_64]: (r1_tarski(k2_enumset1(A_61, B_62, C_63, D_64), k4_enumset1(A_61, A_61, B_62, C_63, D_64, F_296)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10394])).
% 20.81/13.46  tff(c_45627, plain, (![C_546, B_548, A_549, D_547, F_545]: (r1_tarski(k2_enumset1(A_549, B_548, C_546, D_547), k3_enumset1(A_549, B_548, C_546, D_547, F_545)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10402])).
% 20.81/13.46  tff(c_45644, plain, (![A_58, B_59, C_60, F_545]: (r1_tarski(k1_enumset1(A_58, B_59, C_60), k3_enumset1(A_58, A_58, B_59, C_60, F_545)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_45627])).
% 20.81/13.46  tff(c_45652, plain, (![A_550, B_551, C_552, F_553]: (r1_tarski(k1_enumset1(A_550, B_551, C_552), k2_enumset1(A_550, B_551, C_552, F_553)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45644])).
% 20.81/13.46  tff(c_45663, plain, (![A_144, B_143, C_142]: (r1_tarski(k1_enumset1(A_144, B_143, C_142), k1_enumset1(C_142, B_143, A_144)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_45652])).
% 20.81/13.46  tff(c_45817, plain, (![A_570, B_571, C_572]: (r1_tarski(k1_enumset1(A_570, B_571, C_572), k1_enumset1(C_572, B_571, A_570)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_45652])).
% 20.81/13.46  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/13.46  tff(c_45819, plain, (![C_572, B_571, A_570]: (k1_enumset1(C_572, B_571, A_570)=k1_enumset1(A_570, B_571, C_572) | ~r1_tarski(k1_enumset1(C_572, B_571, A_570), k1_enumset1(A_570, B_571, C_572)))), inference(resolution, [status(thm)], [c_45817, c_8])).
% 20.81/13.46  tff(c_45846, plain, (![C_573, B_574, A_575]: (k1_enumset1(C_573, B_574, A_575)=k1_enumset1(A_575, B_574, C_573))), inference(demodulation, [status(thm), theory('equality')], [c_45663, c_45819])).
% 20.81/13.46  tff(c_45971, plain, (![B_57, A_56]: (k1_enumset1(B_57, A_56, A_56)=k2_tarski(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_36, c_45846])).
% 20.81/13.46  tff(c_1814, plain, (![A_222, B_223, C_224]: (k2_enumset1(A_222, B_223, C_224, C_224)=k1_enumset1(C_224, B_223, A_222))), inference(superposition, [status(thm), theory('equality')], [c_492, c_38])).
% 20.81/13.46  tff(c_1836, plain, (![C_224, B_223]: (k1_enumset1(C_224, B_223, B_223)=k1_enumset1(B_223, C_224, C_224))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_38])).
% 20.81/13.46  tff(c_46795, plain, (![C_583, B_584]: (k2_tarski(C_583, B_584)=k2_tarski(B_584, C_583))), inference(demodulation, [status(thm), theory('equality')], [c_45971, c_45971, c_1836])).
% 20.81/13.46  tff(c_48, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.81/13.46  tff(c_48624, plain, (![C_595, B_596]: (k3_tarski(k2_tarski(C_595, B_596))=k2_xboole_0(B_596, C_595))), inference(superposition, [status(thm), theory('equality')], [c_46795, c_48])).
% 20.81/13.46  tff(c_48630, plain, (![C_595, B_596]: (k2_xboole_0(C_595, B_596)=k2_xboole_0(B_596, C_595))), inference(superposition, [status(thm), theory('equality')], [c_48624, c_48])).
% 20.81/13.46  tff(c_58, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.81/13.46  tff(c_187, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.81/13.46  tff(c_196, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_187])).
% 20.81/13.46  tff(c_222, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_196])).
% 20.81/13.46  tff(c_48653, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48630, c_222])).
% 20.81/13.46  tff(c_48658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_48653])).
% 20.81/13.46  tff(c_48659, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_196])).
% 20.81/13.46  tff(c_48666, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48659, c_16])).
% 20.81/13.46  tff(c_54, plain, (![A_85, C_87, B_86]: (r2_hidden(A_85, C_87) | ~r1_tarski(k2_tarski(A_85, B_86), C_87))), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.81/13.46  tff(c_48675, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48666, c_54])).
% 20.81/13.46  tff(c_48680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_48675])).
% 20.81/13.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.81/13.46  
% 20.81/13.46  Inference rules
% 20.81/13.46  ----------------------
% 20.81/13.46  #Ref     : 0
% 20.81/13.46  #Sup     : 12920
% 20.81/13.46  #Fact    : 0
% 20.81/13.46  #Define  : 0
% 20.81/13.46  #Split   : 1
% 20.81/13.46  #Chain   : 0
% 20.81/13.46  #Close   : 0
% 20.81/13.46  
% 20.81/13.46  Ordering : KBO
% 20.81/13.46  
% 20.81/13.46  Simplification rules
% 20.81/13.46  ----------------------
% 20.81/13.46  #Subsume      : 812
% 20.81/13.46  #Demod        : 18759
% 20.81/13.46  #Tautology    : 4247
% 20.81/13.46  #SimpNegUnit  : 1
% 20.81/13.46  #BackRed      : 8
% 20.81/13.46  
% 20.81/13.46  #Partial instantiations: 0
% 20.81/13.46  #Strategies tried      : 1
% 20.81/13.46  
% 20.81/13.46  Timing (in seconds)
% 20.81/13.46  ----------------------
% 20.81/13.46  Preprocessing        : 0.32
% 20.81/13.46  Parsing              : 0.17
% 20.81/13.46  CNF conversion       : 0.02
% 20.81/13.46  Main loop            : 12.32
% 20.81/13.46  Inferencing          : 1.38
% 20.81/13.46  Reduction            : 9.09
% 20.81/13.46  Demodulation         : 8.72
% 20.81/13.46  BG Simplification    : 0.26
% 20.81/13.46  Subsumption          : 1.26
% 20.81/13.46  Abstraction          : 0.41
% 20.81/13.46  MUC search           : 0.00
% 20.81/13.46  Cooper               : 0.00
% 20.81/13.46  Total                : 12.67
% 20.81/13.46  Index Insertion      : 0.00
% 20.81/13.47  Index Deletion       : 0.00
% 20.81/13.47  Index Matching       : 0.00
% 20.81/13.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
