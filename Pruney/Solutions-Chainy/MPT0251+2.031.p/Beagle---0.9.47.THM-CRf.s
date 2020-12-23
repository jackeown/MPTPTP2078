%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 (  76 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_141,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r1_tarski(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    ! [A_41] : r2_hidden(A_41,k1_tarski(A_41)) ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k3_xboole_0(A_6,B_7))
      | ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_355,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_91,B_92),B_93),B_92)
      | r1_tarski(k3_xboole_0(A_91,B_92),B_93) ) ),
    inference(resolution,[status(thm)],[c_236,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_374,plain,(
    ! [A_94,B_95] : r1_tarski(k3_xboole_0(A_94,B_95),B_95) ),
    inference(resolution,[status(thm)],[c_355,c_4])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_229,plain,(
    ! [A_28,B_29] :
      ( k1_tarski(A_28) = B_29
      | ~ r1_tarski(B_29,k1_tarski(A_28))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_46,c_224])).

tff(c_813,plain,(
    ! [A_131,A_132] :
      ( k3_xboole_0(A_131,k1_tarski(A_132)) = k1_tarski(A_132)
      | ~ r2_hidden(A_132,k3_xboole_0(A_131,k1_tarski(A_132))) ) ),
    inference(resolution,[status(thm)],[c_374,c_229])).

tff(c_825,plain,(
    ! [A_6,D_11] :
      ( k3_xboole_0(A_6,k1_tarski(D_11)) = k1_tarski(D_11)
      | ~ r2_hidden(D_11,k1_tarski(D_11))
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_813])).

tff(c_835,plain,(
    ! [A_133,D_134] :
      ( k3_xboole_0(A_133,k1_tarski(D_134)) = k1_tarski(D_134)
      | ~ r2_hidden(D_134,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_825])).

tff(c_32,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_917,plain,(
    ! [A_138,D_139] :
      ( k2_xboole_0(A_138,k1_tarski(D_139)) = A_138
      | ~ r2_hidden(D_139,A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_32])).

tff(c_34,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(B_49,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_48,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_168,plain,(
    ! [B_49,A_48] : k2_xboole_0(B_49,A_48) = k2_xboole_0(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_48])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_50])).

tff(c_923,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_188])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.00/1.47  
% 3.00/1.47  %Foreground sorts:
% 3.00/1.47  
% 3.00/1.47  
% 3.00/1.47  %Background operators:
% 3.00/1.47  
% 3.00/1.47  
% 3.00/1.47  %Foreground operators:
% 3.00/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.00/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.00/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.00/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.47  
% 3.00/1.48  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.00/1.48  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.48  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.00/1.48  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.00/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.48  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.00/1.48  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.00/1.48  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.00/1.48  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.48  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.00/1.48  tff(c_141, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r1_tarski(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.48  tff(c_146, plain, (![A_41]: (r2_hidden(A_41, k1_tarski(A_41)))), inference(resolution, [status(thm)], [c_30, c_141])).
% 3.00/1.48  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k3_xboole_0(A_6, B_7)) | ~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.48  tff(c_236, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.48  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.48  tff(c_355, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_1'(k3_xboole_0(A_91, B_92), B_93), B_92) | r1_tarski(k3_xboole_0(A_91, B_92), B_93))), inference(resolution, [status(thm)], [c_236, c_10])).
% 3.00/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.48  tff(c_374, plain, (![A_94, B_95]: (r1_tarski(k3_xboole_0(A_94, B_95), B_95))), inference(resolution, [status(thm)], [c_355, c_4])).
% 3.00/1.48  tff(c_46, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.48  tff(c_224, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.00/1.48  tff(c_229, plain, (![A_28, B_29]: (k1_tarski(A_28)=B_29 | ~r1_tarski(B_29, k1_tarski(A_28)) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_46, c_224])).
% 3.00/1.48  tff(c_813, plain, (![A_131, A_132]: (k3_xboole_0(A_131, k1_tarski(A_132))=k1_tarski(A_132) | ~r2_hidden(A_132, k3_xboole_0(A_131, k1_tarski(A_132))))), inference(resolution, [status(thm)], [c_374, c_229])).
% 3.00/1.48  tff(c_825, plain, (![A_6, D_11]: (k3_xboole_0(A_6, k1_tarski(D_11))=k1_tarski(D_11) | ~r2_hidden(D_11, k1_tarski(D_11)) | ~r2_hidden(D_11, A_6))), inference(resolution, [status(thm)], [c_8, c_813])).
% 3.00/1.48  tff(c_835, plain, (![A_133, D_134]: (k3_xboole_0(A_133, k1_tarski(D_134))=k1_tarski(D_134) | ~r2_hidden(D_134, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_825])).
% 3.00/1.48  tff(c_32, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k3_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.48  tff(c_917, plain, (![A_138, D_139]: (k2_xboole_0(A_138, k1_tarski(D_139))=A_138 | ~r2_hidden(D_139, A_138))), inference(superposition, [status(thm), theory('equality')], [c_835, c_32])).
% 3.00/1.48  tff(c_34, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.48  tff(c_106, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.48  tff(c_162, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(B_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_34, c_106])).
% 3.00/1.48  tff(c_48, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.48  tff(c_168, plain, (![B_49, A_48]: (k2_xboole_0(B_49, A_48)=k2_xboole_0(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_162, c_48])).
% 3.00/1.48  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.48  tff(c_188, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_50])).
% 3.00/1.48  tff(c_923, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_917, c_188])).
% 3.00/1.48  tff(c_953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_923])).
% 3.00/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  Inference rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Ref     : 0
% 3.00/1.48  #Sup     : 208
% 3.00/1.48  #Fact    : 0
% 3.00/1.48  #Define  : 0
% 3.00/1.48  #Split   : 0
% 3.00/1.48  #Chain   : 0
% 3.00/1.48  #Close   : 0
% 3.00/1.48  
% 3.00/1.48  Ordering : KBO
% 3.00/1.48  
% 3.00/1.48  Simplification rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Subsume      : 22
% 3.00/1.48  #Demod        : 22
% 3.00/1.48  #Tautology    : 65
% 3.00/1.48  #SimpNegUnit  : 0
% 3.00/1.48  #BackRed      : 1
% 3.00/1.48  
% 3.00/1.48  #Partial instantiations: 0
% 3.00/1.48  #Strategies tried      : 1
% 3.00/1.48  
% 3.00/1.48  Timing (in seconds)
% 3.00/1.48  ----------------------
% 3.00/1.48  Preprocessing        : 0.30
% 3.00/1.48  Parsing              : 0.15
% 3.00/1.48  CNF conversion       : 0.02
% 3.00/1.48  Main loop            : 0.37
% 3.00/1.48  Inferencing          : 0.14
% 3.00/1.48  Reduction            : 0.11
% 3.00/1.48  Demodulation         : 0.08
% 3.00/1.48  BG Simplification    : 0.02
% 3.00/1.48  Subsumption          : 0.08
% 3.00/1.48  Abstraction          : 0.03
% 3.00/1.48  MUC search           : 0.00
% 3.00/1.48  Cooper               : 0.00
% 3.00/1.48  Total                : 0.70
% 3.00/1.48  Index Insertion      : 0.00
% 3.00/1.48  Index Deletion       : 0.00
% 3.00/1.48  Index Matching       : 0.00
% 3.00/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
