%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 18.11s
% Output     : CNFRefutation 18.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 185 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 319 expanded)
%              Number of equality atoms :   50 ( 225 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(c_24,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [A_25] : k1_setfam_1(k1_tarski(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_234,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(k1_setfam_1(A_63),k1_setfam_1(B_64)) = k1_setfam_1(k2_xboole_0(A_63,B_64))
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1654,plain,(
    ! [A_156,B_157] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_156),B_157)) = k3_xboole_0(A_156,k1_setfam_1(B_157))
      | k1_xboole_0 = B_157
      | k1_tarski(A_156) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_234])).

tff(c_1680,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,k1_setfam_1(k1_tarski(B_19))) = k1_setfam_1(k2_tarski(A_18,B_19))
      | k1_tarski(B_19) = k1_xboole_0
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1654])).

tff(c_57139,plain,(
    ! [A_640,B_641] :
      ( k1_setfam_1(k2_tarski(A_640,B_641)) = k3_xboole_0(A_640,B_641)
      | k1_tarski(B_641) = k1_xboole_0
      | k1_tarski(A_640) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1680])).

tff(c_42,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_57165,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57139,c_42])).

tff(c_57168,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_57165])).

tff(c_552,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden('#skF_1'(A_90,B_91,C_92),A_90)
      | r2_hidden('#skF_2'(A_90,B_91,C_92),C_92)
      | k3_xboole_0(A_90,B_91) = C_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1302,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_2'(A_137,B_138,A_137),A_137)
      | k3_xboole_0(A_137,B_138) = A_137 ) ),
    inference(resolution,[status(thm)],[c_552,c_14])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_95,plain,(
    ! [A_38,C_39] :
      ( ~ r1_xboole_0(A_38,A_38)
      | ~ r2_hidden(C_39,A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_91])).

tff(c_98,plain,(
    ! [C_39,B_8] :
      ( ~ r2_hidden(C_39,B_8)
      | k3_xboole_0(B_8,B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_100,plain,(
    ! [C_39,B_8] :
      ( ~ r2_hidden(C_39,B_8)
      | k1_xboole_0 != B_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_98])).

tff(c_1400,plain,(
    ! [A_142,B_143] :
      ( k1_xboole_0 != A_142
      | k3_xboole_0(A_142,B_143) = A_142 ) ),
    inference(resolution,[status(thm)],[c_1302,c_100])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | k3_xboole_0(k1_tarski(A_21),k1_tarski(B_22)) != k1_tarski(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1492,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | k1_tarski(A_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1400,c_36])).

tff(c_57197,plain,(
    ! [B_22] : B_22 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_57168,c_1492])).

tff(c_57202,plain,(
    ! [B_642] : B_642 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_57168,c_1492])).

tff(c_58011,plain,(
    k3_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_57202,c_42])).

tff(c_58023,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_57197,c_58011])).

tff(c_58055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58023])).

tff(c_58056,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_57165])).

tff(c_58086,plain,(
    ! [B_22] : B_22 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_58056,c_1492])).

tff(c_58057,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_57165])).

tff(c_59909,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_58086,c_58057])).

tff(c_59915,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_58086,c_59909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.11/9.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.11/9.32  
% 18.11/9.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.11/9.32  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 18.11/9.32  
% 18.11/9.32  %Foreground sorts:
% 18.11/9.32  
% 18.11/9.32  
% 18.11/9.32  %Background operators:
% 18.11/9.32  
% 18.11/9.32  
% 18.11/9.32  %Foreground operators:
% 18.11/9.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.11/9.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.11/9.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.11/9.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.11/9.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.11/9.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.11/9.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.11/9.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.11/9.32  tff('#skF_5', type, '#skF_5': $i).
% 18.11/9.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.11/9.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.11/9.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.11/9.32  tff('#skF_4', type, '#skF_4': $i).
% 18.11/9.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.11/9.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.11/9.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.11/9.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.11/9.32  
% 18.18/9.34  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 18.18/9.34  tff(f_76, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 18.18/9.34  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 18.18/9.34  tff(f_74, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 18.18/9.34  tff(f_79, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 18.18/9.34  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 18.18/9.34  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 18.18/9.34  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.18/9.34  tff(f_64, axiom, (![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 18.18/9.34  tff(c_24, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.18/9.34  tff(c_40, plain, (![A_25]: (k1_setfam_1(k1_tarski(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.18/9.34  tff(c_32, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.18/9.34  tff(c_234, plain, (![A_63, B_64]: (k3_xboole_0(k1_setfam_1(A_63), k1_setfam_1(B_64))=k1_setfam_1(k2_xboole_0(A_63, B_64)) | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.18/9.34  tff(c_1654, plain, (![A_156, B_157]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_156), B_157))=k3_xboole_0(A_156, k1_setfam_1(B_157)) | k1_xboole_0=B_157 | k1_tarski(A_156)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_234])).
% 18.18/9.34  tff(c_1680, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k1_setfam_1(k1_tarski(B_19)))=k1_setfam_1(k2_tarski(A_18, B_19)) | k1_tarski(B_19)=k1_xboole_0 | k1_tarski(A_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_1654])).
% 18.18/9.34  tff(c_57139, plain, (![A_640, B_641]: (k1_setfam_1(k2_tarski(A_640, B_641))=k3_xboole_0(A_640, B_641) | k1_tarski(B_641)=k1_xboole_0 | k1_tarski(A_640)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1680])).
% 18.18/9.34  tff(c_42, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.18/9.34  tff(c_57165, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_57139, c_42])).
% 18.18/9.34  tff(c_57168, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_57165])).
% 18.18/9.34  tff(c_552, plain, (![A_90, B_91, C_92]: (r2_hidden('#skF_1'(A_90, B_91, C_92), A_90) | r2_hidden('#skF_2'(A_90, B_91, C_92), C_92) | k3_xboole_0(A_90, B_91)=C_92)), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.18/9.34  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.18/9.34  tff(c_1302, plain, (![A_137, B_138]: (r2_hidden('#skF_2'(A_137, B_138, A_137), A_137) | k3_xboole_0(A_137, B_138)=A_137)), inference(resolution, [status(thm)], [c_552, c_14])).
% 18.18/9.34  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.18/9.34  tff(c_91, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.18/9.34  tff(c_95, plain, (![A_38, C_39]: (~r1_xboole_0(A_38, A_38) | ~r2_hidden(C_39, A_38))), inference(superposition, [status(thm), theory('equality')], [c_24, c_91])).
% 18.18/9.34  tff(c_98, plain, (![C_39, B_8]: (~r2_hidden(C_39, B_8) | k3_xboole_0(B_8, B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_95])).
% 18.18/9.34  tff(c_100, plain, (![C_39, B_8]: (~r2_hidden(C_39, B_8) | k1_xboole_0!=B_8)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_98])).
% 18.18/9.34  tff(c_1400, plain, (![A_142, B_143]: (k1_xboole_0!=A_142 | k3_xboole_0(A_142, B_143)=A_142)), inference(resolution, [status(thm)], [c_1302, c_100])).
% 18.18/9.34  tff(c_36, plain, (![B_22, A_21]: (B_22=A_21 | k3_xboole_0(k1_tarski(A_21), k1_tarski(B_22))!=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.18/9.34  tff(c_1492, plain, (![B_22, A_21]: (B_22=A_21 | k1_tarski(A_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1400, c_36])).
% 18.18/9.34  tff(c_57197, plain, (![B_22]: (B_22='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57168, c_1492])).
% 18.18/9.34  tff(c_57202, plain, (![B_642]: (B_642='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57168, c_1492])).
% 18.18/9.34  tff(c_58011, plain, (k3_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_57202, c_42])).
% 18.18/9.34  tff(c_58023, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_57197, c_58011])).
% 18.18/9.34  tff(c_58055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_58023])).
% 18.18/9.34  tff(c_58056, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_57165])).
% 18.18/9.34  tff(c_58086, plain, (![B_22]: (B_22='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_58056, c_1492])).
% 18.18/9.34  tff(c_58057, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_57165])).
% 18.18/9.34  tff(c_59909, plain, (k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_58086, c_58057])).
% 18.18/9.34  tff(c_59915, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_58086, c_59909])).
% 18.18/9.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.18/9.34  
% 18.18/9.34  Inference rules
% 18.18/9.34  ----------------------
% 18.18/9.34  #Ref     : 11
% 18.18/9.34  #Sup     : 16377
% 18.18/9.34  #Fact    : 0
% 18.18/9.34  #Define  : 0
% 18.18/9.34  #Split   : 4
% 18.18/9.34  #Chain   : 0
% 18.18/9.34  #Close   : 0
% 18.18/9.34  
% 18.18/9.34  Ordering : KBO
% 18.18/9.34  
% 18.18/9.34  Simplification rules
% 18.18/9.34  ----------------------
% 18.18/9.34  #Subsume      : 7530
% 18.18/9.34  #Demod        : 4047
% 18.18/9.34  #Tautology    : 3362
% 18.18/9.34  #SimpNegUnit  : 182
% 18.18/9.34  #BackRed      : 30
% 18.18/9.34  
% 18.18/9.34  #Partial instantiations: 229
% 18.18/9.34  #Strategies tried      : 1
% 18.18/9.34  
% 18.18/9.34  Timing (in seconds)
% 18.18/9.34  ----------------------
% 18.18/9.34  Preprocessing        : 0.32
% 18.18/9.34  Parsing              : 0.16
% 18.18/9.34  CNF conversion       : 0.02
% 18.18/9.34  Main loop            : 8.25
% 18.18/9.34  Inferencing          : 1.39
% 18.18/9.34  Reduction            : 3.50
% 18.18/9.34  Demodulation         : 2.90
% 18.18/9.34  BG Simplification    : 0.16
% 18.18/9.34  Subsumption          : 2.89
% 18.18/9.34  Abstraction          : 0.23
% 18.18/9.34  MUC search           : 0.00
% 18.18/9.34  Cooper               : 0.00
% 18.18/9.34  Total                : 8.59
% 18.18/9.34  Index Insertion      : 0.00
% 18.18/9.34  Index Deletion       : 0.00
% 18.18/9.34  Index Matching       : 0.00
% 18.18/9.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
