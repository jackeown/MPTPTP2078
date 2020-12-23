%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 14.56s
% Output     : CNFRefutation 14.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 116 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 137 expanded)
%              Number of equality atoms :   43 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_34,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_119])).

tff(c_217,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = k3_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_217])).

tff(c_255,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_247])).

tff(c_430,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(k1_tarski(A_56),B_57) = B_57
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_1376,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(k1_tarski(A_87),B_88) = k1_xboole_0
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_133])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1402,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(k1_tarski(A_87),k1_xboole_0) = k3_xboole_0(k1_tarski(A_87),B_88)
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_20])).

tff(c_33187,plain,(
    ! [A_296,B_297] :
      ( k3_xboole_0(k1_tarski(A_296),B_297) = k1_tarski(A_296)
      | ~ r2_hidden(A_296,B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1402])).

tff(c_66,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_40,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_244,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_217])).

tff(c_314,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_244])).

tff(c_722,plain,(
    ! [A_69,B_70,C_71] : k3_xboole_0(k3_xboole_0(A_69,B_70),C_71) = k3_xboole_0(A_69,k3_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_777,plain,(
    ! [C_71] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_71)) = k3_xboole_0('#skF_1',C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_722])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_478,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(B_64,A_63)) = k4_xboole_0(A_63,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_488,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,k3_xboole_0(B_64,A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_20])).

tff(c_536,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k3_xboole_0(B_64,A_63)) = k3_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_488])).

tff(c_2775,plain,(
    ! [C_108,A_109,B_110] : k3_xboole_0(C_108,k3_xboole_0(A_109,B_110)) = k3_xboole_0(A_109,k3_xboole_0(B_110,C_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_2])).

tff(c_5224,plain,(
    ! [C_126] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_126)) = k3_xboole_0(C_126,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_2775])).

tff(c_5338,plain,(
    ! [B_64] : k3_xboole_0(k3_xboole_0(B_64,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_5224])).

tff(c_7503,plain,(
    ! [B_142] : k3_xboole_0(k3_xboole_0(B_142,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_5338])).

tff(c_7634,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7503])).

tff(c_33433,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_33187,c_7634])).

tff(c_33717,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_33433])).

tff(c_33719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_33717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.56/6.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.56/6.45  
% 14.56/6.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.56/6.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.56/6.45  
% 14.56/6.45  %Foreground sorts:
% 14.56/6.45  
% 14.56/6.45  
% 14.56/6.45  %Background operators:
% 14.56/6.45  
% 14.56/6.45  
% 14.56/6.45  %Foreground operators:
% 14.56/6.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.56/6.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.56/6.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.56/6.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.56/6.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.56/6.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.56/6.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.56/6.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.56/6.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.56/6.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.56/6.45  tff('#skF_2', type, '#skF_2': $i).
% 14.56/6.45  tff('#skF_3', type, '#skF_3': $i).
% 14.56/6.45  tff('#skF_1', type, '#skF_1': $i).
% 14.56/6.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.56/6.45  tff('#skF_4', type, '#skF_4': $i).
% 14.56/6.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.56/6.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.56/6.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.56/6.45  
% 14.56/6.46  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 14.56/6.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.56/6.46  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.56/6.46  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.56/6.46  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.56/6.46  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 14.56/6.46  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.56/6.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.56/6.46  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 14.56/6.46  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 14.56/6.46  tff(c_34, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.56/6.46  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.56/6.46  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.56/6.46  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.56/6.46  tff(c_119, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.56/6.46  tff(c_134, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_119])).
% 14.56/6.46  tff(c_217, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.56/6.46  tff(c_247, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=k3_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_134, c_217])).
% 14.56/6.46  tff(c_255, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_247])).
% 14.56/6.46  tff(c_430, plain, (![A_56, B_57]: (k2_xboole_0(k1_tarski(A_56), B_57)=B_57 | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.56/6.46  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.56/6.46  tff(c_133, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_119])).
% 14.56/6.46  tff(c_1376, plain, (![A_87, B_88]: (k4_xboole_0(k1_tarski(A_87), B_88)=k1_xboole_0 | ~r2_hidden(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_430, c_133])).
% 14.56/6.46  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.56/6.46  tff(c_1402, plain, (![A_87, B_88]: (k4_xboole_0(k1_tarski(A_87), k1_xboole_0)=k3_xboole_0(k1_tarski(A_87), B_88) | ~r2_hidden(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_20])).
% 14.56/6.46  tff(c_33187, plain, (![A_296, B_297]: (k3_xboole_0(k1_tarski(A_296), B_297)=k1_tarski(A_296) | ~r2_hidden(A_296, B_297))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_1402])).
% 14.56/6.46  tff(c_66, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.56/6.46  tff(c_38, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.56/6.46  tff(c_81, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66, c_38])).
% 14.56/6.46  tff(c_40, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.56/6.46  tff(c_135, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_119])).
% 14.56/6.46  tff(c_244, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_217])).
% 14.56/6.46  tff(c_314, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_255, c_244])).
% 14.56/6.46  tff(c_722, plain, (![A_69, B_70, C_71]: (k3_xboole_0(k3_xboole_0(A_69, B_70), C_71)=k3_xboole_0(A_69, k3_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.56/6.46  tff(c_777, plain, (![C_71]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_71))=k3_xboole_0('#skF_1', C_71))), inference(superposition, [status(thm), theory('equality')], [c_314, c_722])).
% 14.56/6.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.56/6.46  tff(c_163, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.56/6.46  tff(c_478, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(B_64, A_63))=k4_xboole_0(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_163])).
% 14.56/6.46  tff(c_488, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, k3_xboole_0(B_64, A_63)))), inference(superposition, [status(thm), theory('equality')], [c_478, c_20])).
% 14.56/6.46  tff(c_536, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k3_xboole_0(B_64, A_63))=k3_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_488])).
% 14.56/6.46  tff(c_2775, plain, (![C_108, A_109, B_110]: (k3_xboole_0(C_108, k3_xboole_0(A_109, B_110))=k3_xboole_0(A_109, k3_xboole_0(B_110, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_722, c_2])).
% 14.56/6.46  tff(c_5224, plain, (![C_126]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_126))=k3_xboole_0(C_126, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_2775])).
% 14.56/6.46  tff(c_5338, plain, (![B_64]: (k3_xboole_0(k3_xboole_0(B_64, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_64)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_5224])).
% 14.56/6.46  tff(c_7503, plain, (![B_142]: (k3_xboole_0(k3_xboole_0(B_142, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', B_142))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_5338])).
% 14.56/6.46  tff(c_7634, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_81, c_7503])).
% 14.56/6.46  tff(c_33433, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_33187, c_7634])).
% 14.56/6.46  tff(c_33717, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_33433])).
% 14.56/6.46  tff(c_33719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_33717])).
% 14.56/6.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.56/6.46  
% 14.56/6.46  Inference rules
% 14.56/6.46  ----------------------
% 14.56/6.46  #Ref     : 0
% 14.56/6.46  #Sup     : 8339
% 14.56/6.46  #Fact    : 0
% 14.56/6.46  #Define  : 0
% 14.56/6.46  #Split   : 6
% 14.56/6.46  #Chain   : 0
% 14.56/6.46  #Close   : 0
% 14.56/6.46  
% 14.56/6.46  Ordering : KBO
% 14.56/6.46  
% 14.56/6.46  Simplification rules
% 14.56/6.46  ----------------------
% 14.56/6.46  #Subsume      : 375
% 14.56/6.46  #Demod        : 10577
% 14.56/6.46  #Tautology    : 4807
% 14.56/6.46  #SimpNegUnit  : 22
% 14.56/6.46  #BackRed      : 2
% 14.56/6.46  
% 14.56/6.46  #Partial instantiations: 0
% 14.56/6.46  #Strategies tried      : 1
% 14.56/6.46  
% 14.56/6.46  Timing (in seconds)
% 14.56/6.46  ----------------------
% 14.56/6.47  Preprocessing        : 0.32
% 14.56/6.47  Parsing              : 0.17
% 14.56/6.47  CNF conversion       : 0.02
% 14.56/6.47  Main loop            : 5.33
% 14.56/6.47  Inferencing          : 0.75
% 14.56/6.47  Reduction            : 3.62
% 14.56/6.47  Demodulation         : 3.35
% 14.56/6.47  BG Simplification    : 0.10
% 14.56/6.47  Subsumption          : 0.66
% 14.56/6.47  Abstraction          : 0.16
% 14.56/6.47  MUC search           : 0.00
% 14.56/6.47  Cooper               : 0.00
% 14.56/6.47  Total                : 5.68
% 14.56/6.47  Index Insertion      : 0.00
% 14.56/6.47  Index Deletion       : 0.00
% 14.56/6.47  Index Matching       : 0.00
% 14.56/6.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
