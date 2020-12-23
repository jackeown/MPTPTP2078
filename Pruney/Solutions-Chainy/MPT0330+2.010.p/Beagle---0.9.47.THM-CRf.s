%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   52 (  87 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 132 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [B_33,A_34] : k3_tarski(k2_tarski(B_33,A_34)) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_16,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_36,B_35] : r1_tarski(A_36,k2_xboole_0(B_35,A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_241,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k2_zfmisc_1(C_58,A_59),k2_zfmisc_1(C_58,B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2246,plain,(
    ! [A_224,C_225,B_226,A_227] :
      ( r1_tarski(A_224,k2_zfmisc_1(C_225,B_226))
      | ~ r1_tarski(A_224,k2_zfmisc_1(C_225,A_227))
      | ~ r1_tarski(A_227,B_226) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_2278,plain,(
    ! [B_228] :
      ( r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',B_228))
      | ~ r1_tarski('#skF_6',B_228) ) ),
    inference(resolution,[status(thm)],[c_24,c_2246])).

tff(c_180,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(k2_zfmisc_1(A_45,C_46),k2_zfmisc_1(B_47,C_46))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_183,plain,(
    ! [A_1,B_47,C_46,A_45] :
      ( r1_tarski(A_1,k2_zfmisc_1(B_47,C_46))
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_45,C_46))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_4479,plain,(
    ! [B_329,B_330] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_329,B_330))
      | ~ r1_tarski('#skF_5',B_329)
      | ~ r1_tarski('#skF_6',B_330) ) ),
    inference(resolution,[status(thm)],[c_2278,c_183])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_789,plain,(
    ! [A_116,C_117,B_118,A_119] :
      ( r1_tarski(A_116,k2_zfmisc_1(C_117,B_118))
      | ~ r1_tarski(A_116,k2_zfmisc_1(C_117,A_119))
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_838,plain,(
    ! [B_121] :
      ( r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',B_121))
      | ~ r1_tarski('#skF_4',B_121) ) ),
    inference(resolution,[status(thm)],[c_26,c_789])).

tff(c_1806,plain,(
    ! [B_186,B_187] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_186,B_187))
      | ~ r1_tarski('#skF_3',B_186)
      | ~ r1_tarski('#skF_4',B_187) ) ),
    inference(resolution,[status(thm)],[c_838,c_183])).

tff(c_319,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(k2_xboole_0(A_75,C_76),B_77)
      | ~ r1_tarski(C_76,B_77)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_358,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_319,c_22])).

tff(c_359,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_1815,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1806,c_359])).

tff(c_1828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_1815])).

tff(c_1829,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_4498,plain,
    ( ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4479,c_1829])).

tff(c_4516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_4498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.56  
% 6.34/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.56  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.34/2.56  
% 6.34/2.56  %Foreground sorts:
% 6.34/2.56  
% 6.34/2.56  
% 6.34/2.56  %Background operators:
% 6.34/2.56  
% 6.34/2.56  
% 6.34/2.56  %Foreground operators:
% 6.34/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.34/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.34/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.34/2.56  tff('#skF_5', type, '#skF_5': $i).
% 6.34/2.56  tff('#skF_6', type, '#skF_6': $i).
% 6.34/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.34/2.56  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.56  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.56  tff('#skF_1', type, '#skF_1': $i).
% 6.34/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.34/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.56  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.34/2.56  
% 6.34/2.58  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.34/2.58  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.34/2.58  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.34/2.58  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.34/2.58  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.34/2.58  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.34/2.58  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.34/2.58  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.58  tff(c_70, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.58  tff(c_85, plain, (![B_33, A_34]: (k3_tarski(k2_tarski(B_33, A_34))=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_8, c_70])).
% 6.34/2.58  tff(c_16, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.58  tff(c_108, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_85, c_16])).
% 6.34/2.58  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.58  tff(c_123, plain, (![A_36, B_35]: (r1_tarski(A_36, k2_xboole_0(B_35, A_36)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_4])).
% 6.34/2.58  tff(c_24, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.34/2.58  tff(c_241, plain, (![C_58, A_59, B_60]: (r1_tarski(k2_zfmisc_1(C_58, A_59), k2_zfmisc_1(C_58, B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.34/2.58  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.58  tff(c_2246, plain, (![A_224, C_225, B_226, A_227]: (r1_tarski(A_224, k2_zfmisc_1(C_225, B_226)) | ~r1_tarski(A_224, k2_zfmisc_1(C_225, A_227)) | ~r1_tarski(A_227, B_226))), inference(resolution, [status(thm)], [c_241, c_2])).
% 6.34/2.58  tff(c_2278, plain, (![B_228]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', B_228)) | ~r1_tarski('#skF_6', B_228))), inference(resolution, [status(thm)], [c_24, c_2246])).
% 6.34/2.58  tff(c_180, plain, (![A_45, C_46, B_47]: (r1_tarski(k2_zfmisc_1(A_45, C_46), k2_zfmisc_1(B_47, C_46)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.34/2.58  tff(c_183, plain, (![A_1, B_47, C_46, A_45]: (r1_tarski(A_1, k2_zfmisc_1(B_47, C_46)) | ~r1_tarski(A_1, k2_zfmisc_1(A_45, C_46)) | ~r1_tarski(A_45, B_47))), inference(resolution, [status(thm)], [c_180, c_2])).
% 6.34/2.58  tff(c_4479, plain, (![B_329, B_330]: (r1_tarski('#skF_2', k2_zfmisc_1(B_329, B_330)) | ~r1_tarski('#skF_5', B_329) | ~r1_tarski('#skF_6', B_330))), inference(resolution, [status(thm)], [c_2278, c_183])).
% 6.34/2.58  tff(c_26, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.34/2.58  tff(c_789, plain, (![A_116, C_117, B_118, A_119]: (r1_tarski(A_116, k2_zfmisc_1(C_117, B_118)) | ~r1_tarski(A_116, k2_zfmisc_1(C_117, A_119)) | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_241, c_2])).
% 6.34/2.58  tff(c_838, plain, (![B_121]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', B_121)) | ~r1_tarski('#skF_4', B_121))), inference(resolution, [status(thm)], [c_26, c_789])).
% 6.34/2.58  tff(c_1806, plain, (![B_186, B_187]: (r1_tarski('#skF_1', k2_zfmisc_1(B_186, B_187)) | ~r1_tarski('#skF_3', B_186) | ~r1_tarski('#skF_4', B_187))), inference(resolution, [status(thm)], [c_838, c_183])).
% 6.34/2.58  tff(c_319, plain, (![A_75, C_76, B_77]: (r1_tarski(k2_xboole_0(A_75, C_76), B_77) | ~r1_tarski(C_76, B_77) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.34/2.58  tff(c_22, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.34/2.58  tff(c_358, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_319, c_22])).
% 6.34/2.58  tff(c_359, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_358])).
% 6.34/2.58  tff(c_1815, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_1806, c_359])).
% 6.34/2.58  tff(c_1828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_1815])).
% 6.34/2.58  tff(c_1829, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_358])).
% 6.34/2.58  tff(c_4498, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_4479, c_1829])).
% 6.34/2.58  tff(c_4516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_4498])).
% 6.34/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.58  
% 6.34/2.58  Inference rules
% 6.34/2.58  ----------------------
% 6.34/2.58  #Ref     : 0
% 6.34/2.58  #Sup     : 1265
% 6.34/2.58  #Fact    : 0
% 6.34/2.58  #Define  : 0
% 6.34/2.58  #Split   : 11
% 6.34/2.58  #Chain   : 0
% 6.34/2.58  #Close   : 0
% 6.34/2.58  
% 6.34/2.58  Ordering : KBO
% 6.34/2.58  
% 6.34/2.58  Simplification rules
% 6.34/2.58  ----------------------
% 6.34/2.58  #Subsume      : 131
% 6.34/2.58  #Demod        : 208
% 6.34/2.58  #Tautology    : 234
% 6.34/2.58  #SimpNegUnit  : 0
% 6.34/2.58  #BackRed      : 0
% 6.34/2.58  
% 6.34/2.58  #Partial instantiations: 0
% 6.34/2.58  #Strategies tried      : 1
% 6.34/2.58  
% 6.34/2.58  Timing (in seconds)
% 6.34/2.58  ----------------------
% 6.34/2.58  Preprocessing        : 0.46
% 6.34/2.58  Parsing              : 0.25
% 6.34/2.58  CNF conversion       : 0.03
% 6.34/2.58  Main loop            : 1.21
% 6.34/2.58  Inferencing          : 0.31
% 6.34/2.58  Reduction            : 0.46
% 6.34/2.58  Demodulation         : 0.37
% 6.34/2.58  BG Simplification    : 0.04
% 6.34/2.58  Subsumption          : 0.31
% 6.34/2.58  Abstraction          : 0.05
% 6.34/2.58  MUC search           : 0.00
% 6.34/2.58  Cooper               : 0.00
% 6.34/2.58  Total                : 1.71
% 6.34/2.58  Index Insertion      : 0.00
% 6.34/2.58  Index Deletion       : 0.00
% 6.34/2.58  Index Matching       : 0.00
% 6.34/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
