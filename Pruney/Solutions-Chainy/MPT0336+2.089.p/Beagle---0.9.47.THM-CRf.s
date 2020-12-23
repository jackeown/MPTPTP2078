%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 143 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | ~ r1_xboole_0(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_114,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = A_49
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_121,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_67,c_114])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_715,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,k1_tarski(B_94)) = A_93
      | r2_hidden(B_94,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [A_26,C_28,B_27] :
      ( r1_xboole_0(A_26,k4_xboole_0(C_28,B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9933,plain,(
    ! [A_259,A_260,B_261] :
      ( r1_xboole_0(A_259,A_260)
      | ~ r1_tarski(A_259,k1_tarski(B_261))
      | r2_hidden(B_261,A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_32])).

tff(c_9991,plain,(
    ! [A_262] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_262)
      | r2_hidden('#skF_5',A_262) ) ),
    inference(resolution,[status(thm)],[c_53,c_9933])).

tff(c_313,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(k3_xboole_0(A_70,B_71),B_71)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_330,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_313])).

tff(c_10016,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_9991,c_330])).

tff(c_10022,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10016])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1296,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7582,plain,(
    ! [C_238,B_239,A_240] :
      ( ~ r2_hidden(C_238,B_239)
      | ~ r2_hidden(C_238,A_240)
      | k4_xboole_0(A_240,B_239) != A_240 ) ),
    inference(resolution,[status(thm)],[c_30,c_1296])).

tff(c_7597,plain,(
    ! [A_240] :
      ( ~ r2_hidden('#skF_5',A_240)
      | k4_xboole_0(A_240,'#skF_4') != A_240 ) ),
    inference(resolution,[status(thm)],[c_50,c_7582])).

tff(c_10025,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10022,c_7597])).

tff(c_10034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_10025])).

tff(c_10035,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10016])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10047,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10035,c_4])).

tff(c_2279,plain,(
    ! [A_155,C_156,B_157] :
      ( ~ r1_xboole_0(A_155,C_156)
      | ~ r1_xboole_0(A_155,B_157)
      | r1_xboole_0(A_155,k2_xboole_0(B_157,C_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11595,plain,(
    ! [B_282,C_283,A_284] :
      ( r1_xboole_0(k2_xboole_0(B_282,C_283),A_284)
      | ~ r1_xboole_0(A_284,C_283)
      | ~ r1_xboole_0(A_284,B_282) ) ),
    inference(resolution,[status(thm)],[c_2279,c_4])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_11613,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_11595,c_46])).

tff(c_11622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10047,c_67,c_11613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.72  
% 7.79/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.79/2.72  
% 7.79/2.72  %Foreground sorts:
% 7.79/2.72  
% 7.79/2.72  
% 7.79/2.72  %Background operators:
% 7.79/2.72  
% 7.79/2.72  
% 7.79/2.72  %Foreground operators:
% 7.79/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.79/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.79/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.79/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.79/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.79/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.79/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.79/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.79/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.79/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.79/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.79/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.79/2.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.79/2.72  
% 7.79/2.73  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.79/2.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.79/2.73  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.79/2.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.79/2.73  tff(f_106, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.79/2.73  tff(f_89, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.79/2.73  tff(f_81, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 7.79/2.73  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.79/2.73  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.79/2.73  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.79/2.73  tff(c_64, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | ~r1_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/2.73  tff(c_67, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_64])).
% 7.79/2.73  tff(c_114, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=A_49 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.79/2.73  tff(c_121, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_67, c_114])).
% 7.79/2.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.79/2.73  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.79/2.73  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 7.79/2.73  tff(c_715, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k1_tarski(B_94))=A_93 | r2_hidden(B_94, A_93))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.79/2.73  tff(c_32, plain, (![A_26, C_28, B_27]: (r1_xboole_0(A_26, k4_xboole_0(C_28, B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.79/2.73  tff(c_9933, plain, (![A_259, A_260, B_261]: (r1_xboole_0(A_259, A_260) | ~r1_tarski(A_259, k1_tarski(B_261)) | r2_hidden(B_261, A_260))), inference(superposition, [status(thm), theory('equality')], [c_715, c_32])).
% 7.79/2.73  tff(c_9991, plain, (![A_262]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_262) | r2_hidden('#skF_5', A_262))), inference(resolution, [status(thm)], [c_53, c_9933])).
% 7.79/2.73  tff(c_313, plain, (![A_70, B_71]: (~r1_xboole_0(k3_xboole_0(A_70, B_71), B_71) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.79/2.73  tff(c_330, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_313])).
% 7.79/2.73  tff(c_10016, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_9991, c_330])).
% 7.79/2.73  tff(c_10022, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_10016])).
% 7.79/2.73  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.79/2.73  tff(c_30, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k4_xboole_0(A_24, B_25)!=A_24)), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.79/2.73  tff(c_1296, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.79/2.73  tff(c_7582, plain, (![C_238, B_239, A_240]: (~r2_hidden(C_238, B_239) | ~r2_hidden(C_238, A_240) | k4_xboole_0(A_240, B_239)!=A_240)), inference(resolution, [status(thm)], [c_30, c_1296])).
% 7.79/2.73  tff(c_7597, plain, (![A_240]: (~r2_hidden('#skF_5', A_240) | k4_xboole_0(A_240, '#skF_4')!=A_240)), inference(resolution, [status(thm)], [c_50, c_7582])).
% 7.79/2.73  tff(c_10025, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_10022, c_7597])).
% 7.79/2.73  tff(c_10034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_10025])).
% 7.79/2.73  tff(c_10035, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_10016])).
% 7.79/2.73  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/2.73  tff(c_10047, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10035, c_4])).
% 7.79/2.73  tff(c_2279, plain, (![A_155, C_156, B_157]: (~r1_xboole_0(A_155, C_156) | ~r1_xboole_0(A_155, B_157) | r1_xboole_0(A_155, k2_xboole_0(B_157, C_156)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.79/2.73  tff(c_11595, plain, (![B_282, C_283, A_284]: (r1_xboole_0(k2_xboole_0(B_282, C_283), A_284) | ~r1_xboole_0(A_284, C_283) | ~r1_xboole_0(A_284, B_282))), inference(resolution, [status(thm)], [c_2279, c_4])).
% 7.79/2.73  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.79/2.73  tff(c_11613, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_11595, c_46])).
% 7.79/2.73  tff(c_11622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10047, c_67, c_11613])).
% 7.79/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.73  
% 7.79/2.73  Inference rules
% 7.79/2.73  ----------------------
% 7.79/2.73  #Ref     : 0
% 7.79/2.73  #Sup     : 2809
% 7.79/2.73  #Fact    : 0
% 7.79/2.73  #Define  : 0
% 7.79/2.73  #Split   : 2
% 7.79/2.73  #Chain   : 0
% 7.79/2.73  #Close   : 0
% 7.79/2.73  
% 7.79/2.73  Ordering : KBO
% 7.79/2.73  
% 7.79/2.73  Simplification rules
% 7.79/2.74  ----------------------
% 7.79/2.74  #Subsume      : 151
% 7.79/2.74  #Demod        : 2487
% 7.79/2.74  #Tautology    : 1584
% 7.79/2.74  #SimpNegUnit  : 0
% 7.79/2.74  #BackRed      : 4
% 7.79/2.74  
% 7.79/2.74  #Partial instantiations: 0
% 7.79/2.74  #Strategies tried      : 1
% 7.79/2.74  
% 7.79/2.74  Timing (in seconds)
% 7.79/2.74  ----------------------
% 7.79/2.74  Preprocessing        : 0.30
% 7.79/2.74  Parsing              : 0.16
% 7.79/2.74  CNF conversion       : 0.02
% 7.79/2.74  Main loop            : 1.66
% 7.79/2.74  Inferencing          : 0.42
% 7.79/2.74  Reduction            : 0.80
% 7.79/2.74  Demodulation         : 0.68
% 7.79/2.74  BG Simplification    : 0.05
% 7.79/2.74  Subsumption          : 0.28
% 7.79/2.74  Abstraction          : 0.06
% 7.79/2.74  MUC search           : 0.00
% 7.79/2.74  Cooper               : 0.00
% 7.79/2.74  Total                : 1.99
% 7.79/2.74  Index Insertion      : 0.00
% 7.79/2.74  Index Deletion       : 0.00
% 7.79/2.74  Index Matching       : 0.00
% 7.79/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
