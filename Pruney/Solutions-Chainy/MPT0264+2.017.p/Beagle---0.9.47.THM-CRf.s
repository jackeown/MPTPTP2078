%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 13.05s
% Output     : CNFRefutation 13.05s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  80 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_108,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [B_40,A_39] : r2_hidden(B_40,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( k3_xboole_0(B_26,k1_tarski(A_25)) = k1_tarski(A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_241,plain,(
    ! [A_57,B_58,C_59] : k3_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,A_23)
      | k3_xboole_0(A_23,k1_tarski(B_24)) != k1_tarski(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4730,plain,(
    ! [B_147,A_148,B_149] :
      ( r2_hidden(B_147,k3_xboole_0(A_148,B_149))
      | k3_xboole_0(A_148,k3_xboole_0(B_149,k1_tarski(B_147))) != k1_tarski(B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_38])).

tff(c_11803,plain,(
    ! [A_217,A_218,B_219] :
      ( r2_hidden(A_217,k3_xboole_0(A_218,B_219))
      | k3_xboole_0(A_218,k1_tarski(A_217)) != k1_tarski(A_217)
      | ~ r2_hidden(A_217,B_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4730])).

tff(c_17240,plain,(
    ! [A_239] :
      ( r2_hidden(A_239,k1_tarski('#skF_3'))
      | k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski(A_239)) != k1_tarski(A_239)
      | ~ r2_hidden(A_239,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_11803])).

tff(c_17258,plain,(
    ! [A_240] :
      ( r2_hidden(A_240,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_240,'#skF_5')
      | ~ r2_hidden(A_240,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_17240])).

tff(c_17274,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_17258])).

tff(c_17281,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17274])).

tff(c_30,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1613,plain,(
    ! [E_81,C_82,B_83,A_84] :
      ( E_81 = C_82
      | E_81 = B_83
      | E_81 = A_84
      | ~ r2_hidden(E_81,k1_enumset1(A_84,B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3614,plain,(
    ! [E_114,B_115,A_116] :
      ( E_114 = B_115
      | E_114 = A_116
      | E_114 = A_116
      | ~ r2_hidden(E_114,k2_tarski(A_116,B_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1613])).

tff(c_3627,plain,(
    ! [E_114,A_13] :
      ( E_114 = A_13
      | E_114 = A_13
      | E_114 = A_13
      | ~ r2_hidden(E_114,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3614])).

tff(c_17288,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17281,c_3627])).

tff(c_17294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_42,c_17288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:44:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.05/5.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/5.87  
% 13.05/5.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/5.87  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.05/5.87  
% 13.05/5.87  %Foreground sorts:
% 13.05/5.87  
% 13.05/5.87  
% 13.05/5.87  %Background operators:
% 13.05/5.87  
% 13.05/5.87  
% 13.05/5.87  %Foreground operators:
% 13.05/5.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.05/5.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.05/5.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.05/5.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.05/5.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.05/5.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.05/5.87  tff('#skF_5', type, '#skF_5': $i).
% 13.05/5.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.05/5.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.05/5.87  tff('#skF_3', type, '#skF_3': $i).
% 13.05/5.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.05/5.87  tff('#skF_4', type, '#skF_4': $i).
% 13.05/5.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.05/5.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.05/5.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 13.05/5.87  
% 13.05/5.88  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 13.05/5.88  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.05/5.88  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 13.05/5.88  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 13.05/5.88  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.05/5.88  tff(f_56, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 13.05/5.88  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.05/5.88  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.05/5.88  tff(c_44, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.05/5.88  tff(c_108, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.05/5.88  tff(c_8, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.05/5.88  tff(c_114, plain, (![B_40, A_39]: (r2_hidden(B_40, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 13.05/5.88  tff(c_40, plain, (![B_26, A_25]: (k3_xboole_0(B_26, k1_tarski(A_25))=k1_tarski(A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.05/5.88  tff(c_46, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.05/5.88  tff(c_241, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.05/5.88  tff(c_38, plain, (![B_24, A_23]: (r2_hidden(B_24, A_23) | k3_xboole_0(A_23, k1_tarski(B_24))!=k1_tarski(B_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.05/5.88  tff(c_4730, plain, (![B_147, A_148, B_149]: (r2_hidden(B_147, k3_xboole_0(A_148, B_149)) | k3_xboole_0(A_148, k3_xboole_0(B_149, k1_tarski(B_147)))!=k1_tarski(B_147))), inference(superposition, [status(thm), theory('equality')], [c_241, c_38])).
% 13.05/5.88  tff(c_11803, plain, (![A_217, A_218, B_219]: (r2_hidden(A_217, k3_xboole_0(A_218, B_219)) | k3_xboole_0(A_218, k1_tarski(A_217))!=k1_tarski(A_217) | ~r2_hidden(A_217, B_219))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4730])).
% 13.05/5.88  tff(c_17240, plain, (![A_239]: (r2_hidden(A_239, k1_tarski('#skF_3')) | k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski(A_239))!=k1_tarski(A_239) | ~r2_hidden(A_239, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_11803])).
% 13.05/5.88  tff(c_17258, plain, (![A_240]: (r2_hidden(A_240, k1_tarski('#skF_3')) | ~r2_hidden(A_240, '#skF_5') | ~r2_hidden(A_240, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_17240])).
% 13.05/5.88  tff(c_17274, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_114, c_17258])).
% 13.05/5.88  tff(c_17281, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_17274])).
% 13.05/5.88  tff(c_30, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.05/5.88  tff(c_32, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.05/5.88  tff(c_1613, plain, (![E_81, C_82, B_83, A_84]: (E_81=C_82 | E_81=B_83 | E_81=A_84 | ~r2_hidden(E_81, k1_enumset1(A_84, B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.05/5.88  tff(c_3614, plain, (![E_114, B_115, A_116]: (E_114=B_115 | E_114=A_116 | E_114=A_116 | ~r2_hidden(E_114, k2_tarski(A_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1613])).
% 13.05/5.88  tff(c_3627, plain, (![E_114, A_13]: (E_114=A_13 | E_114=A_13 | E_114=A_13 | ~r2_hidden(E_114, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3614])).
% 13.05/5.88  tff(c_17288, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_17281, c_3627])).
% 13.05/5.88  tff(c_17294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_42, c_17288])).
% 13.05/5.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/5.88  
% 13.05/5.88  Inference rules
% 13.05/5.88  ----------------------
% 13.05/5.88  #Ref     : 0
% 13.05/5.88  #Sup     : 4400
% 13.05/5.88  #Fact    : 6
% 13.05/5.88  #Define  : 0
% 13.05/5.88  #Split   : 0
% 13.05/5.88  #Chain   : 0
% 13.05/5.88  #Close   : 0
% 13.05/5.88  
% 13.05/5.88  Ordering : KBO
% 13.05/5.88  
% 13.05/5.88  Simplification rules
% 13.05/5.88  ----------------------
% 13.05/5.88  #Subsume      : 730
% 13.05/5.88  #Demod        : 3074
% 13.05/5.88  #Tautology    : 425
% 13.05/5.88  #SimpNegUnit  : 1
% 13.05/5.88  #BackRed      : 0
% 13.05/5.88  
% 13.05/5.88  #Partial instantiations: 0
% 13.05/5.88  #Strategies tried      : 1
% 13.05/5.88  
% 13.05/5.88  Timing (in seconds)
% 13.05/5.88  ----------------------
% 13.05/5.89  Preprocessing        : 0.30
% 13.05/5.89  Parsing              : 0.15
% 13.05/5.89  CNF conversion       : 0.02
% 13.20/5.89  Main loop            : 4.83
% 13.20/5.89  Inferencing          : 0.73
% 13.20/5.89  Reduction            : 3.29
% 13.20/5.89  Demodulation         : 3.09
% 13.20/5.89  BG Simplification    : 0.13
% 13.20/5.89  Subsumption          : 0.55
% 13.20/5.89  Abstraction          : 0.20
% 13.20/5.89  MUC search           : 0.00
% 13.20/5.89  Cooper               : 0.00
% 13.20/5.89  Total                : 5.16
% 13.20/5.89  Index Insertion      : 0.00
% 13.20/5.89  Index Deletion       : 0.00
% 13.20/5.89  Index Matching       : 0.00
% 13.20/5.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
