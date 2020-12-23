%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 107 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 ( 123 expanded)
%              Number of equality atoms :   29 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
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

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_138,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_173,plain,(
    ! [B_43,A_44] : k3_tarski(k2_tarski(B_43,A_44)) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_40,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_207,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_40])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ! [A_31,B_32] :
      ( k1_xboole_0 = A_31
      | k2_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_112,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42])).

tff(c_228,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_112])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | k2_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_280,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_8])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_291,plain,(
    ! [A_8] : k4_xboole_0(A_8,'#skF_6') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_10])).

tff(c_20,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_288,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_116])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_349,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_493,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | k4_xboole_0(A_74,B_73) != A_74 ) ),
    inference(resolution,[status(thm)],[c_14,c_349])).

tff(c_497,plain,(
    ! [A_74] :
      ( ~ r2_hidden('#skF_5',A_74)
      | k4_xboole_0(A_74,'#skF_6') != A_74 ) ),
    inference(resolution,[status(thm)],[c_288,c_493])).

tff(c_509,plain,(
    ! [A_74] : ~ r2_hidden('#skF_5',A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_497])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:13:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.32  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.21/1.32  
% 2.21/1.32  %Foreground sorts:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Background operators:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Foreground operators:
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.32  
% 2.50/1.33  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.50/1.33  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.50/1.33  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.50/1.33  tff(f_47, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.50/1.33  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.50/1.33  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.50/1.33  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.50/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.50/1.33  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.33  tff(c_138, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.50/1.33  tff(c_173, plain, (![B_43, A_44]: (k3_tarski(k2_tarski(B_43, A_44))=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 2.50/1.33  tff(c_40, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.50/1.33  tff(c_207, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_173, c_40])).
% 2.50/1.33  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.33  tff(c_58, plain, (![A_31, B_32]: (k1_xboole_0=A_31 | k2_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.33  tff(c_62, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_58])).
% 2.50/1.33  tff(c_112, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42])).
% 2.50/1.33  tff(c_228, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_207, c_112])).
% 2.50/1.33  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | k2_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.33  tff(c_280, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_228, c_8])).
% 2.50/1.33  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.33  tff(c_291, plain, (![A_8]: (k4_xboole_0(A_8, '#skF_6')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_10])).
% 2.50/1.33  tff(c_20, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.33  tff(c_116, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_20])).
% 2.50/1.33  tff(c_288, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_116])).
% 2.50/1.33  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.33  tff(c_349, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.33  tff(c_493, plain, (![C_72, B_73, A_74]: (~r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | k4_xboole_0(A_74, B_73)!=A_74)), inference(resolution, [status(thm)], [c_14, c_349])).
% 2.50/1.33  tff(c_497, plain, (![A_74]: (~r2_hidden('#skF_5', A_74) | k4_xboole_0(A_74, '#skF_6')!=A_74)), inference(resolution, [status(thm)], [c_288, c_493])).
% 2.50/1.33  tff(c_509, plain, (![A_74]: (~r2_hidden('#skF_5', A_74))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_497])).
% 2.50/1.33  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_288])).
% 2.50/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  Inference rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Ref     : 0
% 2.50/1.33  #Sup     : 123
% 2.50/1.33  #Fact    : 0
% 2.50/1.33  #Define  : 0
% 2.50/1.33  #Split   : 1
% 2.50/1.33  #Chain   : 0
% 2.50/1.33  #Close   : 0
% 2.50/1.33  
% 2.50/1.33  Ordering : KBO
% 2.50/1.33  
% 2.50/1.33  Simplification rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Subsume      : 15
% 2.50/1.33  #Demod        : 50
% 2.50/1.33  #Tautology    : 83
% 2.50/1.33  #SimpNegUnit  : 1
% 2.50/1.33  #BackRed      : 12
% 2.50/1.33  
% 2.50/1.33  #Partial instantiations: 0
% 2.50/1.33  #Strategies tried      : 1
% 2.50/1.33  
% 2.50/1.33  Timing (in seconds)
% 2.50/1.33  ----------------------
% 2.50/1.34  Preprocessing        : 0.31
% 2.50/1.34  Parsing              : 0.16
% 2.50/1.34  CNF conversion       : 0.02
% 2.50/1.34  Main loop            : 0.26
% 2.50/1.34  Inferencing          : 0.09
% 2.50/1.34  Reduction            : 0.09
% 2.50/1.34  Demodulation         : 0.07
% 2.50/1.34  BG Simplification    : 0.02
% 2.50/1.34  Subsumption          : 0.04
% 2.50/1.34  Abstraction          : 0.02
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.60
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
