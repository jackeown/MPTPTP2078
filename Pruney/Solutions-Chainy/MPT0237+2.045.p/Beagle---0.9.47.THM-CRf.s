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
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 123 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 ( 138 expanded)
%              Number of equality atoms :   31 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_91,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_50,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_50] : k3_tarski(k1_tarski(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_149,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_158,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_149])).

tff(c_161,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_158])).

tff(c_235,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(k1_tarski(A_89),B_90) = k1_tarski(A_89)
      | r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_741,plain,(
    ! [B_1536,A_1537] :
      ( k5_xboole_0(B_1536,k1_tarski(A_1537)) = k2_xboole_0(B_1536,k1_tarski(A_1537))
      | r2_hidden(A_1537,B_1536) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_12])).

tff(c_70,plain,(
    ! [A_48,B_49] :
      ( k5_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k2_tarski(A_48,B_49)
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1583,plain,(
    ! [A_6967,A_6968] :
      ( k2_xboole_0(k1_tarski(A_6967),k1_tarski(A_6968)) = k2_tarski(A_6967,A_6968)
      | A_6968 = A_6967
      | r2_hidden(A_6968,k1_tarski(A_6967)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_70])).

tff(c_68,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_74,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6'))) != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_74])).

tff(c_1723,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_75])).

tff(c_1727,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1723])).

tff(c_38,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1766,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1727,c_38])).

tff(c_1773,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) != k2_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1766,c_1766,c_75])).

tff(c_1779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_50,c_1773])).

tff(c_1780,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1723])).

tff(c_1786,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) != k2_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_1780,c_75])).

tff(c_1791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_161,c_1786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.64  
% 3.40/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.64  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.40/1.64  
% 3.40/1.64  %Foreground sorts:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Background operators:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Foreground operators:
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.40/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.40/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.40/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.40/1.64  
% 3.40/1.65  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.65  tff(f_91, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.40/1.65  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.40/1.65  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.40/1.65  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.40/1.65  tff(f_89, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.40/1.65  tff(f_94, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.40/1.65  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.40/1.65  tff(c_50, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.40/1.65  tff(c_72, plain, (![A_50]: (k3_tarski(k1_tarski(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.65  tff(c_149, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.40/1.65  tff(c_158, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_50, c_149])).
% 3.40/1.65  tff(c_161, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_158])).
% 3.40/1.65  tff(c_235, plain, (![A_89, B_90]: (k4_xboole_0(k1_tarski(A_89), B_90)=k1_tarski(A_89) | r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.40/1.65  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.65  tff(c_741, plain, (![B_1536, A_1537]: (k5_xboole_0(B_1536, k1_tarski(A_1537))=k2_xboole_0(B_1536, k1_tarski(A_1537)) | r2_hidden(A_1537, B_1536))), inference(superposition, [status(thm), theory('equality')], [c_235, c_12])).
% 3.40/1.65  tff(c_70, plain, (![A_48, B_49]: (k5_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k2_tarski(A_48, B_49) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.40/1.65  tff(c_1583, plain, (![A_6967, A_6968]: (k2_xboole_0(k1_tarski(A_6967), k1_tarski(A_6968))=k2_tarski(A_6967, A_6968) | A_6968=A_6967 | r2_hidden(A_6968, k1_tarski(A_6967)))), inference(superposition, [status(thm), theory('equality')], [c_741, c_70])).
% 3.40/1.65  tff(c_68, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.40/1.65  tff(c_74, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6')))!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.40/1.65  tff(c_75, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_74])).
% 3.40/1.65  tff(c_1723, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_75])).
% 3.40/1.65  tff(c_1727, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_1723])).
% 3.40/1.65  tff(c_38, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.65  tff(c_1766, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1727, c_38])).
% 3.40/1.65  tff(c_1773, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))!=k2_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1766, c_1766, c_75])).
% 3.40/1.65  tff(c_1779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_50, c_1773])).
% 3.40/1.65  tff(c_1780, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1723])).
% 3.40/1.65  tff(c_1786, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))!=k2_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_1780, c_75])).
% 3.40/1.65  tff(c_1791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_161, c_1786])).
% 3.40/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.65  
% 3.40/1.65  Inference rules
% 3.40/1.65  ----------------------
% 3.40/1.65  #Ref     : 0
% 3.40/1.65  #Sup     : 167
% 3.40/1.65  #Fact    : 0
% 3.40/1.65  #Define  : 0
% 3.40/1.65  #Split   : 2
% 3.40/1.65  #Chain   : 0
% 3.40/1.65  #Close   : 0
% 3.40/1.65  
% 3.40/1.65  Ordering : KBO
% 3.40/1.65  
% 3.40/1.65  Simplification rules
% 3.40/1.65  ----------------------
% 3.40/1.65  #Subsume      : 9
% 3.40/1.65  #Demod        : 61
% 3.40/1.65  #Tautology    : 79
% 3.40/1.65  #SimpNegUnit  : 0
% 3.40/1.65  #BackRed      : 11
% 3.40/1.65  
% 3.40/1.65  #Partial instantiations: 1632
% 3.40/1.65  #Strategies tried      : 1
% 3.40/1.65  
% 3.40/1.65  Timing (in seconds)
% 3.40/1.65  ----------------------
% 3.40/1.65  Preprocessing        : 0.36
% 3.40/1.65  Parsing              : 0.19
% 3.40/1.65  CNF conversion       : 0.03
% 3.40/1.65  Main loop            : 0.48
% 3.40/1.65  Inferencing          : 0.27
% 3.40/1.65  Reduction            : 0.11
% 3.40/1.65  Demodulation         : 0.08
% 3.75/1.65  BG Simplification    : 0.03
% 3.75/1.65  Subsumption          : 0.07
% 3.75/1.65  Abstraction          : 0.02
% 3.75/1.65  MUC search           : 0.00
% 3.75/1.65  Cooper               : 0.00
% 3.75/1.65  Total                : 0.87
% 3.75/1.65  Index Insertion      : 0.00
% 3.75/1.65  Index Deletion       : 0.00
% 3.75/1.65  Index Matching       : 0.00
% 3.75/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
