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
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    ! [A_57,C_58,B_59] : k2_xboole_0(k2_zfmisc_1(A_57,C_58),k2_zfmisc_1(B_59,C_58)) = k2_zfmisc_1(k2_xboole_0(A_57,B_59),C_58) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2031,plain,(
    ! [A_209,A_210,B_211,C_212] :
      ( r1_tarski(A_209,k2_zfmisc_1(k2_xboole_0(A_210,B_211),C_212))
      | ~ r1_tarski(A_209,k2_zfmisc_1(B_211,C_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2])).

tff(c_296,plain,(
    ! [C_81,A_82,B_83] : k2_xboole_0(k2_zfmisc_1(C_81,A_82),k2_zfmisc_1(C_81,B_83)) = k2_zfmisc_1(C_81,k2_xboole_0(A_82,B_83)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1759,plain,(
    ! [A_189,C_190,A_191,B_192] :
      ( r1_tarski(A_189,k2_zfmisc_1(C_190,k2_xboole_0(A_191,B_192)))
      | ~ r1_tarski(A_189,k2_zfmisc_1(C_190,B_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_2])).

tff(c_20,plain,(
    ! [C_25,A_23,B_24] : k2_xboole_0(k2_zfmisc_1(C_25,A_23),k2_zfmisc_1(C_25,B_24)) = k2_zfmisc_1(C_25,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [A_57,C_58,B_59] : r1_tarski(k2_zfmisc_1(A_57,C_58),k2_zfmisc_1(k2_xboole_0(A_57,B_59),C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_6])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_38,A_39,B_40] :
      ( r1_tarski(A_38,k2_xboole_0(A_39,B_40))
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_836,plain,(
    ! [A_123,A_124,B_125,A_126] :
      ( r1_tarski(A_123,k2_xboole_0(A_124,B_125))
      | ~ r1_tarski(A_123,A_126)
      | ~ r1_tarski(A_126,A_124) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_1122,plain,(
    ! [A_143,B_144] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_143,B_144))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_143) ) ),
    inference(resolution,[status(thm)],[c_26,c_836])).

tff(c_1197,plain,(
    ! [B_147,B_148] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3',B_147),'#skF_4'),B_148)) ),
    inference(resolution,[status(thm)],[c_155,c_1122])).

tff(c_1217,plain,(
    ! [B_147,B_24] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_147),k2_xboole_0('#skF_4',B_24))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1197])).

tff(c_81,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k2_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(C_47,B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_81,c_22])).

tff(c_400,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_1459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_400])).

tff(c_1460,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_1795,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1759,c_1460])).

tff(c_2042,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2031,c_1795])).

tff(c_2083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:32:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.81  
% 4.34/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.81  %$ r1_tarski > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.34/1.81  
% 4.34/1.81  %Foreground sorts:
% 4.34/1.81  
% 4.34/1.81  
% 4.34/1.81  %Background operators:
% 4.34/1.81  
% 4.34/1.81  
% 4.34/1.81  %Foreground operators:
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.34/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.34/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.34/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.34/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.34/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.34/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.34/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.34/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.34/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.34/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.34/1.81  
% 4.48/1.82  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.48/1.82  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.48/1.82  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.48/1.82  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.48/1.82  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.48/1.82  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.48/1.82  tff(c_24, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.48/1.82  tff(c_138, plain, (![A_57, C_58, B_59]: (k2_xboole_0(k2_zfmisc_1(A_57, C_58), k2_zfmisc_1(B_59, C_58))=k2_zfmisc_1(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.48/1.82  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.48/1.82  tff(c_2031, plain, (![A_209, A_210, B_211, C_212]: (r1_tarski(A_209, k2_zfmisc_1(k2_xboole_0(A_210, B_211), C_212)) | ~r1_tarski(A_209, k2_zfmisc_1(B_211, C_212)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_2])).
% 4.48/1.82  tff(c_296, plain, (![C_81, A_82, B_83]: (k2_xboole_0(k2_zfmisc_1(C_81, A_82), k2_zfmisc_1(C_81, B_83))=k2_zfmisc_1(C_81, k2_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.48/1.82  tff(c_1759, plain, (![A_189, C_190, A_191, B_192]: (r1_tarski(A_189, k2_zfmisc_1(C_190, k2_xboole_0(A_191, B_192))) | ~r1_tarski(A_189, k2_zfmisc_1(C_190, B_192)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_2])).
% 4.48/1.82  tff(c_20, plain, (![C_25, A_23, B_24]: (k2_xboole_0(k2_zfmisc_1(C_25, A_23), k2_zfmisc_1(C_25, B_24))=k2_zfmisc_1(C_25, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.48/1.82  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.48/1.82  tff(c_155, plain, (![A_57, C_58, B_59]: (r1_tarski(k2_zfmisc_1(A_57, C_58), k2_zfmisc_1(k2_xboole_0(A_57, B_59), C_58)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_6])).
% 4.48/1.82  tff(c_26, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.48/1.82  tff(c_47, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.82  tff(c_60, plain, (![A_38, A_39, B_40]: (r1_tarski(A_38, k2_xboole_0(A_39, B_40)) | ~r1_tarski(A_38, A_39))), inference(resolution, [status(thm)], [c_6, c_47])).
% 4.48/1.82  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.82  tff(c_836, plain, (![A_123, A_124, B_125, A_126]: (r1_tarski(A_123, k2_xboole_0(A_124, B_125)) | ~r1_tarski(A_123, A_126) | ~r1_tarski(A_126, A_124))), inference(resolution, [status(thm)], [c_60, c_4])).
% 4.48/1.82  tff(c_1122, plain, (![A_143, B_144]: (r1_tarski('#skF_1', k2_xboole_0(A_143, B_144)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_143))), inference(resolution, [status(thm)], [c_26, c_836])).
% 4.48/1.82  tff(c_1197, plain, (![B_147, B_148]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3', B_147), '#skF_4'), B_148)))), inference(resolution, [status(thm)], [c_155, c_1122])).
% 4.48/1.82  tff(c_1217, plain, (![B_147, B_24]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_147), k2_xboole_0('#skF_4', B_24))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1197])).
% 4.48/1.82  tff(c_81, plain, (![A_46, C_47, B_48]: (r1_tarski(k2_xboole_0(A_46, C_47), B_48) | ~r1_tarski(C_47, B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.48/1.82  tff(c_22, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.48/1.82  tff(c_87, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_81, c_22])).
% 4.48/1.82  tff(c_400, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_87])).
% 4.48/1.82  tff(c_1459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1217, c_400])).
% 4.48/1.82  tff(c_1460, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_87])).
% 4.48/1.82  tff(c_1795, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_1759, c_1460])).
% 4.48/1.82  tff(c_2042, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2031, c_1795])).
% 4.48/1.82  tff(c_2083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2042])).
% 4.48/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.82  
% 4.48/1.82  Inference rules
% 4.48/1.82  ----------------------
% 4.48/1.82  #Ref     : 0
% 4.48/1.82  #Sup     : 567
% 4.48/1.82  #Fact    : 0
% 4.48/1.82  #Define  : 0
% 4.48/1.82  #Split   : 4
% 4.48/1.82  #Chain   : 0
% 4.48/1.82  #Close   : 0
% 4.48/1.82  
% 4.48/1.82  Ordering : KBO
% 4.48/1.82  
% 4.48/1.82  Simplification rules
% 4.48/1.82  ----------------------
% 4.48/1.82  #Subsume      : 22
% 4.48/1.82  #Demod        : 72
% 4.48/1.82  #Tautology    : 92
% 4.48/1.82  #SimpNegUnit  : 4
% 4.48/1.82  #BackRed      : 1
% 4.48/1.82  
% 4.48/1.82  #Partial instantiations: 0
% 4.48/1.82  #Strategies tried      : 1
% 4.48/1.82  
% 4.48/1.82  Timing (in seconds)
% 4.48/1.82  ----------------------
% 4.48/1.83  Preprocessing        : 0.31
% 4.48/1.83  Parsing              : 0.17
% 4.48/1.83  CNF conversion       : 0.02
% 4.48/1.83  Main loop            : 0.67
% 4.48/1.83  Inferencing          : 0.21
% 4.48/1.83  Reduction            : 0.23
% 4.48/1.83  Demodulation         : 0.18
% 4.48/1.83  BG Simplification    : 0.03
% 4.48/1.83  Subsumption          : 0.15
% 4.48/1.83  Abstraction          : 0.03
% 4.48/1.83  MUC search           : 0.00
% 4.48/1.83  Cooper               : 0.00
% 4.48/1.83  Total                : 1.01
% 4.48/1.83  Index Insertion      : 0.00
% 4.48/1.83  Index Deletion       : 0.00
% 4.48/1.83  Index Matching       : 0.00
% 4.48/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
