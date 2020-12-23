%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_82,plain,(
    ! [A_81,B_82] : k1_enumset1(A_81,A_81,B_82) = k2_tarski(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [B_82,A_81] : r2_hidden(B_82,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_62,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,k3_tarski(B_91))
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6480,plain,(
    ! [A_15110,A_15111,B_15112] :
      ( r1_tarski(A_15110,k2_xboole_0(A_15111,B_15112))
      | ~ r2_hidden(A_15110,k2_tarski(A_15111,B_15112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_123])).

tff(c_6503,plain,(
    ! [B_82,A_81] : r1_tarski(B_82,k2_xboole_0(A_81,B_82)) ),
    inference(resolution,[status(thm)],[c_91,c_6480])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_154,plain,(
    ! [A_97,B_98] :
      ( r2_xboole_0(A_97,B_98)
      | B_98 = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [B_100,A_101] :
      ( ~ r1_tarski(B_100,A_101)
      | B_100 = A_101
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_154,c_14])).

tff(c_182,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_170])).

tff(c_332,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_6508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6503,c_332])).

tff(c_6509,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_81,B_82] : r2_hidden(A_81,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_60,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,k3_tarski(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    ! [C_105,B_106,A_107] :
      ( r2_hidden(C_105,B_106)
      | ~ r2_hidden(C_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_284,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden(A_117,B_118)
      | ~ r1_tarski(k2_tarski(A_117,B_119),B_118) ) ),
    inference(resolution,[status(thm)],[c_88,c_192])).

tff(c_7006,plain,(
    ! [A_15350,B_15351,B_15352] :
      ( r2_hidden(A_15350,k3_tarski(B_15351))
      | ~ r2_hidden(k2_tarski(A_15350,B_15352),B_15351) ) ),
    inference(resolution,[status(thm)],[c_60,c_284])).

tff(c_7074,plain,(
    ! [A_15350,B_15352,B_82] : r2_hidden(A_15350,k3_tarski(k2_tarski(k2_tarski(A_15350,B_15352),B_82))) ),
    inference(resolution,[status(thm)],[c_88,c_7006])).

tff(c_7156,plain,(
    ! [A_15363,B_15364,B_15365] : r2_hidden(A_15363,k2_xboole_0(k2_tarski(A_15363,B_15364),B_15365)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7074])).

tff(c_7169,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6509,c_7156])).

tff(c_7181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.36  
% 6.39/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.37  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.39/2.37  
% 6.39/2.37  %Foreground sorts:
% 6.39/2.37  
% 6.39/2.37  
% 6.39/2.37  %Background operators:
% 6.39/2.37  
% 6.39/2.37  
% 6.39/2.37  %Foreground operators:
% 6.39/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.39/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.39/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.39/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.39/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.39/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.39/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.39/2.37  tff('#skF_6', type, '#skF_6': $i).
% 6.39/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.39/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.39/2.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.39/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.39/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.39/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.39/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.39/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.39/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.39/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.39/2.37  
% 6.42/2.38  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.42/2.38  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.42/2.38  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.42/2.38  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.42/2.38  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.42/2.38  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.42/2.38  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.42/2.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.42/2.38  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.42/2.38  tff(c_82, plain, (![A_81, B_82]: (k1_enumset1(A_81, A_81, B_82)=k2_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.42/2.38  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.42/2.38  tff(c_91, plain, (![B_82, A_81]: (r2_hidden(B_82, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_18])).
% 6.42/2.38  tff(c_62, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.42/2.38  tff(c_123, plain, (![A_90, B_91]: (r1_tarski(A_90, k3_tarski(B_91)) | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.42/2.38  tff(c_6480, plain, (![A_15110, A_15111, B_15112]: (r1_tarski(A_15110, k2_xboole_0(A_15111, B_15112)) | ~r2_hidden(A_15110, k2_tarski(A_15111, B_15112)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_123])).
% 6.42/2.38  tff(c_6503, plain, (![B_82, A_81]: (r1_tarski(B_82, k2_xboole_0(A_81, B_82)))), inference(resolution, [status(thm)], [c_91, c_6480])).
% 6.42/2.38  tff(c_66, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.42/2.38  tff(c_154, plain, (![A_97, B_98]: (r2_xboole_0(A_97, B_98) | B_98=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.38  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.42/2.38  tff(c_170, plain, (![B_100, A_101]: (~r1_tarski(B_100, A_101) | B_100=A_101 | ~r1_tarski(A_101, B_100))), inference(resolution, [status(thm)], [c_154, c_14])).
% 6.42/2.38  tff(c_182, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_170])).
% 6.42/2.38  tff(c_332, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_182])).
% 6.42/2.38  tff(c_6508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6503, c_332])).
% 6.42/2.38  tff(c_6509, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_182])).
% 6.42/2.38  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.42/2.38  tff(c_88, plain, (![A_81, B_82]: (r2_hidden(A_81, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 6.42/2.38  tff(c_60, plain, (![A_62, B_63]: (r1_tarski(A_62, k3_tarski(B_63)) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.42/2.38  tff(c_192, plain, (![C_105, B_106, A_107]: (r2_hidden(C_105, B_106) | ~r2_hidden(C_105, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.42/2.38  tff(c_284, plain, (![A_117, B_118, B_119]: (r2_hidden(A_117, B_118) | ~r1_tarski(k2_tarski(A_117, B_119), B_118))), inference(resolution, [status(thm)], [c_88, c_192])).
% 6.42/2.38  tff(c_7006, plain, (![A_15350, B_15351, B_15352]: (r2_hidden(A_15350, k3_tarski(B_15351)) | ~r2_hidden(k2_tarski(A_15350, B_15352), B_15351))), inference(resolution, [status(thm)], [c_60, c_284])).
% 6.42/2.38  tff(c_7074, plain, (![A_15350, B_15352, B_82]: (r2_hidden(A_15350, k3_tarski(k2_tarski(k2_tarski(A_15350, B_15352), B_82))))), inference(resolution, [status(thm)], [c_88, c_7006])).
% 6.42/2.38  tff(c_7156, plain, (![A_15363, B_15364, B_15365]: (r2_hidden(A_15363, k2_xboole_0(k2_tarski(A_15363, B_15364), B_15365)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7074])).
% 6.42/2.38  tff(c_7169, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6509, c_7156])).
% 6.42/2.38  tff(c_7181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_7169])).
% 6.42/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.38  
% 6.42/2.38  Inference rules
% 6.42/2.38  ----------------------
% 6.42/2.38  #Ref     : 0
% 6.42/2.38  #Sup     : 876
% 6.42/2.38  #Fact    : 18
% 6.42/2.38  #Define  : 0
% 6.42/2.38  #Split   : 1
% 6.42/2.38  #Chain   : 0
% 6.42/2.38  #Close   : 0
% 6.42/2.38  
% 6.42/2.38  Ordering : KBO
% 6.42/2.38  
% 6.42/2.38  Simplification rules
% 6.42/2.38  ----------------------
% 6.42/2.38  #Subsume      : 90
% 6.42/2.38  #Demod        : 206
% 6.42/2.38  #Tautology    : 233
% 6.42/2.38  #SimpNegUnit  : 1
% 6.42/2.38  #BackRed      : 2
% 6.42/2.38  
% 6.42/2.38  #Partial instantiations: 4848
% 6.42/2.38  #Strategies tried      : 1
% 6.42/2.38  
% 6.42/2.38  Timing (in seconds)
% 6.42/2.38  ----------------------
% 6.42/2.38  Preprocessing        : 0.36
% 6.42/2.38  Parsing              : 0.17
% 6.42/2.38  CNF conversion       : 0.03
% 6.42/2.38  Main loop            : 1.20
% 6.42/2.38  Inferencing          : 0.62
% 6.42/2.38  Reduction            : 0.31
% 6.42/2.38  Demodulation         : 0.24
% 6.42/2.38  BG Simplification    : 0.06
% 6.42/2.38  Subsumption          : 0.15
% 6.42/2.38  Abstraction          : 0.05
% 6.42/2.38  MUC search           : 0.00
% 6.42/2.38  Cooper               : 0.00
% 6.42/2.38  Total                : 1.59
% 6.42/2.38  Index Insertion      : 0.00
% 6.42/2.38  Index Deletion       : 0.00
% 6.42/2.38  Index Matching       : 0.00
% 6.42/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
