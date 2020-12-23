%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 176 expanded)
%              Number of equality atoms :   45 ( 161 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_52,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_98,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_99,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_99])).

tff(c_839,plain,(
    ! [B_83,A_84] :
      ( k1_tarski(B_83) = A_84
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,k1_tarski(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_853,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_102,c_839])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_98,c_853])).

tff(c_866,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_867,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_868,plain,(
    ! [A_8] : k2_xboole_0(A_8,'#skF_2') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_8])).

tff(c_942,plain,(
    ! [B_96,A_97] : k2_xboole_0(B_96,A_97) = k2_xboole_0(A_97,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_971,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_56])).

tff(c_1003,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_971])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_1003])).

tff(c_1006,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1007,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1045,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1007,c_54])).

tff(c_1046,plain,(
    ! [B_104,A_105] : k2_xboole_0(B_104,A_105) = k2_xboole_0(A_105,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1008,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_56])).

tff(c_1067,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_1008])).

tff(c_28,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1114,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_28])).

tff(c_1843,plain,(
    ! [B_142,A_143] :
      ( k1_tarski(B_142) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k1_tarski(B_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1858,plain,(
    ! [A_143] :
      ( k1_tarski('#skF_1') = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_1843])).

tff(c_1942,plain,(
    ! [A_144] :
      ( A_144 = '#skF_2'
      | k1_xboole_0 = A_144
      | ~ r1_tarski(A_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1858])).

tff(c_1962,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1114,c_1942])).

tff(c_1978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1006,c_1045,c_1962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  
% 3.10/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.49  
% 3.10/1.49  %Foreground sorts:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Background operators:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Foreground operators:
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.49  
% 3.10/1.50  tff(f_103, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.10/1.50  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.10/1.50  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.10/1.50  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.10/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.10/1.50  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.10/1.50  tff(c_107, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 3.10/1.50  tff(c_50, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.10/1.50  tff(c_98, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 3.10/1.50  tff(c_56, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.10/1.50  tff(c_99, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.50  tff(c_102, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_99])).
% 3.10/1.50  tff(c_839, plain, (![B_83, A_84]: (k1_tarski(B_83)=A_84 | k1_xboole_0=A_84 | ~r1_tarski(A_84, k1_tarski(B_83)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.10/1.50  tff(c_853, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_102, c_839])).
% 3.10/1.50  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_98, c_853])).
% 3.10/1.50  tff(c_866, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 3.10/1.50  tff(c_867, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 3.10/1.50  tff(c_8, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.50  tff(c_868, plain, (![A_8]: (k2_xboole_0(A_8, '#skF_2')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_867, c_8])).
% 3.10/1.50  tff(c_942, plain, (![B_96, A_97]: (k2_xboole_0(B_96, A_97)=k2_xboole_0(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.50  tff(c_971, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_942, c_56])).
% 3.10/1.50  tff(c_1003, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_868, c_971])).
% 3.10/1.50  tff(c_1005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_866, c_1003])).
% 3.10/1.50  tff(c_1006, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.10/1.50  tff(c_1007, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 3.10/1.50  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.10/1.50  tff(c_1045, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1007, c_54])).
% 3.10/1.50  tff(c_1046, plain, (![B_104, A_105]: (k2_xboole_0(B_104, A_105)=k2_xboole_0(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.50  tff(c_1008, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_56])).
% 3.10/1.50  tff(c_1067, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1046, c_1008])).
% 3.10/1.50  tff(c_28, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.50  tff(c_1114, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_28])).
% 3.10/1.50  tff(c_1843, plain, (![B_142, A_143]: (k1_tarski(B_142)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k1_tarski(B_142)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.10/1.50  tff(c_1858, plain, (![A_143]: (k1_tarski('#skF_1')=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1007, c_1843])).
% 3.10/1.50  tff(c_1942, plain, (![A_144]: (A_144='#skF_2' | k1_xboole_0=A_144 | ~r1_tarski(A_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1858])).
% 3.10/1.50  tff(c_1962, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1114, c_1942])).
% 3.10/1.50  tff(c_1978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1006, c_1045, c_1962])).
% 3.10/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  Inference rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Ref     : 0
% 3.10/1.50  #Sup     : 457
% 3.10/1.50  #Fact    : 0
% 3.10/1.50  #Define  : 0
% 3.10/1.50  #Split   : 3
% 3.10/1.50  #Chain   : 0
% 3.10/1.50  #Close   : 0
% 3.10/1.50  
% 3.10/1.50  Ordering : KBO
% 3.10/1.50  
% 3.10/1.50  Simplification rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Subsume      : 4
% 3.10/1.50  #Demod        : 234
% 3.10/1.50  #Tautology    : 310
% 3.10/1.50  #SimpNegUnit  : 4
% 3.10/1.50  #BackRed      : 5
% 3.10/1.50  
% 3.10/1.50  #Partial instantiations: 0
% 3.10/1.50  #Strategies tried      : 1
% 3.10/1.50  
% 3.10/1.50  Timing (in seconds)
% 3.10/1.50  ----------------------
% 3.10/1.50  Preprocessing        : 0.33
% 3.10/1.50  Parsing              : 0.17
% 3.10/1.50  CNF conversion       : 0.02
% 3.10/1.50  Main loop            : 0.44
% 3.10/1.50  Inferencing          : 0.15
% 3.10/1.50  Reduction            : 0.17
% 3.10/1.50  Demodulation         : 0.13
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.07
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.79
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
