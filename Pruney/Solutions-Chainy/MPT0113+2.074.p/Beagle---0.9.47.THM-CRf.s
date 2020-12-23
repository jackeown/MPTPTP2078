%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   49 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 111 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_181,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_418,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_819,plain,(
    ! [A_152,B_153,B_154,B_155] :
      ( r2_hidden('#skF_1'(A_152,B_153),B_154)
      | ~ r1_tarski(B_155,B_154)
      | ~ r1_tarski(A_152,B_155)
      | r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_418,c_2])).

tff(c_866,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164,B_165),k4_xboole_0('#skF_3','#skF_4'))
      | ~ r1_tarski(A_164,'#skF_2')
      | r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_24,c_819])).

tff(c_963,plain,(
    ! [A_181,B_182,B_183] :
      ( r2_hidden('#skF_1'(A_181,B_182),B_183)
      | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_183)
      | ~ r1_tarski(A_181,'#skF_2')
      | r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_866,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2412,plain,(
    ! [B_349,A_350] :
      ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_349)
      | ~ r1_tarski(A_350,'#skF_2')
      | r1_tarski(A_350,B_349) ) ),
    inference(resolution,[status(thm)],[c_963,c_4])).

tff(c_2425,plain,(
    ! [A_351] :
      ( ~ r1_tarski(A_351,'#skF_2')
      | r1_tarski(A_351,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_2412])).

tff(c_2429,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_2425])).

tff(c_2437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_2429])).

tff(c_2438,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2440,plain,(
    ! [B_352,A_353] :
      ( r1_xboole_0(B_352,A_353)
      | ~ r1_xboole_0(A_353,B_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2443,plain,(
    ! [B_16,A_15] : r1_xboole_0(B_16,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_20,c_2440])).

tff(c_2449,plain,(
    ! [A_356,B_357] :
      ( k2_xboole_0(A_356,B_357) = B_357
      | ~ r1_tarski(A_356,B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2461,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2449])).

tff(c_2533,plain,(
    ! [A_371,B_372,C_373] :
      ( r1_xboole_0(A_371,B_372)
      | ~ r1_xboole_0(A_371,k2_xboole_0(B_372,C_373)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2600,plain,(
    ! [A_380] :
      ( r1_xboole_0(A_380,'#skF_2')
      | ~ r1_xboole_0(A_380,k4_xboole_0('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2461,c_2533])).

tff(c_2614,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_2443,c_2600])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2617,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_2614,c_8])).

tff(c_2621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2438,c_2617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:10:17 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.83  
% 4.68/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.68/1.83  
% 4.68/1.83  %Foreground sorts:
% 4.68/1.83  
% 4.68/1.83  
% 4.68/1.83  %Background operators:
% 4.68/1.83  
% 4.68/1.83  
% 4.68/1.83  %Foreground operators:
% 4.68/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.83  
% 4.68/1.85  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.68/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.68/1.85  tff(f_42, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.68/1.85  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.68/1.85  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.68/1.85  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.68/1.85  tff(f_58, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.68/1.85  tff(c_22, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.85  tff(c_27, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_22])).
% 4.68/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.85  tff(c_170, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.85  tff(c_175, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_170])).
% 4.68/1.85  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.85  tff(c_24, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.85  tff(c_181, plain, (![C_60, B_61, A_62]: (r2_hidden(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.85  tff(c_418, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_181])).
% 4.68/1.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.85  tff(c_819, plain, (![A_152, B_153, B_154, B_155]: (r2_hidden('#skF_1'(A_152, B_153), B_154) | ~r1_tarski(B_155, B_154) | ~r1_tarski(A_152, B_155) | r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_418, c_2])).
% 4.68/1.85  tff(c_866, plain, (![A_164, B_165]: (r2_hidden('#skF_1'(A_164, B_165), k4_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(A_164, '#skF_2') | r1_tarski(A_164, B_165))), inference(resolution, [status(thm)], [c_24, c_819])).
% 4.68/1.85  tff(c_963, plain, (![A_181, B_182, B_183]: (r2_hidden('#skF_1'(A_181, B_182), B_183) | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_183) | ~r1_tarski(A_181, '#skF_2') | r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_866, c_2])).
% 4.68/1.85  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.85  tff(c_2412, plain, (![B_349, A_350]: (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_349) | ~r1_tarski(A_350, '#skF_2') | r1_tarski(A_350, B_349))), inference(resolution, [status(thm)], [c_963, c_4])).
% 4.68/1.85  tff(c_2425, plain, (![A_351]: (~r1_tarski(A_351, '#skF_2') | r1_tarski(A_351, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_2412])).
% 4.68/1.85  tff(c_2429, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_175, c_2425])).
% 4.68/1.85  tff(c_2437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_2429])).
% 4.68/1.85  tff(c_2438, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 4.68/1.85  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.68/1.85  tff(c_2440, plain, (![B_352, A_353]: (r1_xboole_0(B_352, A_353) | ~r1_xboole_0(A_353, B_352))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.85  tff(c_2443, plain, (![B_16, A_15]: (r1_xboole_0(B_16, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_20, c_2440])).
% 4.68/1.85  tff(c_2449, plain, (![A_356, B_357]: (k2_xboole_0(A_356, B_357)=B_357 | ~r1_tarski(A_356, B_357))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.68/1.85  tff(c_2461, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_2449])).
% 4.68/1.85  tff(c_2533, plain, (![A_371, B_372, C_373]: (r1_xboole_0(A_371, B_372) | ~r1_xboole_0(A_371, k2_xboole_0(B_372, C_373)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.85  tff(c_2600, plain, (![A_380]: (r1_xboole_0(A_380, '#skF_2') | ~r1_xboole_0(A_380, k4_xboole_0('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2461, c_2533])).
% 4.68/1.85  tff(c_2614, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_2443, c_2600])).
% 4.68/1.85  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.85  tff(c_2617, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_2614, c_8])).
% 4.68/1.85  tff(c_2621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2438, c_2617])).
% 4.68/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.85  
% 4.68/1.85  Inference rules
% 4.68/1.85  ----------------------
% 4.68/1.85  #Ref     : 0
% 4.68/1.85  #Sup     : 607
% 4.68/1.85  #Fact    : 0
% 4.68/1.85  #Define  : 0
% 4.68/1.85  #Split   : 3
% 4.68/1.85  #Chain   : 0
% 4.68/1.85  #Close   : 0
% 4.68/1.85  
% 4.68/1.85  Ordering : KBO
% 4.68/1.85  
% 4.68/1.85  Simplification rules
% 4.68/1.85  ----------------------
% 4.68/1.85  #Subsume      : 41
% 4.68/1.85  #Demod        : 253
% 4.68/1.85  #Tautology    : 284
% 4.68/1.85  #SimpNegUnit  : 2
% 4.68/1.85  #BackRed      : 0
% 4.68/1.85  
% 4.68/1.85  #Partial instantiations: 0
% 4.68/1.85  #Strategies tried      : 1
% 4.68/1.85  
% 4.68/1.85  Timing (in seconds)
% 4.68/1.85  ----------------------
% 4.68/1.85  Preprocessing        : 0.27
% 4.68/1.85  Parsing              : 0.15
% 4.68/1.85  CNF conversion       : 0.02
% 4.68/1.85  Main loop            : 0.83
% 4.68/1.85  Inferencing          : 0.27
% 4.68/1.85  Reduction            : 0.29
% 4.68/1.85  Demodulation         : 0.23
% 4.68/1.85  BG Simplification    : 0.02
% 4.68/1.85  Subsumption          : 0.19
% 4.68/1.85  Abstraction          : 0.02
% 4.68/1.85  MUC search           : 0.00
% 4.68/1.85  Cooper               : 0.00
% 4.68/1.85  Total                : 1.12
% 4.68/1.85  Index Insertion      : 0.00
% 4.68/1.85  Index Deletion       : 0.00
% 4.68/1.85  Index Matching       : 0.00
% 4.68/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
