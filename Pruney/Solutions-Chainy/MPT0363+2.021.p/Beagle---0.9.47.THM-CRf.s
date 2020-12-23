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
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 ( 104 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_225,plain,(
    ! [A_65] :
      ( r1_xboole_0(A_65,'#skF_4')
      | ~ r1_tarski(A_65,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_244,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_244])).

tff(c_256,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_322,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_329,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_322])).

tff(c_387,plain,(
    ! [A_101,B_102,C_103] :
      ( r1_tarski(A_101,k4_xboole_0(B_102,C_103))
      | ~ r1_xboole_0(A_101,C_103)
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_518,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,k3_subset_1('#skF_2','#skF_4'))
      | ~ r1_xboole_0(A_123,'#skF_4')
      | ~ r1_tarski(A_123,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_387])).

tff(c_255,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_527,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_518,c_255])).

tff(c_532,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_527])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_306,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_533,plain,(
    ! [A_124,B_125,A_126] :
      ( r2_hidden('#skF_1'(A_124,B_125),A_126)
      | ~ m1_subset_1(A_124,k1_zfmisc_1(A_126))
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_306])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_545,plain,(
    ! [A_127,A_128] :
      ( ~ m1_subset_1(A_127,k1_zfmisc_1(A_128))
      | r1_tarski(A_127,A_128) ) ),
    inference(resolution,[status(thm)],[c_533,c_4])).

tff(c_551,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_545])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.46/1.41  
% 2.46/1.41  %Foreground sorts:
% 2.46/1.41  
% 2.46/1.41  
% 2.46/1.41  %Background operators:
% 2.46/1.41  
% 2.46/1.41  
% 2.46/1.41  %Foreground operators:
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.46/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.46/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.41  
% 2.46/1.42  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.46/1.42  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.46/1.42  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.46/1.42  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.46/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.46/1.42  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.46/1.42  tff(c_22, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.42  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.46/1.42  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.42  tff(c_32, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_28])).
% 2.46/1.42  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.42  tff(c_95, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.42  tff(c_102, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_95])).
% 2.46/1.42  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.42  tff(c_225, plain, (![A_65]: (r1_xboole_0(A_65, '#skF_4') | ~r1_tarski(A_65, k3_subset_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 2.46/1.42  tff(c_244, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_225])).
% 2.46/1.42  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_244])).
% 2.46/1.42  tff(c_256, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 2.46/1.42  tff(c_322, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.42  tff(c_329, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_322])).
% 2.46/1.42  tff(c_387, plain, (![A_101, B_102, C_103]: (r1_tarski(A_101, k4_xboole_0(B_102, C_103)) | ~r1_xboole_0(A_101, C_103) | ~r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.42  tff(c_518, plain, (![A_123]: (r1_tarski(A_123, k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0(A_123, '#skF_4') | ~r1_tarski(A_123, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_329, c_387])).
% 2.46/1.42  tff(c_255, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 2.46/1.42  tff(c_527, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_518, c_255])).
% 2.46/1.42  tff(c_532, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_527])).
% 2.46/1.42  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.46/1.42  tff(c_306, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, A_89) | ~r2_hidden(C_88, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.42  tff(c_533, plain, (![A_124, B_125, A_126]: (r2_hidden('#skF_1'(A_124, B_125), A_126) | ~m1_subset_1(A_124, k1_zfmisc_1(A_126)) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_6, c_306])).
% 2.46/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.46/1.42  tff(c_545, plain, (![A_127, A_128]: (~m1_subset_1(A_127, k1_zfmisc_1(A_128)) | r1_tarski(A_127, A_128))), inference(resolution, [status(thm)], [c_533, c_4])).
% 2.46/1.42  tff(c_551, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_545])).
% 2.46/1.42  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_551])).
% 2.46/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.42  
% 2.46/1.42  Inference rules
% 2.46/1.42  ----------------------
% 2.46/1.42  #Ref     : 0
% 2.46/1.42  #Sup     : 114
% 2.46/1.42  #Fact    : 0
% 2.46/1.42  #Define  : 0
% 2.46/1.42  #Split   : 1
% 2.46/1.42  #Chain   : 0
% 2.46/1.42  #Close   : 0
% 2.46/1.42  
% 2.46/1.42  Ordering : KBO
% 2.46/1.42  
% 2.46/1.42  Simplification rules
% 2.46/1.42  ----------------------
% 2.46/1.42  #Subsume      : 0
% 2.46/1.42  #Demod        : 20
% 2.46/1.42  #Tautology    : 36
% 2.46/1.42  #SimpNegUnit  : 4
% 2.46/1.42  #BackRed      : 0
% 2.46/1.42  
% 2.46/1.42  #Partial instantiations: 0
% 2.46/1.42  #Strategies tried      : 1
% 2.46/1.42  
% 2.46/1.42  Timing (in seconds)
% 2.46/1.42  ----------------------
% 2.46/1.43  Preprocessing        : 0.30
% 2.46/1.43  Parsing              : 0.17
% 2.46/1.43  CNF conversion       : 0.02
% 2.46/1.43  Main loop            : 0.31
% 2.46/1.43  Inferencing          : 0.12
% 2.46/1.43  Reduction            : 0.09
% 2.46/1.43  Demodulation         : 0.06
% 2.46/1.43  BG Simplification    : 0.02
% 2.46/1.43  Subsumption          : 0.05
% 2.46/1.43  Abstraction          : 0.01
% 2.46/1.43  MUC search           : 0.00
% 2.46/1.43  Cooper               : 0.00
% 2.46/1.43  Total                : 0.64
% 2.46/1.43  Index Insertion      : 0.00
% 2.46/1.43  Index Deletion       : 0.00
% 2.46/1.43  Index Matching       : 0.00
% 2.46/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
