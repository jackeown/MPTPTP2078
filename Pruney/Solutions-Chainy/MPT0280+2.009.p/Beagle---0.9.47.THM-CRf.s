%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  89 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_zfmisc_1(A_41),k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k5_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_167,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(k5_xboole_0(A_72,C_73),B_74)
      | ~ r1_tarski(C_73,B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_533,plain,(
    ! [A_124,B_125,B_126] :
      ( r1_tarski(k2_xboole_0(A_124,B_125),B_126)
      | ~ r1_tarski(k3_xboole_0(A_124,B_125),B_126)
      | ~ r1_tarski(k5_xboole_0(A_124,B_125),B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_167])).

tff(c_1229,plain,(
    ! [A_153,C_154,B_155] :
      ( r1_tarski(k2_xboole_0(A_153,C_154),B_155)
      | ~ r1_tarski(k3_xboole_0(A_153,C_154),B_155)
      | ~ r1_tarski(C_154,B_155)
      | ~ r1_tarski(A_153,B_155) ) ),
    inference(resolution,[status(thm)],[c_12,c_533])).

tff(c_1249,plain,(
    ! [A_156,C_157,B_158] :
      ( r1_tarski(k2_xboole_0(A_156,C_157),B_158)
      | ~ r1_tarski(C_157,B_158)
      | ~ r1_tarski(A_156,B_158) ) ),
    inference(resolution,[status(thm)],[c_8,c_1229])).

tff(c_34,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1309,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1249,c_34])).

tff(c_1958,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_1964,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_1958])).

tff(c_1970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1964])).

tff(c_1971,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_1979,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_1971])).

tff(c_1985,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1979])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  
% 3.93/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.93/1.66  
% 3.93/1.66  %Foreground sorts:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Background operators:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Foreground operators:
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.93/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.93/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.93/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.93/1.66  
% 3.93/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.93/1.67  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.93/1.67  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.93/1.67  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.93/1.67  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.93/1.67  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 3.93/1.67  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.93/1.67  tff(f_70, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 3.93/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.67  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.93/1.67  tff(c_32, plain, (![A_41, B_42]: (r1_tarski(k1_zfmisc_1(A_41), k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.93/1.67  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.93/1.67  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.93/1.67  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(k5_xboole_0(A_9, C_11), B_10) | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.93/1.67  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.93/1.67  tff(c_167, plain, (![A_72, C_73, B_74]: (r1_tarski(k5_xboole_0(A_72, C_73), B_74) | ~r1_tarski(C_73, B_74) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.93/1.67  tff(c_533, plain, (![A_124, B_125, B_126]: (r1_tarski(k2_xboole_0(A_124, B_125), B_126) | ~r1_tarski(k3_xboole_0(A_124, B_125), B_126) | ~r1_tarski(k5_xboole_0(A_124, B_125), B_126))), inference(superposition, [status(thm), theory('equality')], [c_18, c_167])).
% 3.93/1.67  tff(c_1229, plain, (![A_153, C_154, B_155]: (r1_tarski(k2_xboole_0(A_153, C_154), B_155) | ~r1_tarski(k3_xboole_0(A_153, C_154), B_155) | ~r1_tarski(C_154, B_155) | ~r1_tarski(A_153, B_155))), inference(resolution, [status(thm)], [c_12, c_533])).
% 3.93/1.67  tff(c_1249, plain, (![A_156, C_157, B_158]: (r1_tarski(k2_xboole_0(A_156, C_157), B_158) | ~r1_tarski(C_157, B_158) | ~r1_tarski(A_156, B_158))), inference(resolution, [status(thm)], [c_8, c_1229])).
% 3.93/1.67  tff(c_34, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.67  tff(c_1309, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1249, c_34])).
% 3.93/1.67  tff(c_1958, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1309])).
% 3.93/1.67  tff(c_1964, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_1958])).
% 3.93/1.67  tff(c_1970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1964])).
% 3.93/1.67  tff(c_1971, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1309])).
% 3.93/1.67  tff(c_1979, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_1971])).
% 3.93/1.67  tff(c_1985, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_1979])).
% 3.93/1.67  tff(c_1990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1985])).
% 3.93/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.67  
% 3.93/1.67  Inference rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Ref     : 0
% 3.93/1.67  #Sup     : 474
% 3.93/1.67  #Fact    : 0
% 3.93/1.67  #Define  : 0
% 3.93/1.67  #Split   : 2
% 3.93/1.67  #Chain   : 0
% 3.93/1.67  #Close   : 0
% 3.93/1.67  
% 3.93/1.67  Ordering : KBO
% 3.93/1.67  
% 3.93/1.67  Simplification rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Subsume      : 17
% 3.93/1.67  #Demod        : 347
% 3.93/1.67  #Tautology    : 129
% 3.93/1.67  #SimpNegUnit  : 0
% 3.93/1.67  #BackRed      : 1
% 3.93/1.67  
% 3.93/1.67  #Partial instantiations: 0
% 3.93/1.67  #Strategies tried      : 1
% 3.93/1.67  
% 3.93/1.67  Timing (in seconds)
% 3.93/1.67  ----------------------
% 4.05/1.68  Preprocessing        : 0.31
% 4.05/1.68  Parsing              : 0.17
% 4.05/1.68  CNF conversion       : 0.02
% 4.05/1.68  Main loop            : 0.61
% 4.05/1.68  Inferencing          : 0.21
% 4.05/1.68  Reduction            : 0.21
% 4.05/1.68  Demodulation         : 0.17
% 4.05/1.68  BG Simplification    : 0.03
% 4.05/1.68  Subsumption          : 0.12
% 4.05/1.68  Abstraction          : 0.05
% 4.05/1.68  MUC search           : 0.00
% 4.05/1.68  Cooper               : 0.00
% 4.05/1.68  Total                : 0.94
% 4.05/1.68  Index Insertion      : 0.00
% 4.05/1.68  Index Deletion       : 0.00
% 4.05/1.68  Index Matching       : 0.00
% 4.05/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
