%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 170 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    ! [B_28,A_29] :
      ( v1_xboole_0(B_28)
      | ~ m1_subset_1(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k2_tarski(A_46,B_47),C_48)
      | ~ r2_hidden(B_47,C_48)
      | ~ r2_hidden(A_46,C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [B_36,A_37] :
      ( m1_subset_1(B_36,A_37)
      | ~ r2_hidden(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_124,plain,(
    ! [C_38,A_39] :
      ( m1_subset_1(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_120])).

tff(c_36,plain,(
    ~ m1_subset_1(k2_tarski('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_132,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_36])).

tff(c_180,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_132])).

tff(c_193,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_196,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_199,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_196])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_199])).

tff(c_202,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_206,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_202])).

tff(c_209,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_206])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_209])).

tff(c_213,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:32:25 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.15  
% 1.94/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.94/1.15  
% 1.94/1.15  %Foreground sorts:
% 1.94/1.15  
% 1.94/1.15  
% 1.94/1.15  %Background operators:
% 1.94/1.15  
% 1.94/1.15  
% 1.94/1.15  %Foreground operators:
% 1.94/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.15  
% 1.94/1.16  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 1.94/1.16  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.94/1.16  tff(f_46, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.94/1.16  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.94/1.16  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.94/1.16  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.17  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.17  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.17  tff(c_89, plain, (![B_28, A_29]: (v1_xboole_0(B_28) | ~m1_subset_1(B_28, A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.17  tff(c_100, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_89])).
% 1.94/1.17  tff(c_102, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_100])).
% 1.94/1.17  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.17  tff(c_28, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.17  tff(c_164, plain, (![A_46, B_47, C_48]: (r1_tarski(k2_tarski(A_46, B_47), C_48) | ~r2_hidden(B_47, C_48) | ~r2_hidden(A_46, C_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.17  tff(c_34, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.17  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.17  tff(c_117, plain, (![B_36, A_37]: (m1_subset_1(B_36, A_37) | ~r2_hidden(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.17  tff(c_120, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_10, c_117])).
% 1.94/1.17  tff(c_124, plain, (![C_38, A_39]: (m1_subset_1(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(negUnitSimplification, [status(thm)], [c_34, c_120])).
% 1.94/1.17  tff(c_36, plain, (~m1_subset_1(k2_tarski('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.17  tff(c_132, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_36])).
% 1.94/1.17  tff(c_180, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_164, c_132])).
% 1.94/1.17  tff(c_193, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_180])).
% 1.94/1.17  tff(c_196, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_193])).
% 1.94/1.17  tff(c_199, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_196])).
% 1.94/1.17  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_199])).
% 1.94/1.17  tff(c_202, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_180])).
% 1.94/1.17  tff(c_206, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_202])).
% 1.94/1.17  tff(c_209, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_206])).
% 1.94/1.17  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_209])).
% 1.94/1.17  tff(c_213, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_100])).
% 1.94/1.17  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.17  tff(c_221, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_213, c_2])).
% 1.94/1.17  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_221])).
% 1.94/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.17  
% 1.94/1.17  Inference rules
% 1.94/1.17  ----------------------
% 1.94/1.17  #Ref     : 0
% 1.94/1.17  #Sup     : 37
% 1.94/1.17  #Fact    : 0
% 1.94/1.17  #Define  : 0
% 1.94/1.17  #Split   : 3
% 1.94/1.17  #Chain   : 0
% 1.94/1.17  #Close   : 0
% 1.94/1.17  
% 1.94/1.17  Ordering : KBO
% 1.94/1.17  
% 1.94/1.17  Simplification rules
% 1.94/1.17  ----------------------
% 1.94/1.17  #Subsume      : 10
% 1.94/1.17  #Demod        : 2
% 1.94/1.17  #Tautology    : 16
% 1.94/1.17  #SimpNegUnit  : 5
% 1.94/1.17  #BackRed      : 0
% 1.94/1.17  
% 1.94/1.17  #Partial instantiations: 0
% 1.94/1.17  #Strategies tried      : 1
% 1.94/1.17  
% 1.94/1.17  Timing (in seconds)
% 1.94/1.17  ----------------------
% 1.94/1.17  Preprocessing        : 0.31
% 1.94/1.17  Parsing              : 0.16
% 1.94/1.17  CNF conversion       : 0.02
% 1.94/1.17  Main loop            : 0.17
% 1.94/1.17  Inferencing          : 0.06
% 1.94/1.17  Reduction            : 0.05
% 1.94/1.17  Demodulation         : 0.03
% 1.94/1.17  BG Simplification    : 0.01
% 1.94/1.17  Subsumption          : 0.03
% 1.94/1.17  Abstraction          : 0.01
% 1.94/1.17  MUC search           : 0.00
% 1.94/1.17  Cooper               : 0.00
% 1.94/1.17  Total                : 0.51
% 1.94/1.17  Index Insertion      : 0.00
% 1.94/1.17  Index Deletion       : 0.00
% 1.94/1.17  Index Matching       : 0.00
% 1.94/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
