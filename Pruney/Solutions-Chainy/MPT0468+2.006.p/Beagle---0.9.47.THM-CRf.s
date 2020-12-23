%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  46 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [C_48,A_49] :
      ( r2_hidden(k4_tarski(C_48,'#skF_5'(A_49,k1_relat_1(A_49),C_48)),A_49)
      | ~ r2_hidden(C_48,k1_relat_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [B_30,C_31] : ~ r2_hidden(k4_tarski(B_30,C_31),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_113,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_103,c_34])).

tff(c_123,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_30,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,k2_zfmisc_1(k1_relat_1(A_27),k2_relat_1(A_27)))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_6')))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_30])).

tff(c_138,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16,c_132])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_138,c_73])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.52  
% 2.28/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.52  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.28/1.52  
% 2.28/1.52  %Foreground sorts:
% 2.28/1.52  
% 2.28/1.52  
% 2.28/1.52  %Background operators:
% 2.28/1.52  
% 2.28/1.52  
% 2.28/1.52  %Foreground operators:
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.28/1.52  
% 2.31/1.54  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 2.31/1.54  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.31/1.54  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.31/1.54  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.31/1.54  tff(f_59, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.31/1.54  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.31/1.54  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.54  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.31/1.54  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.31/1.54  tff(c_16, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.54  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.54  tff(c_103, plain, (![C_48, A_49]: (r2_hidden(k4_tarski(C_48, '#skF_5'(A_49, k1_relat_1(A_49), C_48)), A_49) | ~r2_hidden(C_48, k1_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.54  tff(c_34, plain, (![B_30, C_31]: (~r2_hidden(k4_tarski(B_30, C_31), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.31/1.54  tff(c_113, plain, (![C_50]: (~r2_hidden(C_50, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_103, c_34])).
% 2.31/1.54  tff(c_123, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.31/1.54  tff(c_30, plain, (![A_27]: (r1_tarski(A_27, k2_zfmisc_1(k1_relat_1(A_27), k2_relat_1(A_27))) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.54  tff(c_132, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_6'))) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_123, c_30])).
% 2.31/1.54  tff(c_138, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16, c_132])).
% 2.31/1.54  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.54  tff(c_64, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.54  tff(c_73, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_64])).
% 2.31/1.54  tff(c_154, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_138, c_73])).
% 2.31/1.54  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_154])).
% 2.31/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.54  
% 2.31/1.54  Inference rules
% 2.31/1.54  ----------------------
% 2.31/1.54  #Ref     : 0
% 2.31/1.54  #Sup     : 25
% 2.31/1.54  #Fact    : 0
% 2.31/1.54  #Define  : 0
% 2.31/1.54  #Split   : 0
% 2.31/1.54  #Chain   : 0
% 2.31/1.54  #Close   : 0
% 2.31/1.54  
% 2.31/1.54  Ordering : KBO
% 2.31/1.54  
% 2.31/1.54  Simplification rules
% 2.31/1.54  ----------------------
% 2.31/1.54  #Subsume      : 0
% 2.31/1.54  #Demod        : 6
% 2.31/1.54  #Tautology    : 16
% 2.31/1.54  #SimpNegUnit  : 2
% 2.31/1.54  #BackRed      : 1
% 2.31/1.54  
% 2.31/1.54  #Partial instantiations: 0
% 2.31/1.54  #Strategies tried      : 1
% 2.31/1.54  
% 2.31/1.54  Timing (in seconds)
% 2.31/1.54  ----------------------
% 2.31/1.54  Preprocessing        : 0.49
% 2.31/1.54  Parsing              : 0.25
% 2.31/1.54  CNF conversion       : 0.04
% 2.31/1.54  Main loop            : 0.21
% 2.31/1.54  Inferencing          : 0.07
% 2.31/1.54  Reduction            : 0.07
% 2.31/1.54  Demodulation         : 0.05
% 2.31/1.54  BG Simplification    : 0.02
% 2.31/1.54  Subsumption          : 0.03
% 2.31/1.54  Abstraction          : 0.01
% 2.31/1.54  MUC search           : 0.00
% 2.31/1.54  Cooper               : 0.00
% 2.31/1.54  Total                : 0.74
% 2.31/1.54  Index Insertion      : 0.00
% 2.31/1.54  Index Deletion       : 0.00
% 2.31/1.54  Index Matching       : 0.00
% 2.31/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
