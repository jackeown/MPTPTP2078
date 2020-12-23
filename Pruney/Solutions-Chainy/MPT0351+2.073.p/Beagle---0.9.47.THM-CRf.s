%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_14,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_22])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [C_38,A_39,B_40] :
      ( r2_hidden(C_38,A_39)
      | ~ r2_hidden(C_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_44,B_45,A_46] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_46)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_46))
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_50,A_51] :
      ( ~ m1_subset_1(A_50,k1_zfmisc_1(A_51))
      | r1_tarski(A_50,A_51) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_125,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_125,c_10])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_109,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_subset_1(A_47,B_48,C_49) = k2_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [A_53,B_54] :
      ( k4_subset_1(A_53,B_54,A_53) = k2_xboole_0(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_25,c_109])).

tff(c_157,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_161,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_157])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.36  
% 1.99/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.36  
% 1.99/1.36  %Foreground sorts:
% 1.99/1.36  
% 1.99/1.36  
% 1.99/1.36  %Background operators:
% 1.99/1.36  
% 1.99/1.36  
% 1.99/1.36  %Foreground operators:
% 1.99/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.36  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 1.99/1.36  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.36  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.99/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.36  
% 1.99/1.37  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.99/1.37  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 1.99/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.99/1.37  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.99/1.37  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.99/1.37  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.99/1.37  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.99/1.37  tff(c_14, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.37  tff(c_22, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.37  tff(c_26, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_22])).
% 1.99/1.37  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.37  tff(c_81, plain, (![C_38, A_39, B_40]: (r2_hidden(C_38, A_39) | ~r2_hidden(C_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.37  tff(c_97, plain, (![A_44, B_45, A_46]: (r2_hidden('#skF_1'(A_44, B_45), A_46) | ~m1_subset_1(A_44, k1_zfmisc_1(A_46)) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_6, c_81])).
% 1.99/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.37  tff(c_116, plain, (![A_50, A_51]: (~m1_subset_1(A_50, k1_zfmisc_1(A_51)) | r1_tarski(A_50, A_51))), inference(resolution, [status(thm)], [c_97, c_4])).
% 1.99/1.37  tff(c_125, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_116])).
% 1.99/1.37  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.37  tff(c_129, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_125, c_10])).
% 1.99/1.37  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.37  tff(c_25, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 1.99/1.37  tff(c_109, plain, (![A_47, B_48, C_49]: (k4_subset_1(A_47, B_48, C_49)=k2_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.37  tff(c_153, plain, (![A_53, B_54]: (k4_subset_1(A_53, B_54, A_53)=k2_xboole_0(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_25, c_109])).
% 1.99/1.37  tff(c_157, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_153])).
% 1.99/1.37  tff(c_161, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_157])).
% 1.99/1.37  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_161])).
% 1.99/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.37  
% 1.99/1.37  Inference rules
% 1.99/1.37  ----------------------
% 1.99/1.37  #Ref     : 0
% 1.99/1.37  #Sup     : 33
% 1.99/1.37  #Fact    : 0
% 1.99/1.37  #Define  : 0
% 1.99/1.37  #Split   : 0
% 1.99/1.37  #Chain   : 0
% 1.99/1.37  #Close   : 0
% 1.99/1.37  
% 1.99/1.37  Ordering : KBO
% 1.99/1.37  
% 1.99/1.37  Simplification rules
% 1.99/1.37  ----------------------
% 1.99/1.37  #Subsume      : 0
% 1.99/1.37  #Demod        : 7
% 1.99/1.37  #Tautology    : 16
% 1.99/1.37  #SimpNegUnit  : 1
% 1.99/1.37  #BackRed      : 0
% 1.99/1.37  
% 1.99/1.37  #Partial instantiations: 0
% 1.99/1.37  #Strategies tried      : 1
% 1.99/1.37  
% 1.99/1.37  Timing (in seconds)
% 1.99/1.37  ----------------------
% 1.99/1.37  Preprocessing        : 0.34
% 1.99/1.37  Parsing              : 0.17
% 1.99/1.37  CNF conversion       : 0.02
% 1.99/1.37  Main loop            : 0.15
% 1.99/1.37  Inferencing          : 0.06
% 1.99/1.37  Reduction            : 0.04
% 1.99/1.37  Demodulation         : 0.03
% 1.99/1.37  BG Simplification    : 0.01
% 1.99/1.37  Subsumption          : 0.03
% 1.99/1.37  Abstraction          : 0.01
% 1.99/1.37  MUC search           : 0.00
% 1.99/1.37  Cooper               : 0.00
% 1.99/1.37  Total                : 0.52
% 2.14/1.37  Index Insertion      : 0.00
% 2.14/1.37  Index Deletion       : 0.00
% 2.14/1.37  Index Matching       : 0.00
% 2.14/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
