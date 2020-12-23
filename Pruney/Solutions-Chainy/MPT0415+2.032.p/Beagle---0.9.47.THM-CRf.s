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
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [C_24,B_25] : ~ r2_hidden(C_24,k4_xboole_0(B_25,k1_tarski(C_24))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_1'(A_63,B_64,C_65),C_65)
      | r2_hidden(k3_subset_1(A_63,'#skF_1'(A_63,B_64,C_65)),B_64)
      | k7_setfam_1(A_63,B_64) = C_65
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_zfmisc_1(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_196,plain,(
    ! [A_63,C_65] :
      ( r2_hidden('#skF_1'(A_63,k1_xboole_0,C_65),C_65)
      | k7_setfam_1(A_63,k1_xboole_0) = C_65
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_zfmisc_1(A_63)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(resolution,[status(thm)],[c_166,c_50])).

tff(c_207,plain,(
    ! [A_66,C_67] :
      ( r2_hidden('#skF_1'(A_66,k1_xboole_0,C_67),C_67)
      | k7_setfam_1(A_66,k1_xboole_0) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_196])).

tff(c_215,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_1'(A_66,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_66,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_207])).

tff(c_225,plain,(
    ! [A_68] : k7_setfam_1(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_215])).

tff(c_30,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    ! [A_39,B_40] :
      ( k7_setfam_1(A_39,k7_setfam_1(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_96,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_231,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_96])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.16/1.33  
% 2.16/1.33  %Foreground sorts:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Background operators:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Foreground operators:
% 2.16/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.33  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.16/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.16/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.33  
% 2.16/1.34  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.16/1.34  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.16/1.34  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.16/1.34  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.16/1.34  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.16/1.34  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.16/1.34  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.16/1.34  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.34  tff(c_47, plain, (![C_24, B_25]: (~r2_hidden(C_24, k4_xboole_0(B_25, k1_tarski(C_24))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.34  tff(c_50, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_47])).
% 2.16/1.34  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.34  tff(c_166, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_1'(A_63, B_64, C_65), C_65) | r2_hidden(k3_subset_1(A_63, '#skF_1'(A_63, B_64, C_65)), B_64) | k7_setfam_1(A_63, B_64)=C_65 | ~m1_subset_1(C_65, k1_zfmisc_1(k1_zfmisc_1(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.34  tff(c_196, plain, (![A_63, C_65]: (r2_hidden('#skF_1'(A_63, k1_xboole_0, C_65), C_65) | k7_setfam_1(A_63, k1_xboole_0)=C_65 | ~m1_subset_1(C_65, k1_zfmisc_1(k1_zfmisc_1(A_63))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(resolution, [status(thm)], [c_166, c_50])).
% 2.16/1.34  tff(c_207, plain, (![A_66, C_67]: (r2_hidden('#skF_1'(A_66, k1_xboole_0, C_67), C_67) | k7_setfam_1(A_66, k1_xboole_0)=C_67 | ~m1_subset_1(C_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_196])).
% 2.16/1.34  tff(c_215, plain, (![A_66]: (r2_hidden('#skF_1'(A_66, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_66, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_207])).
% 2.16/1.34  tff(c_225, plain, (![A_68]: (k7_setfam_1(A_68, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_215])).
% 2.16/1.34  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.16/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.16/1.34  tff(c_89, plain, (![A_39, B_40]: (k7_setfam_1(A_39, k7_setfam_1(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.34  tff(c_91, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_89])).
% 2.16/1.34  tff(c_96, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_91])).
% 2.16/1.34  tff(c_231, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_225, c_96])).
% 2.16/1.34  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_231])).
% 2.16/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.34  
% 2.16/1.34  Inference rules
% 2.16/1.34  ----------------------
% 2.16/1.34  #Ref     : 0
% 2.16/1.34  #Sup     : 47
% 2.16/1.34  #Fact    : 0
% 2.16/1.34  #Define  : 0
% 2.16/1.34  #Split   : 0
% 2.16/1.34  #Chain   : 0
% 2.16/1.34  #Close   : 0
% 2.16/1.34  
% 2.16/1.34  Ordering : KBO
% 2.16/1.34  
% 2.16/1.34  Simplification rules
% 2.16/1.34  ----------------------
% 2.16/1.34  #Subsume      : 13
% 2.16/1.34  #Demod        : 18
% 2.16/1.34  #Tautology    : 17
% 2.16/1.34  #SimpNegUnit  : 7
% 2.16/1.34  #BackRed      : 1
% 2.16/1.34  
% 2.16/1.34  #Partial instantiations: 0
% 2.16/1.34  #Strategies tried      : 1
% 2.16/1.34  
% 2.16/1.34  Timing (in seconds)
% 2.16/1.34  ----------------------
% 2.16/1.34  Preprocessing        : 0.33
% 2.16/1.34  Parsing              : 0.17
% 2.16/1.34  CNF conversion       : 0.02
% 2.16/1.34  Main loop            : 0.19
% 2.16/1.34  Inferencing          : 0.07
% 2.16/1.34  Reduction            : 0.06
% 2.16/1.34  Demodulation         : 0.04
% 2.16/1.34  BG Simplification    : 0.02
% 2.16/1.34  Subsumption          : 0.04
% 2.16/1.34  Abstraction          : 0.01
% 2.16/1.35  MUC search           : 0.00
% 2.16/1.35  Cooper               : 0.00
% 2.16/1.35  Total                : 0.54
% 2.16/1.35  Index Insertion      : 0.00
% 2.16/1.35  Index Deletion       : 0.00
% 2.16/1.35  Index Matching       : 0.00
% 2.16/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
