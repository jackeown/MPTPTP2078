%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   19 (  27 expanded)
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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | k4_xboole_0(A_26,k1_tarski(B_25)) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [B_25] : ~ r2_hidden(B_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_151,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_54),C_54)
      | r2_hidden(k3_subset_1(A_52,'#skF_1'(A_52,B_53,C_54)),B_53)
      | k7_setfam_1(A_52,B_53) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_zfmisc_1(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_171,plain,(
    ! [A_52,C_54] :
      ( r2_hidden('#skF_1'(A_52,k1_xboole_0,C_54),C_54)
      | k7_setfam_1(A_52,k1_xboole_0) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_zfmisc_1(A_52)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(resolution,[status(thm)],[c_151,c_73])).

tff(c_179,plain,(
    ! [A_55,C_56] :
      ( r2_hidden('#skF_1'(A_55,k1_xboole_0,C_56),C_56)
      | k7_setfam_1(A_55,k1_xboole_0) = C_56
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_187,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_1'(A_55,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_55,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_197,plain,(
    ! [A_57] : k7_setfam_1(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_187])).

tff(c_28,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_34,B_35] :
      ( k7_setfam_1(A_34,k7_setfam_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_94,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_89])).

tff(c_203,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_94])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:22 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.20  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.93/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.20  
% 2.02/1.21  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.02/1.21  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.02/1.21  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.02/1.21  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.02/1.21  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.02/1.21  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.02/1.21  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.21  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.21  tff(c_64, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | k4_xboole_0(A_26, k1_tarski(B_25))!=A_26)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.21  tff(c_73, plain, (![B_25]: (~r2_hidden(B_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.02/1.21  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.21  tff(c_151, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_1'(A_52, B_53, C_54), C_54) | r2_hidden(k3_subset_1(A_52, '#skF_1'(A_52, B_53, C_54)), B_53) | k7_setfam_1(A_52, B_53)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k1_zfmisc_1(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.21  tff(c_171, plain, (![A_52, C_54]: (r2_hidden('#skF_1'(A_52, k1_xboole_0, C_54), C_54) | k7_setfam_1(A_52, k1_xboole_0)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k1_zfmisc_1(A_52))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(resolution, [status(thm)], [c_151, c_73])).
% 2.02/1.21  tff(c_179, plain, (![A_55, C_56]: (r2_hidden('#skF_1'(A_55, k1_xboole_0, C_56), C_56) | k7_setfam_1(A_55, k1_xboole_0)=C_56 | ~m1_subset_1(C_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_171])).
% 2.02/1.21  tff(c_187, plain, (![A_55]: (r2_hidden('#skF_1'(A_55, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_55, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_179])).
% 2.02/1.21  tff(c_197, plain, (![A_57]: (k7_setfam_1(A_57, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_73, c_187])).
% 2.02/1.21  tff(c_28, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.21  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.21  tff(c_87, plain, (![A_34, B_35]: (k7_setfam_1(A_34, k7_setfam_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.21  tff(c_89, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_87])).
% 2.02/1.21  tff(c_94, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_89])).
% 2.02/1.21  tff(c_203, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_197, c_94])).
% 2.02/1.21  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_203])).
% 2.02/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  Inference rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Ref     : 0
% 2.02/1.21  #Sup     : 41
% 2.02/1.21  #Fact    : 0
% 2.02/1.21  #Define  : 0
% 2.02/1.21  #Split   : 0
% 2.02/1.21  #Chain   : 0
% 2.02/1.21  #Close   : 0
% 2.02/1.21  
% 2.02/1.21  Ordering : KBO
% 2.02/1.21  
% 2.02/1.21  Simplification rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Subsume      : 9
% 2.02/1.21  #Demod        : 18
% 2.02/1.21  #Tautology    : 19
% 2.02/1.21  #SimpNegUnit  : 5
% 2.02/1.21  #BackRed      : 1
% 2.02/1.21  
% 2.02/1.21  #Partial instantiations: 0
% 2.02/1.21  #Strategies tried      : 1
% 2.02/1.21  
% 2.02/1.21  Timing (in seconds)
% 2.02/1.21  ----------------------
% 2.02/1.21  Preprocessing        : 0.30
% 2.02/1.21  Parsing              : 0.16
% 2.02/1.21  CNF conversion       : 0.02
% 2.02/1.21  Main loop            : 0.17
% 2.02/1.21  Inferencing          : 0.06
% 2.02/1.22  Reduction            : 0.05
% 2.02/1.22  Demodulation         : 0.04
% 2.02/1.22  BG Simplification    : 0.01
% 2.02/1.22  Subsumption          : 0.03
% 2.02/1.22  Abstraction          : 0.01
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.49
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
