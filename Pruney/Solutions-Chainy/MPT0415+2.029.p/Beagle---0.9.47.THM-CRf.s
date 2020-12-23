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
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_1'(A_54,B_55,C_56),C_56)
      | r2_hidden(k3_subset_1(A_54,'#skF_1'(A_54,B_55,C_56)),B_55)
      | k7_setfam_1(A_54,B_55) = C_56
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,(
    ! [A_54,C_56] :
      ( r2_hidden('#skF_1'(A_54,k1_xboole_0,C_56),C_56)
      | k7_setfam_1(A_54,k1_xboole_0) = C_56
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(resolution,[status(thm)],[c_157,c_65])).

tff(c_189,plain,(
    ! [A_60,C_61] :
      ( r2_hidden('#skF_1'(A_60,k1_xboole_0,C_61),C_61)
      | k7_setfam_1(A_60,k1_xboole_0) = C_61
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_197,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_1'(A_60,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_60,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_207,plain,(
    ! [A_62] : k7_setfam_1(A_62,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_197])).

tff(c_30,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    ! [A_36,B_37] :
      ( k7_setfam_1(A_36,k7_setfam_1(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_95,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_100,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_95])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_100])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.23  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.00/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.23  
% 2.08/1.24  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.08/1.24  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.24  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.08/1.24  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.24  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.08/1.24  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.08/1.24  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.24  tff(c_62, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.24  tff(c_65, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 2.08/1.24  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.24  tff(c_157, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_1'(A_54, B_55, C_56), C_56) | r2_hidden(k3_subset_1(A_54, '#skF_1'(A_54, B_55, C_56)), B_55) | k7_setfam_1(A_54, B_55)=C_56 | ~m1_subset_1(C_56, k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.24  tff(c_177, plain, (![A_54, C_56]: (r2_hidden('#skF_1'(A_54, k1_xboole_0, C_56), C_56) | k7_setfam_1(A_54, k1_xboole_0)=C_56 | ~m1_subset_1(C_56, k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(resolution, [status(thm)], [c_157, c_65])).
% 2.08/1.24  tff(c_189, plain, (![A_60, C_61]: (r2_hidden('#skF_1'(A_60, k1_xboole_0, C_61), C_61) | k7_setfam_1(A_60, k1_xboole_0)=C_61 | ~m1_subset_1(C_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_177])).
% 2.08/1.24  tff(c_197, plain, (![A_60]: (r2_hidden('#skF_1'(A_60, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_189])).
% 2.08/1.24  tff(c_207, plain, (![A_62]: (k7_setfam_1(A_62, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_65, c_197])).
% 2.08/1.24  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_93, plain, (![A_36, B_37]: (k7_setfam_1(A_36, k7_setfam_1(A_36, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.24  tff(c_95, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_93])).
% 2.08/1.24  tff(c_100, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_95])).
% 2.08/1.24  tff(c_213, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_207, c_100])).
% 2.08/1.24  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_213])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 44
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 0
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 10
% 2.08/1.24  #Demod        : 18
% 2.08/1.24  #Tautology    : 21
% 2.08/1.24  #SimpNegUnit  : 5
% 2.08/1.24  #BackRed      : 1
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.25  Preprocessing        : 0.30
% 2.08/1.25  Parsing              : 0.16
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.18
% 2.08/1.25  Inferencing          : 0.07
% 2.08/1.25  Reduction            : 0.05
% 2.08/1.25  Demodulation         : 0.04
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.04
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.51
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
