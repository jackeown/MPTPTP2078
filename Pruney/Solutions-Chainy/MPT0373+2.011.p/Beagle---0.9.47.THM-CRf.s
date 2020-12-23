%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:58 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  90 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [B_26,A_27] :
      ( v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_24,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [B_28,A_29] :
      ( m1_subset_1(B_28,A_29)
      | ~ r2_hidden(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_94,plain,(
    ! [C_32,A_33] :
      ( m1_subset_1(C_32,k1_zfmisc_1(A_33))
      | ~ r1_tarski(C_32,A_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_78])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_102,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_32])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_109,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_112,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_109])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_112])).

tff(c_116,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:15:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.14  
% 1.72/1.15  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.72/1.15  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.72/1.15  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.72/1.15  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.72/1.15  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.72/1.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.72/1.15  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.72/1.15  tff(c_36, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.72/1.15  tff(c_65, plain, (![B_26, A_27]: (v1_xboole_0(B_26) | ~m1_subset_1(B_26, A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.15  tff(c_73, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_65])).
% 1.72/1.15  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_73])).
% 1.72/1.15  tff(c_24, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.15  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.15  tff(c_30, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.15  tff(c_8, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.15  tff(c_75, plain, (![B_28, A_29]: (m1_subset_1(B_28, A_29) | ~r2_hidden(B_28, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.15  tff(c_78, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_8, c_75])).
% 1.72/1.15  tff(c_94, plain, (![C_32, A_33]: (m1_subset_1(C_32, k1_zfmisc_1(A_33)) | ~r1_tarski(C_32, A_33))), inference(negUnitSimplification, [status(thm)], [c_30, c_78])).
% 1.72/1.15  tff(c_32, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.72/1.15  tff(c_102, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_94, c_32])).
% 1.72/1.15  tff(c_106, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_102])).
% 1.72/1.15  tff(c_109, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_106])).
% 1.72/1.15  tff(c_112, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_109])).
% 1.72/1.15  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_112])).
% 1.72/1.15  tff(c_116, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_73])).
% 1.72/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.15  tff(c_123, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_116, c_2])).
% 1.72/1.15  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_123])).
% 1.72/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  Inference rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Ref     : 0
% 1.72/1.15  #Sup     : 16
% 1.72/1.15  #Fact    : 0
% 1.72/1.15  #Define  : 0
% 1.72/1.15  #Split   : 1
% 1.72/1.15  #Chain   : 0
% 1.72/1.15  #Close   : 0
% 1.72/1.15  
% 1.72/1.15  Ordering : KBO
% 1.72/1.15  
% 1.72/1.15  Simplification rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Subsume      : 2
% 1.72/1.15  #Demod        : 1
% 1.72/1.15  #Tautology    : 6
% 1.72/1.15  #SimpNegUnit  : 4
% 1.72/1.15  #BackRed      : 0
% 1.72/1.15  
% 1.72/1.15  #Partial instantiations: 0
% 1.72/1.15  #Strategies tried      : 1
% 1.72/1.15  
% 1.72/1.15  Timing (in seconds)
% 1.72/1.15  ----------------------
% 1.72/1.15  Preprocessing        : 0.29
% 1.72/1.15  Parsing              : 0.15
% 1.72/1.15  CNF conversion       : 0.02
% 1.72/1.15  Main loop            : 0.11
% 1.72/1.15  Inferencing          : 0.04
% 1.72/1.15  Reduction            : 0.03
% 1.72/1.15  Demodulation         : 0.02
% 1.72/1.15  BG Simplification    : 0.01
% 1.72/1.15  Subsumption          : 0.02
% 1.72/1.15  Abstraction          : 0.01
% 1.72/1.15  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.43
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
