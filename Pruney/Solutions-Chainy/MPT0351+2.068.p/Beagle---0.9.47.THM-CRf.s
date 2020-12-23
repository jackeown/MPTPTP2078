%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  57 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,A_30)
      | ~ m1_subset_1(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [B_29,A_3] :
      ( r1_tarski(B_29,A_3)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_77,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_73])).

tff(c_90,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_186,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_subset_1(A_49,B_50,C_51) = k2_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_200,plain,(
    ! [A_52,B_53] :
      ( k4_subset_1(A_52,B_53,A_52) = k2_xboole_0(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_36,c_186])).

tff(c_209,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_200])).

tff(c_215,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_209])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.84/1.21  
% 1.84/1.21  %Foreground sorts:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Background operators:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Foreground operators:
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 1.84/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.84/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.21  
% 1.84/1.22  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.84/1.22  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 1.84/1.22  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.84/1.22  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.84/1.22  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.84/1.22  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.84/1.22  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.84/1.22  tff(f_62, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.84/1.22  tff(c_24, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.22  tff(c_32, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.84/1.22  tff(c_35, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_32])).
% 1.84/1.22  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.84/1.22  tff(c_28, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.22  tff(c_69, plain, (![B_29, A_30]: (r2_hidden(B_29, A_30) | ~m1_subset_1(B_29, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.23  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.23  tff(c_73, plain, (![B_29, A_3]: (r1_tarski(B_29, A_3) | ~m1_subset_1(B_29, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_69, c_4])).
% 1.84/1.23  tff(c_77, plain, (![B_31, A_32]: (r1_tarski(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)))), inference(negUnitSimplification, [status(thm)], [c_28, c_73])).
% 1.84/1.23  tff(c_90, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_77])).
% 1.84/1.23  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.23  tff(c_99, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_90, c_2])).
% 1.84/1.23  tff(c_26, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.23  tff(c_36, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 1.84/1.23  tff(c_186, plain, (![A_49, B_50, C_51]: (k4_subset_1(A_49, B_50, C_51)=k2_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.84/1.23  tff(c_200, plain, (![A_52, B_53]: (k4_subset_1(A_52, B_53, A_52)=k2_xboole_0(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_36, c_186])).
% 1.84/1.23  tff(c_209, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_200])).
% 1.84/1.23  tff(c_215, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_209])).
% 1.84/1.23  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_215])).
% 1.84/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  Inference rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Ref     : 0
% 1.84/1.23  #Sup     : 39
% 1.84/1.23  #Fact    : 0
% 1.84/1.23  #Define  : 0
% 1.84/1.23  #Split   : 0
% 1.84/1.23  #Chain   : 0
% 1.84/1.23  #Close   : 0
% 1.84/1.23  
% 1.84/1.23  Ordering : KBO
% 1.84/1.23  
% 1.84/1.23  Simplification rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Subsume      : 6
% 1.84/1.23  #Demod        : 5
% 1.84/1.23  #Tautology    : 12
% 1.84/1.23  #SimpNegUnit  : 3
% 1.84/1.23  #BackRed      : 0
% 1.84/1.23  
% 1.84/1.23  #Partial instantiations: 0
% 1.84/1.23  #Strategies tried      : 1
% 1.84/1.23  
% 1.84/1.23  Timing (in seconds)
% 1.84/1.23  ----------------------
% 1.84/1.23  Preprocessing        : 0.29
% 1.84/1.23  Parsing              : 0.15
% 1.84/1.23  CNF conversion       : 0.02
% 1.84/1.23  Main loop            : 0.17
% 1.84/1.23  Inferencing          : 0.06
% 1.84/1.23  Reduction            : 0.05
% 1.84/1.23  Demodulation         : 0.03
% 1.84/1.23  BG Simplification    : 0.01
% 1.84/1.23  Subsumption          : 0.03
% 1.84/1.23  Abstraction          : 0.01
% 1.84/1.23  MUC search           : 0.00
% 1.84/1.23  Cooper               : 0.00
% 1.84/1.23  Total                : 0.48
% 1.84/1.23  Index Insertion      : 0.00
% 1.84/1.23  Index Deletion       : 0.00
% 1.84/1.23  Index Matching       : 0.00
% 1.84/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
