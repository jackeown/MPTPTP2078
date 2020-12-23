%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_431,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_444,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_431])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_368,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_xboole_0(A_61,C_62)
      | ~ r1_xboole_0(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_638,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_xboole_0(A_77,B_78)
      | ~ r1_tarski(A_77,k4_xboole_0(A_79,B_78)) ) ),
    inference(resolution,[status(thm)],[c_14,c_368])).

tff(c_697,plain,(
    ! [A_82] :
      ( r1_xboole_0(A_82,'#skF_5')
      | ~ r1_tarski(A_82,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_638])).

tff(c_706,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_697])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_713,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_706,c_16])).

tff(c_48,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_129])).

tff(c_714,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_141])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.79/1.44  
% 2.79/1.44  %Foreground sorts:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Background operators:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Foreground operators:
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.79/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.44  
% 2.79/1.45  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.79/1.45  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.79/1.45  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.79/1.45  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.79/1.45  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.79/1.45  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.79/1.45  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_431, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.45  tff(c_444, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_431])).
% 2.79/1.45  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.45  tff(c_368, plain, (![A_61, C_62, B_63]: (r1_xboole_0(A_61, C_62) | ~r1_xboole_0(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.45  tff(c_638, plain, (![A_77, B_78, A_79]: (r1_xboole_0(A_77, B_78) | ~r1_tarski(A_77, k4_xboole_0(A_79, B_78)))), inference(resolution, [status(thm)], [c_14, c_368])).
% 2.79/1.45  tff(c_697, plain, (![A_82]: (r1_xboole_0(A_82, '#skF_5') | ~r1_tarski(A_82, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_444, c_638])).
% 2.79/1.45  tff(c_706, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_697])).
% 2.79/1.45  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.79/1.45  tff(c_713, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_706, c_16])).
% 2.79/1.45  tff(c_48, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.45  tff(c_129, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.45  tff(c_141, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_129])).
% 2.79/1.45  tff(c_714, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_713, c_141])).
% 2.79/1.45  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_714])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 186
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 1
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 12
% 2.79/1.45  #Demod        : 63
% 2.79/1.45  #Tautology    : 110
% 2.79/1.45  #SimpNegUnit  : 3
% 2.79/1.45  #BackRed      : 2
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.32
% 2.79/1.45  Parsing              : 0.17
% 2.79/1.45  CNF conversion       : 0.02
% 2.79/1.45  Main loop            : 0.31
% 2.91/1.45  Inferencing          : 0.11
% 2.91/1.45  Reduction            : 0.10
% 2.91/1.45  Demodulation         : 0.07
% 2.91/1.45  BG Simplification    : 0.02
% 2.91/1.45  Subsumption          : 0.05
% 2.91/1.45  Abstraction          : 0.01
% 2.91/1.45  MUC search           : 0.00
% 2.91/1.45  Cooper               : 0.00
% 2.91/1.45  Total                : 0.66
% 2.91/1.45  Index Insertion      : 0.00
% 2.91/1.45  Index Deletion       : 0.00
% 2.91/1.45  Index Matching       : 0.00
% 2.91/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
