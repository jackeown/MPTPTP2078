%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  76 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) != k1_xboole_0
     => ! [C] :
          ( m1_subset_1(C,k2_zfmisc_1(A,B))
         => ( C != k1_mcart_1(C)
            & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_13,B_14] : ~ r2_hidden(A_13,k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_16,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_49,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    m1_subset_1('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_70,plain,(
    ! [C_20,A_21,B_22] :
      ( k1_mcart_1(C_20) != C_20
      | ~ m1_subset_1(C_20,k2_zfmisc_1(A_21,B_22))
      | k2_zfmisc_1(A_21,B_22) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,
    ( k1_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_70])).

tff(c_82,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_73])).

tff(c_86,plain,(
    r2_hidden('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_86])).

tff(c_89,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_119,plain,(
    ! [C_28,A_29,B_30] :
      ( k2_mcart_1(C_28) != C_28
      | ~ m1_subset_1(C_28,k2_zfmisc_1(A_29,B_30))
      | k2_zfmisc_1(A_29,B_30) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,
    ( k2_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_119])).

tff(c_131,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_122])).

tff(c_135,plain,(
    r2_hidden('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_18])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:52:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  %$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.80/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.80/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.17  
% 1.80/1.18  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.80/1.18  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.80/1.18  tff(f_59, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.80/1.18  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 1.80/1.18  tff(f_50, axiom, (![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 1.80/1.18  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.18  tff(c_41, plain, (![A_13, B_14]: (~r2_hidden(A_13, k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.18  tff(c_44, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 1.80/1.18  tff(c_16, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.80/1.18  tff(c_54, plain, (k1_mcart_1('#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 1.80/1.18  tff(c_18, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.80/1.18  tff(c_49, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.18  tff(c_53, plain, (m1_subset_1('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_49])).
% 1.80/1.18  tff(c_70, plain, (![C_20, A_21, B_22]: (k1_mcart_1(C_20)!=C_20 | ~m1_subset_1(C_20, k2_zfmisc_1(A_21, B_22)) | k2_zfmisc_1(A_21, B_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.18  tff(c_73, plain, (k1_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_70])).
% 1.80/1.18  tff(c_82, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_73])).
% 1.80/1.18  tff(c_86, plain, (r2_hidden('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_18])).
% 1.80/1.18  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_86])).
% 1.80/1.18  tff(c_89, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 1.80/1.18  tff(c_119, plain, (![C_28, A_29, B_30]: (k2_mcart_1(C_28)!=C_28 | ~m1_subset_1(C_28, k2_zfmisc_1(A_29, B_30)) | k2_zfmisc_1(A_29, B_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.18  tff(c_122, plain, (k2_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_119])).
% 1.80/1.18  tff(c_131, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_122])).
% 1.80/1.18  tff(c_135, plain, (r2_hidden('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_18])).
% 1.80/1.18  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_135])).
% 1.80/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  Inference rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Ref     : 0
% 1.80/1.18  #Sup     : 26
% 1.80/1.18  #Fact    : 0
% 1.80/1.18  #Define  : 0
% 1.80/1.18  #Split   : 1
% 1.80/1.18  #Chain   : 0
% 1.80/1.18  #Close   : 0
% 1.80/1.18  
% 1.80/1.18  Ordering : KBO
% 1.80/1.18  
% 1.80/1.18  Simplification rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Subsume      : 2
% 1.80/1.18  #Demod        : 12
% 1.80/1.18  #Tautology    : 20
% 1.80/1.18  #SimpNegUnit  : 2
% 1.80/1.18  #BackRed      : 4
% 1.80/1.18  
% 1.80/1.18  #Partial instantiations: 0
% 1.80/1.18  #Strategies tried      : 1
% 1.80/1.18  
% 1.80/1.18  Timing (in seconds)
% 1.80/1.18  ----------------------
% 1.80/1.18  Preprocessing        : 0.28
% 1.80/1.18  Parsing              : 0.16
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.19  Main loop            : 0.12
% 1.80/1.19  Inferencing          : 0.05
% 1.80/1.19  Reduction            : 0.04
% 1.80/1.19  Demodulation         : 0.03
% 1.80/1.19  BG Simplification    : 0.01
% 1.80/1.19  Subsumption          : 0.02
% 1.80/1.19  Abstraction          : 0.01
% 1.80/1.19  MUC search           : 0.00
% 1.80/1.19  Cooper               : 0.00
% 1.80/1.19  Total                : 0.42
% 1.80/1.19  Index Insertion      : 0.00
% 1.80/1.19  Index Deletion       : 0.00
% 1.80/1.19  Index Matching       : 0.00
% 1.80/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
