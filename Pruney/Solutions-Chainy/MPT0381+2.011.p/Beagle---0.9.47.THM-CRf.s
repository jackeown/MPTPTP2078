%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 134 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
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
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_260,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k2_tarski(A_74,B_75),C_76)
      | ~ r2_hidden(B_75,C_76)
      | ~ r2_hidden(A_74,C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k2_tarski(A_52,B_53),C_54)
      | ~ r2_hidden(B_53,C_54)
      | ~ r2_hidden(A_52,C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_180,plain,(
    ! [A_55,C_56] :
      ( r1_tarski(k1_tarski(A_55),C_56)
      | ~ r2_hidden(A_55,C_56)
      | ~ r2_hidden(A_55,C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_168])).

tff(c_75,plain,(
    ! [B_30,A_31] :
      ( m1_subset_1(B_30,A_31)
      | ~ v1_xboole_0(B_30)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_75,c_36])).

tff(c_84,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ r2_hidden(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [C_50,A_51] :
      ( m1_subset_1(C_50,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51))
      | ~ r1_tarski(C_50,A_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_162,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_36])).

tff(c_167,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_162])).

tff(c_183,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_167])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183])).

tff(c_192,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_58,plain,(
    ! [C_22,A_23] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_23,C_22] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_195,plain,(
    ! [C_22] : ~ r1_tarski(C_22,'#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_62])).

tff(c_276,plain,(
    ! [B_75,A_74] :
      ( ~ r2_hidden(B_75,'#skF_5')
      | ~ r2_hidden(A_74,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_260,c_195])).

tff(c_277,plain,(
    ! [A_74] : ~ r2_hidden(A_74,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_38])).

tff(c_280,plain,(
    ! [B_75] : ~ r2_hidden(B_75,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 1.97/1.27  
% 1.97/1.27  %Foreground sorts:
% 1.97/1.27  
% 1.97/1.27  
% 1.97/1.27  %Background operators:
% 1.97/1.27  
% 1.97/1.27  
% 1.97/1.27  %Foreground operators:
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.97/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.27  
% 1.97/1.28  tff(f_48, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.97/1.28  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.97/1.28  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.28  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.97/1.28  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.97/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.97/1.28  tff(c_260, plain, (![A_74, B_75, C_76]: (r1_tarski(k2_tarski(A_74, B_75), C_76) | ~r2_hidden(B_75, C_76) | ~r2_hidden(A_74, C_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.28  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.97/1.28  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.28  tff(c_168, plain, (![A_52, B_53, C_54]: (r1_tarski(k2_tarski(A_52, B_53), C_54) | ~r2_hidden(B_53, C_54) | ~r2_hidden(A_52, C_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.28  tff(c_180, plain, (![A_55, C_56]: (r1_tarski(k1_tarski(A_55), C_56) | ~r2_hidden(A_55, C_56) | ~r2_hidden(A_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_6, c_168])).
% 1.97/1.28  tff(c_75, plain, (![B_30, A_31]: (m1_subset_1(B_30, A_31) | ~v1_xboole_0(B_30) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.28  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.97/1.28  tff(c_83, plain, (~v1_xboole_0(k1_tarski('#skF_4')) | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_75, c_36])).
% 1.97/1.28  tff(c_84, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_83])).
% 1.97/1.28  tff(c_12, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.28  tff(c_99, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~r2_hidden(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.28  tff(c_153, plain, (![C_50, A_51]: (m1_subset_1(C_50, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)) | ~r1_tarski(C_50, A_51))), inference(resolution, [status(thm)], [c_12, c_99])).
% 1.97/1.28  tff(c_162, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_153, c_36])).
% 1.97/1.28  tff(c_167, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_162])).
% 1.97/1.29  tff(c_183, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_180, c_167])).
% 1.97/1.29  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_183])).
% 1.97/1.29  tff(c_192, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_83])).
% 1.97/1.29  tff(c_58, plain, (![C_22, A_23]: (r2_hidden(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.29  tff(c_62, plain, (![A_23, C_22]: (~v1_xboole_0(k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.97/1.29  tff(c_195, plain, (![C_22]: (~r1_tarski(C_22, '#skF_5'))), inference(resolution, [status(thm)], [c_192, c_62])).
% 1.97/1.29  tff(c_276, plain, (![B_75, A_74]: (~r2_hidden(B_75, '#skF_5') | ~r2_hidden(A_74, '#skF_5'))), inference(resolution, [status(thm)], [c_260, c_195])).
% 1.97/1.29  tff(c_277, plain, (![A_74]: (~r2_hidden(A_74, '#skF_5'))), inference(splitLeft, [status(thm)], [c_276])).
% 1.97/1.29  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_38])).
% 1.97/1.29  tff(c_280, plain, (![B_75]: (~r2_hidden(B_75, '#skF_5'))), inference(splitRight, [status(thm)], [c_276])).
% 1.97/1.29  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_38])).
% 1.97/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  Inference rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Ref     : 0
% 1.97/1.29  #Sup     : 49
% 1.97/1.29  #Fact    : 0
% 1.97/1.29  #Define  : 0
% 1.97/1.29  #Split   : 2
% 1.97/1.29  #Chain   : 0
% 1.97/1.29  #Close   : 0
% 1.97/1.29  
% 1.97/1.29  Ordering : KBO
% 1.97/1.29  
% 1.97/1.29  Simplification rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Subsume      : 6
% 1.97/1.29  #Demod        : 2
% 1.97/1.29  #Tautology    : 22
% 1.97/1.29  #SimpNegUnit  : 5
% 1.97/1.29  #BackRed      : 2
% 1.97/1.29  
% 1.97/1.29  #Partial instantiations: 0
% 1.97/1.29  #Strategies tried      : 1
% 1.97/1.29  
% 1.97/1.29  Timing (in seconds)
% 1.97/1.29  ----------------------
% 1.97/1.29  Preprocessing        : 0.30
% 1.97/1.29  Parsing              : 0.15
% 1.97/1.29  CNF conversion       : 0.02
% 1.97/1.29  Main loop            : 0.18
% 1.97/1.29  Inferencing          : 0.07
% 1.97/1.29  Reduction            : 0.05
% 1.97/1.29  Demodulation         : 0.03
% 1.97/1.29  BG Simplification    : 0.02
% 1.97/1.29  Subsumption          : 0.04
% 1.97/1.29  Abstraction          : 0.01
% 1.97/1.29  MUC search           : 0.00
% 1.97/1.29  Cooper               : 0.00
% 1.97/1.29  Total                : 0.51
% 1.97/1.29  Index Insertion      : 0.00
% 1.97/1.29  Index Deletion       : 0.00
% 1.97/1.29  Index Matching       : 0.00
% 1.97/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
