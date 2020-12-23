%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   47 (  69 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [B_38] : k9_subset_1('#skF_4',B_38,'#skF_6') = k3_xboole_0(B_38,'#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_89,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k9_subset_1(A_42,B_43,C_44),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [B_38] :
      ( m1_subset_1(k3_xboole_0(B_38,'#skF_6'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_102,plain,(
    ! [B_38] : m1_subset_1(k3_xboole_0(B_38,'#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_97])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [D_28,A_29,B_30] :
      ( r2_hidden(D_28,A_29)
      | ~ r2_hidden(D_28,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [A_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_61,B_62),B_63),A_61)
      | r1_tarski(k3_xboole_0(A_61,B_62),B_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_201,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(resolution,[status(thm)],[c_183,c_4])).

tff(c_514,plain,(
    ! [A_135,C_136,B_137] :
      ( r1_tarski(k3_subset_1(A_135,C_136),k3_subset_1(A_135,B_137))
      | ~ r1_tarski(B_137,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k9_subset_1('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_519,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_514,c_70])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_38,c_201,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.48/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.35  
% 2.48/1.36  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.48/1.36  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.48/1.36  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.48/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/1.36  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.48/1.36  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.48/1.36  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.48/1.36  tff(c_63, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.48/1.36  tff(c_68, plain, (![B_38]: (k9_subset_1('#skF_4', B_38, '#skF_6')=k3_xboole_0(B_38, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_63])).
% 2.48/1.36  tff(c_89, plain, (![A_42, B_43, C_44]: (m1_subset_1(k9_subset_1(A_42, B_43, C_44), k1_zfmisc_1(A_42)) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.36  tff(c_97, plain, (![B_38]: (m1_subset_1(k3_xboole_0(B_38, '#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_89])).
% 2.48/1.36  tff(c_102, plain, (![B_38]: (m1_subset_1(k3_xboole_0(B_38, '#skF_6'), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_97])).
% 2.48/1.36  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.48/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.36  tff(c_47, plain, (![D_28, A_29, B_30]: (r2_hidden(D_28, A_29) | ~r2_hidden(D_28, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.36  tff(c_183, plain, (![A_61, B_62, B_63]: (r2_hidden('#skF_1'(k3_xboole_0(A_61, B_62), B_63), A_61) | r1_tarski(k3_xboole_0(A_61, B_62), B_63))), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.48/1.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.36  tff(c_201, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(resolution, [status(thm)], [c_183, c_4])).
% 2.48/1.36  tff(c_514, plain, (![A_135, C_136, B_137]: (r1_tarski(k3_subset_1(A_135, C_136), k3_subset_1(A_135, B_137)) | ~r1_tarski(B_137, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_135)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.36  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k9_subset_1('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.48/1.36  tff(c_70, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 2.48/1.36  tff(c_519, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_514, c_70])).
% 2.48/1.36  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_38, c_201, c_519])).
% 2.48/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  Inference rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Ref     : 0
% 2.48/1.36  #Sup     : 108
% 2.48/1.36  #Fact    : 0
% 2.48/1.36  #Define  : 0
% 2.48/1.36  #Split   : 0
% 2.48/1.36  #Chain   : 0
% 2.48/1.36  #Close   : 0
% 2.48/1.36  
% 2.48/1.36  Ordering : KBO
% 2.48/1.36  
% 2.48/1.36  Simplification rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Subsume      : 8
% 2.48/1.36  #Demod        : 10
% 2.48/1.36  #Tautology    : 17
% 2.48/1.36  #SimpNegUnit  : 0
% 2.48/1.36  #BackRed      : 1
% 2.48/1.36  
% 2.48/1.36  #Partial instantiations: 0
% 2.48/1.36  #Strategies tried      : 1
% 2.48/1.36  
% 2.48/1.36  Timing (in seconds)
% 2.48/1.36  ----------------------
% 2.48/1.37  Preprocessing        : 0.30
% 2.48/1.37  Parsing              : 0.16
% 2.48/1.37  CNF conversion       : 0.02
% 2.48/1.37  Main loop            : 0.29
% 2.48/1.37  Inferencing          : 0.11
% 2.48/1.37  Reduction            : 0.07
% 2.48/1.37  Demodulation         : 0.05
% 2.48/1.37  BG Simplification    : 0.02
% 2.48/1.37  Subsumption          : 0.07
% 2.48/1.37  Abstraction          : 0.02
% 2.48/1.37  MUC search           : 0.00
% 2.48/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.62
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
