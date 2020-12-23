%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   51 (  77 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [B_15,A_12] :
      ( r2_hidden(k4_tarski(B_15,k1_funct_1(A_12,B_15)),A_12)
      | ~ r2_hidden(B_15,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_183,plain,(
    ! [A_52,C_53,B_54,D_55] :
      ( r2_hidden(A_52,k9_relat_1(C_53,B_54))
      | ~ r2_hidden(D_55,B_54)
      | ~ r2_hidden(k4_tarski(D_55,A_52),C_53)
      | ~ r2_hidden(D_55,k1_relat_1(C_53))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_214,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(A_56,k9_relat_1(C_57,'#skF_3'))
      | ~ r2_hidden(k4_tarski('#skF_2',A_56),C_57)
      | ~ r2_hidden('#skF_2',k1_relat_1(C_57))
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_235,plain,(
    ! [A_58] :
      ( r2_hidden(k1_funct_1(A_58,'#skF_2'),k9_relat_1(A_58,'#skF_3'))
      | ~ r2_hidden('#skF_2',k1_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_214])).

tff(c_33,plain,(
    ! [B_17,A_18] :
      ( k2_relat_1(k7_relat_1(B_17,A_18)) = k9_relat_1(B_17,A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_24])).

tff(c_45,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_243,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_45])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.28  
% 2.26/1.30  tff(f_77, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 2.26/1.30  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.26/1.30  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.26/1.30  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.26/1.30  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.30  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.30  tff(c_28, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.30  tff(c_18, plain, (![B_15, A_12]: (r2_hidden(k4_tarski(B_15, k1_funct_1(A_12, B_15)), A_12) | ~r2_hidden(B_15, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.30  tff(c_26, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.30  tff(c_183, plain, (![A_52, C_53, B_54, D_55]: (r2_hidden(A_52, k9_relat_1(C_53, B_54)) | ~r2_hidden(D_55, B_54) | ~r2_hidden(k4_tarski(D_55, A_52), C_53) | ~r2_hidden(D_55, k1_relat_1(C_53)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.30  tff(c_214, plain, (![A_56, C_57]: (r2_hidden(A_56, k9_relat_1(C_57, '#skF_3')) | ~r2_hidden(k4_tarski('#skF_2', A_56), C_57) | ~r2_hidden('#skF_2', k1_relat_1(C_57)) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_26, c_183])).
% 2.26/1.30  tff(c_235, plain, (![A_58]: (r2_hidden(k1_funct_1(A_58, '#skF_2'), k9_relat_1(A_58, '#skF_3')) | ~r2_hidden('#skF_2', k1_relat_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_18, c_214])).
% 2.26/1.30  tff(c_33, plain, (![B_17, A_18]: (k2_relat_1(k7_relat_1(B_17, A_18))=k9_relat_1(B_17, A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.30  tff(c_24, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.30  tff(c_39, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_33, c_24])).
% 2.26/1.30  tff(c_45, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_39])).
% 2.26/1.30  tff(c_243, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_235, c_45])).
% 2.26/1.30  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_243])).
% 2.26/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  Inference rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Ref     : 0
% 2.26/1.30  #Sup     : 49
% 2.26/1.30  #Fact    : 0
% 2.26/1.30  #Define  : 0
% 2.26/1.30  #Split   : 0
% 2.26/1.30  #Chain   : 0
% 2.26/1.30  #Close   : 0
% 2.26/1.30  
% 2.26/1.30  Ordering : KBO
% 2.26/1.30  
% 2.26/1.30  Simplification rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Subsume      : 7
% 2.26/1.30  #Demod        : 4
% 2.26/1.30  #Tautology    : 10
% 2.26/1.30  #SimpNegUnit  : 0
% 2.26/1.30  #BackRed      : 0
% 2.26/1.30  
% 2.26/1.30  #Partial instantiations: 0
% 2.26/1.30  #Strategies tried      : 1
% 2.26/1.30  
% 2.26/1.30  Timing (in seconds)
% 2.26/1.30  ----------------------
% 2.26/1.31  Preprocessing        : 0.30
% 2.26/1.31  Parsing              : 0.16
% 2.26/1.31  CNF conversion       : 0.02
% 2.26/1.31  Main loop            : 0.25
% 2.26/1.31  Inferencing          : 0.10
% 2.26/1.31  Reduction            : 0.06
% 2.26/1.31  Demodulation         : 0.04
% 2.26/1.31  BG Simplification    : 0.02
% 2.26/1.31  Subsumption          : 0.05
% 2.26/1.31  Abstraction          : 0.01
% 2.26/1.31  MUC search           : 0.00
% 2.26/1.31  Cooper               : 0.00
% 2.26/1.31  Total                : 0.58
% 2.26/1.31  Index Insertion      : 0.00
% 2.26/1.31  Index Deletion       : 0.00
% 2.26/1.31  Index Matching       : 0.00
% 2.26/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
