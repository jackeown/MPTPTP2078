%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  75 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_60,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_79,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(k4_tarski(B_62,k1_funct_1(A_63,B_62)),A_63)
      | ~ r2_hidden(B_62,k1_relat_1(A_63))
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [D_54,A_55,B_56,E_57] :
      ( r2_hidden(D_54,k9_relat_1(A_55,B_56))
      | ~ r2_hidden(E_57,B_56)
      | ~ r2_hidden(k4_tarski(E_57,D_54),A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [D_54,A_55] :
      ( r2_hidden(D_54,k9_relat_1(A_55,'#skF_6'))
      | ~ r2_hidden(k4_tarski('#skF_5',D_54),A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_88,plain,(
    ! [A_64] :
      ( r2_hidden(k1_funct_1(A_64,'#skF_5'),k9_relat_1(A_64,'#skF_6'))
      | ~ r2_hidden('#skF_5',k1_relat_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_79,c_63])).

tff(c_39,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(k7_relat_1(B_50,A_51)) = k9_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_30])).

tff(c_51,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_45])).

tff(c_93,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_51])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:51:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.91/1.23  
% 1.91/1.23  %Foreground sorts:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Background operators:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Foreground operators:
% 1.91/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.91/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.23  
% 1.91/1.24  tff(f_71, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 1.91/1.24  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 1.91/1.24  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 1.91/1.24  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.91/1.24  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.24  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.24  tff(c_34, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.24  tff(c_79, plain, (![B_62, A_63]: (r2_hidden(k4_tarski(B_62, k1_funct_1(A_63, B_62)), A_63) | ~r2_hidden(B_62, k1_relat_1(A_63)) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.24  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.24  tff(c_54, plain, (![D_54, A_55, B_56, E_57]: (r2_hidden(D_54, k9_relat_1(A_55, B_56)) | ~r2_hidden(E_57, B_56) | ~r2_hidden(k4_tarski(E_57, D_54), A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.24  tff(c_63, plain, (![D_54, A_55]: (r2_hidden(D_54, k9_relat_1(A_55, '#skF_6')) | ~r2_hidden(k4_tarski('#skF_5', D_54), A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_32, c_54])).
% 1.91/1.24  tff(c_88, plain, (![A_64]: (r2_hidden(k1_funct_1(A_64, '#skF_5'), k9_relat_1(A_64, '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(A_64)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_79, c_63])).
% 1.91/1.24  tff(c_39, plain, (![B_50, A_51]: (k2_relat_1(k7_relat_1(B_50, A_51))=k9_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.24  tff(c_30, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.24  tff(c_45, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_39, c_30])).
% 1.91/1.24  tff(c_51, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_45])).
% 1.91/1.24  tff(c_93, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_51])).
% 1.91/1.24  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_93])).
% 1.91/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  Inference rules
% 1.91/1.24  ----------------------
% 1.91/1.24  #Ref     : 0
% 1.91/1.24  #Sup     : 13
% 1.91/1.24  #Fact    : 0
% 1.91/1.24  #Define  : 0
% 1.91/1.24  #Split   : 0
% 1.91/1.24  #Chain   : 0
% 1.91/1.24  #Close   : 0
% 1.91/1.24  
% 1.91/1.24  Ordering : KBO
% 1.91/1.24  
% 1.91/1.24  Simplification rules
% 1.91/1.24  ----------------------
% 1.91/1.24  #Subsume      : 1
% 1.91/1.24  #Demod        : 4
% 1.91/1.24  #Tautology    : 2
% 1.91/1.24  #SimpNegUnit  : 0
% 1.91/1.24  #BackRed      : 0
% 1.91/1.24  
% 1.91/1.24  #Partial instantiations: 0
% 1.91/1.24  #Strategies tried      : 1
% 1.91/1.24  
% 1.91/1.24  Timing (in seconds)
% 1.91/1.24  ----------------------
% 1.91/1.25  Preprocessing        : 0.31
% 1.91/1.25  Parsing              : 0.17
% 1.91/1.25  CNF conversion       : 0.03
% 1.91/1.25  Main loop            : 0.13
% 1.91/1.25  Inferencing          : 0.05
% 1.91/1.25  Reduction            : 0.04
% 1.91/1.25  Demodulation         : 0.03
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.02
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.47
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
