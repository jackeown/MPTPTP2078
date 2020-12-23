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
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   44 (  75 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 175 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> ( r2_hidden(A,k1_relat_1(C))
            & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_51,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_28,plain,
    ( r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3')
    | r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,
    ( r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3')
    | k1_funct_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    k1_funct_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( k1_funct_1('#skF_3','#skF_1') != '#skF_2'
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_29,c_18])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ! [B_17,A_18] :
      ( r2_hidden(k4_tarski(B_17,k1_funct_1(A_18,B_17)),A_18)
      | ~ r2_hidden(B_17,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_59,plain,
    ( r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_50])).

tff(c_63,plain,(
    r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_34,c_59])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_63])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_66,plain,(
    r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_68,plain,(
    ! [A_19,C_20,B_21] :
      ( r2_hidden(A_19,k1_relat_1(C_20))
      | ~ r2_hidden(k4_tarski(A_19,B_21),C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_68])).

tff(c_74,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_71])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_74])).

tff(c_78,plain,(
    k1_funct_1('#skF_3','#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_77,plain,(
    r2_hidden(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_89,plain,(
    ! [A_25,C_26,B_27] :
      ( r2_hidden(A_25,k1_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_25,B_27),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_89])).

tff(c_95,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_92])).

tff(c_117,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_funct_1(A_34,B_35) = C_36
      | ~ r2_hidden(k4_tarski(B_35,C_36),A_34)
      | ~ r2_hidden(B_35,k1_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,
    ( k1_funct_1('#skF_3','#skF_1') = '#skF_2'
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_117])).

tff(c_133,plain,(
    k1_funct_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_95,c_127])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.16  
% 1.78/1.16  %Foreground sorts:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Background operators:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Foreground operators:
% 1.78/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.16  
% 1.78/1.17  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.78/1.17  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 1.78/1.17  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.78/1.17  tff(c_28, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3') | r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.17  tff(c_34, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 1.78/1.17  tff(c_24, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3') | k1_funct_1('#skF_3', '#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.17  tff(c_29, plain, (k1_funct_1('#skF_3', '#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 1.78/1.17  tff(c_18, plain, (k1_funct_1('#skF_3', '#skF_1')!='#skF_2' | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.17  tff(c_49, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_29, c_18])).
% 1.78/1.17  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.17  tff(c_14, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.17  tff(c_50, plain, (![B_17, A_18]: (r2_hidden(k4_tarski(B_17, k1_funct_1(A_18, B_17)), A_18) | ~r2_hidden(B_17, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.17  tff(c_59, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_50])).
% 1.78/1.17  tff(c_63, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_34, c_59])).
% 1.78/1.17  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_63])).
% 1.78/1.17  tff(c_67, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 1.78/1.17  tff(c_66, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 1.78/1.17  tff(c_68, plain, (![A_19, C_20, B_21]: (r2_hidden(A_19, k1_relat_1(C_20)) | ~r2_hidden(k4_tarski(A_19, B_21), C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.17  tff(c_71, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_68])).
% 1.78/1.17  tff(c_74, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_71])).
% 1.78/1.17  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_74])).
% 1.78/1.17  tff(c_78, plain, (k1_funct_1('#skF_3', '#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 1.78/1.17  tff(c_77, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 1.78/1.17  tff(c_89, plain, (![A_25, C_26, B_27]: (r2_hidden(A_25, k1_relat_1(C_26)) | ~r2_hidden(k4_tarski(A_25, B_27), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.17  tff(c_92, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_77, c_89])).
% 1.78/1.17  tff(c_95, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_92])).
% 1.78/1.17  tff(c_117, plain, (![A_34, B_35, C_36]: (k1_funct_1(A_34, B_35)=C_36 | ~r2_hidden(k4_tarski(B_35, C_36), A_34) | ~r2_hidden(B_35, k1_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.17  tff(c_127, plain, (k1_funct_1('#skF_3', '#skF_1')='#skF_2' | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_77, c_117])).
% 1.78/1.17  tff(c_133, plain, (k1_funct_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_95, c_127])).
% 1.78/1.17  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_133])).
% 1.78/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  Inference rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Ref     : 0
% 1.78/1.17  #Sup     : 17
% 1.78/1.17  #Fact    : 0
% 1.78/1.17  #Define  : 0
% 1.78/1.17  #Split   : 2
% 1.78/1.17  #Chain   : 0
% 1.78/1.17  #Close   : 0
% 1.78/1.17  
% 1.78/1.17  Ordering : KBO
% 1.78/1.17  
% 1.78/1.17  Simplification rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Subsume      : 2
% 1.78/1.17  #Demod        : 13
% 1.78/1.17  #Tautology    : 9
% 1.78/1.17  #SimpNegUnit  : 3
% 1.78/1.17  #BackRed      : 0
% 1.78/1.17  
% 1.78/1.17  #Partial instantiations: 0
% 1.78/1.17  #Strategies tried      : 1
% 1.78/1.17  
% 1.78/1.17  Timing (in seconds)
% 1.78/1.17  ----------------------
% 1.78/1.17  Preprocessing        : 0.27
% 1.78/1.17  Parsing              : 0.15
% 1.78/1.17  CNF conversion       : 0.02
% 1.78/1.17  Main loop            : 0.14
% 1.78/1.17  Inferencing          : 0.06
% 1.93/1.17  Reduction            : 0.04
% 1.93/1.17  Demodulation         : 0.03
% 1.93/1.17  BG Simplification    : 0.01
% 1.93/1.17  Subsumption          : 0.02
% 1.93/1.17  Abstraction          : 0.01
% 1.93/1.17  MUC search           : 0.00
% 1.93/1.17  Cooper               : 0.00
% 1.93/1.17  Total                : 0.44
% 1.93/1.17  Index Insertion      : 0.00
% 1.93/1.17  Index Deletion       : 0.00
% 1.93/1.17  Index Matching       : 0.00
% 1.93/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
