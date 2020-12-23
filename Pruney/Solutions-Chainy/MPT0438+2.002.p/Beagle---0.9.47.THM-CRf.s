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
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 13.53s
% Output     : CNFRefutation 13.53s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(k4_tarski('#skF_1'(A_99,B_100),'#skF_2'(A_99,B_100)),A_99)
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_37,A_22,D_40] :
      ( r2_hidden(C_37,k1_relat_1(A_22))
      | ~ r2_hidden(k4_tarski(C_37,D_40),A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100),k1_relat_1(A_99))
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_140,c_16])).

tff(c_28,plain,(
    ! [C_56,A_41,D_59] :
      ( r2_hidden(C_56,k2_relat_1(A_41))
      | ~ r2_hidden(k4_tarski(D_59,C_56),A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_2'(A_99,B_100),k2_relat_1(A_99))
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_108,B_109] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_108,B_109),'#skF_2'(A_108,B_109)),B_109)
      | r1_tarski(A_108,B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20462,plain,(
    ! [A_689,C_690,D_691] :
      ( r1_tarski(A_689,k2_zfmisc_1(C_690,D_691))
      | ~ v1_relat_1(A_689)
      | ~ r2_hidden('#skF_2'(A_689,k2_zfmisc_1(C_690,D_691)),D_691)
      | ~ r2_hidden('#skF_1'(A_689,k2_zfmisc_1(C_690,D_691)),C_690) ) ),
    inference(resolution,[status(thm)],[c_2,c_215])).

tff(c_24199,plain,(
    ! [A_732,C_733] :
      ( ~ r2_hidden('#skF_1'(A_732,k2_zfmisc_1(C_733,k2_relat_1(A_732))),C_733)
      | r1_tarski(A_732,k2_zfmisc_1(C_733,k2_relat_1(A_732)))
      | ~ v1_relat_1(A_732) ) ),
    inference(resolution,[status(thm)],[c_169,c_20462])).

tff(c_24431,plain,(
    ! [A_734] :
      ( r1_tarski(A_734,k2_zfmisc_1(k1_relat_1(A_734),k2_relat_1(A_734)))
      | ~ v1_relat_1(A_734) ) ),
    inference(resolution,[status(thm)],[c_168,c_24199])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_11',k2_zfmisc_1(k1_relat_1('#skF_11'),k2_relat_1('#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24449,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_24431,c_38])).

tff(c_24472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.53/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/5.56  
% 13.53/5.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/5.57  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 13.53/5.57  
% 13.53/5.57  %Foreground sorts:
% 13.53/5.57  
% 13.53/5.57  
% 13.53/5.57  %Background operators:
% 13.53/5.57  
% 13.53/5.57  
% 13.53/5.57  %Foreground operators:
% 13.53/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.53/5.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.53/5.57  tff('#skF_11', type, '#skF_11': $i).
% 13.53/5.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 13.53/5.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.53/5.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.53/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.53/5.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.53/5.57  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 13.53/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.53/5.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.53/5.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.53/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.53/5.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.53/5.57  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.53/5.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.53/5.57  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 13.53/5.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.53/5.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.53/5.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.53/5.57  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 13.53/5.57  
% 13.53/5.57  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 13.53/5.57  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 13.53/5.57  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 13.53/5.57  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 13.53/5.57  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 13.53/5.57  tff(c_40, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.53/5.57  tff(c_140, plain, (![A_99, B_100]: (r2_hidden(k4_tarski('#skF_1'(A_99, B_100), '#skF_2'(A_99, B_100)), A_99) | r1_tarski(A_99, B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.53/5.57  tff(c_16, plain, (![C_37, A_22, D_40]: (r2_hidden(C_37, k1_relat_1(A_22)) | ~r2_hidden(k4_tarski(C_37, D_40), A_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.53/5.57  tff(c_168, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100), k1_relat_1(A_99)) | r1_tarski(A_99, B_100) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_140, c_16])).
% 13.53/5.57  tff(c_28, plain, (![C_56, A_41, D_59]: (r2_hidden(C_56, k2_relat_1(A_41)) | ~r2_hidden(k4_tarski(D_59, C_56), A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.53/5.57  tff(c_169, plain, (![A_99, B_100]: (r2_hidden('#skF_2'(A_99, B_100), k2_relat_1(A_99)) | r1_tarski(A_99, B_100) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_140, c_28])).
% 13.53/5.57  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.53/5.57  tff(c_215, plain, (![A_108, B_109]: (~r2_hidden(k4_tarski('#skF_1'(A_108, B_109), '#skF_2'(A_108, B_109)), B_109) | r1_tarski(A_108, B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.53/5.57  tff(c_20462, plain, (![A_689, C_690, D_691]: (r1_tarski(A_689, k2_zfmisc_1(C_690, D_691)) | ~v1_relat_1(A_689) | ~r2_hidden('#skF_2'(A_689, k2_zfmisc_1(C_690, D_691)), D_691) | ~r2_hidden('#skF_1'(A_689, k2_zfmisc_1(C_690, D_691)), C_690))), inference(resolution, [status(thm)], [c_2, c_215])).
% 13.53/5.57  tff(c_24199, plain, (![A_732, C_733]: (~r2_hidden('#skF_1'(A_732, k2_zfmisc_1(C_733, k2_relat_1(A_732))), C_733) | r1_tarski(A_732, k2_zfmisc_1(C_733, k2_relat_1(A_732))) | ~v1_relat_1(A_732))), inference(resolution, [status(thm)], [c_169, c_20462])).
% 13.53/5.57  tff(c_24431, plain, (![A_734]: (r1_tarski(A_734, k2_zfmisc_1(k1_relat_1(A_734), k2_relat_1(A_734))) | ~v1_relat_1(A_734))), inference(resolution, [status(thm)], [c_168, c_24199])).
% 13.53/5.57  tff(c_38, plain, (~r1_tarski('#skF_11', k2_zfmisc_1(k1_relat_1('#skF_11'), k2_relat_1('#skF_11')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.53/5.57  tff(c_24449, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_24431, c_38])).
% 13.53/5.57  tff(c_24472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_24449])).
% 13.53/5.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/5.57  
% 13.53/5.57  Inference rules
% 13.53/5.57  ----------------------
% 13.53/5.57  #Ref     : 0
% 13.53/5.57  #Sup     : 6691
% 13.53/5.57  #Fact    : 0
% 13.53/5.57  #Define  : 0
% 13.53/5.57  #Split   : 0
% 13.53/5.57  #Chain   : 0
% 13.53/5.57  #Close   : 0
% 13.53/5.57  
% 13.53/5.57  Ordering : KBO
% 13.53/5.57  
% 13.53/5.57  Simplification rules
% 13.53/5.57  ----------------------
% 13.53/5.57  #Subsume      : 517
% 13.53/5.57  #Demod        : 3
% 13.53/5.57  #Tautology    : 42
% 13.53/5.57  #SimpNegUnit  : 0
% 13.53/5.57  #BackRed      : 0
% 13.53/5.57  
% 13.53/5.57  #Partial instantiations: 0
% 13.53/5.57  #Strategies tried      : 1
% 13.53/5.57  
% 13.53/5.57  Timing (in seconds)
% 13.53/5.57  ----------------------
% 13.53/5.58  Preprocessing        : 0.29
% 13.53/5.58  Parsing              : 0.15
% 13.53/5.58  CNF conversion       : 0.03
% 13.53/5.58  Main loop            : 4.51
% 13.53/5.58  Inferencing          : 0.79
% 13.53/5.58  Reduction            : 0.55
% 13.53/5.58  Demodulation         : 0.32
% 13.53/5.58  BG Simplification    : 0.13
% 13.53/5.58  Subsumption          : 2.71
% 13.53/5.58  Abstraction          : 0.20
% 13.53/5.58  MUC search           : 0.00
% 13.53/5.58  Cooper               : 0.00
% 13.53/5.58  Total                : 4.83
% 13.53/5.58  Index Insertion      : 0.00
% 13.53/5.58  Index Deletion       : 0.00
% 13.53/5.58  Index Matching       : 0.00
% 13.53/5.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
