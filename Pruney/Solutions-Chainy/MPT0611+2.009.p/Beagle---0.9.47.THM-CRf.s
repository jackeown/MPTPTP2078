%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_12,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19,plain,(
    ! [B_12,A_13] :
      ( r1_xboole_0(B_12,A_13)
      | ~ r1_xboole_0(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r1_xboole_0(k2_relat_1('#skF_2'),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_70,plain,(
    ! [C_26,D_27,A_28,B_29] :
      ( ~ r1_xboole_0(C_26,D_27)
      | r1_xboole_0(k2_zfmisc_1(A_28,C_26),k2_zfmisc_1(B_29,D_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [C_47,A_48,D_51,B_50,A_49] :
      ( r1_xboole_0(A_49,k2_zfmisc_1(B_50,D_51))
      | ~ r1_tarski(A_49,k2_zfmisc_1(A_48,C_47))
      | ~ r1_xboole_0(C_47,D_51) ) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_106,plain,(
    ! [A_52,B_53,D_54] :
      ( r1_xboole_0(A_52,k2_zfmisc_1(B_53,D_54))
      | ~ r1_xboole_0(k2_relat_1(A_52),D_54)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_118,plain,(
    ! [B_53] :
      ( r1_xboole_0('#skF_2',k2_zfmisc_1(B_53,k2_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_135,plain,(
    ! [B_55] : r1_xboole_0('#skF_2',k2_zfmisc_1(B_55,k2_relat_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_118])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [B_62] : r1_xboole_0(k2_zfmisc_1(B_62,k2_relat_1('#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_223,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(A_76,'#skF_2')
      | ~ r1_tarski(A_76,k2_zfmisc_1(B_77,k2_relat_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_227,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_223])).

tff(c_230,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_227])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.63  
% 2.72/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.63  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.72/1.63  
% 2.72/1.63  %Foreground sorts:
% 2.72/1.63  
% 2.72/1.63  
% 2.72/1.63  %Background operators:
% 2.72/1.63  
% 2.72/1.63  
% 2.72/1.63  %Foreground operators:
% 2.72/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.63  
% 2.72/1.65  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 2.72/1.65  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.72/1.65  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.72/1.65  tff(f_41, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.72/1.65  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.72/1.65  tff(c_12, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.65  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.65  tff(c_10, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.65  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.65  tff(c_14, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.65  tff(c_19, plain, (![B_12, A_13]: (r1_xboole_0(B_12, A_13) | ~r1_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.65  tff(c_22, plain, (r1_xboole_0(k2_relat_1('#skF_2'), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_19])).
% 2.72/1.65  tff(c_70, plain, (![C_26, D_27, A_28, B_29]: (~r1_xboole_0(C_26, D_27) | r1_xboole_0(k2_zfmisc_1(A_28, C_26), k2_zfmisc_1(B_29, D_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.65  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.65  tff(c_102, plain, (![C_47, A_48, D_51, B_50, A_49]: (r1_xboole_0(A_49, k2_zfmisc_1(B_50, D_51)) | ~r1_tarski(A_49, k2_zfmisc_1(A_48, C_47)) | ~r1_xboole_0(C_47, D_51))), inference(resolution, [status(thm)], [c_70, c_4])).
% 2.72/1.65  tff(c_106, plain, (![A_52, B_53, D_54]: (r1_xboole_0(A_52, k2_zfmisc_1(B_53, D_54)) | ~r1_xboole_0(k2_relat_1(A_52), D_54) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.72/1.65  tff(c_118, plain, (![B_53]: (r1_xboole_0('#skF_2', k2_zfmisc_1(B_53, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_106])).
% 2.72/1.65  tff(c_135, plain, (![B_55]: (r1_xboole_0('#skF_2', k2_zfmisc_1(B_55, k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_118])).
% 2.72/1.65  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.65  tff(c_153, plain, (![B_62]: (r1_xboole_0(k2_zfmisc_1(B_62, k2_relat_1('#skF_1')), '#skF_2'))), inference(resolution, [status(thm)], [c_135, c_2])).
% 2.72/1.65  tff(c_223, plain, (![A_76, B_77]: (r1_xboole_0(A_76, '#skF_2') | ~r1_tarski(A_76, k2_zfmisc_1(B_77, k2_relat_1('#skF_1'))))), inference(resolution, [status(thm)], [c_153, c_4])).
% 2.72/1.65  tff(c_227, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_223])).
% 2.72/1.65  tff(c_230, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_227])).
% 2.72/1.65  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_230])).
% 2.72/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.65  
% 2.72/1.65  Inference rules
% 2.72/1.65  ----------------------
% 2.72/1.65  #Ref     : 0
% 2.72/1.65  #Sup     : 54
% 2.72/1.65  #Fact    : 0
% 2.72/1.65  #Define  : 0
% 2.72/1.65  #Split   : 0
% 2.72/1.65  #Chain   : 0
% 2.72/1.65  #Close   : 0
% 2.72/1.65  
% 2.72/1.65  Ordering : KBO
% 2.72/1.65  
% 2.72/1.65  Simplification rules
% 2.72/1.65  ----------------------
% 2.72/1.65  #Subsume      : 5
% 2.72/1.65  #Demod        : 8
% 2.72/1.65  #Tautology    : 3
% 2.72/1.65  #SimpNegUnit  : 1
% 2.72/1.65  #BackRed      : 0
% 2.72/1.65  
% 2.72/1.65  #Partial instantiations: 0
% 2.72/1.65  #Strategies tried      : 1
% 2.72/1.65  
% 2.72/1.65  Timing (in seconds)
% 2.72/1.65  ----------------------
% 2.72/1.65  Preprocessing        : 0.41
% 2.72/1.65  Parsing              : 0.23
% 2.72/1.65  CNF conversion       : 0.03
% 2.72/1.65  Main loop            : 0.40
% 2.72/1.65  Inferencing          : 0.16
% 2.72/1.65  Reduction            : 0.09
% 2.72/1.65  Demodulation         : 0.06
% 2.72/1.66  BG Simplification    : 0.02
% 2.72/1.66  Subsumption          : 0.11
% 2.72/1.66  Abstraction          : 0.01
% 2.72/1.66  MUC search           : 0.00
% 2.72/1.66  Cooper               : 0.00
% 2.72/1.66  Total                : 0.85
% 2.72/1.66  Index Insertion      : 0.00
% 2.72/1.66  Index Deletion       : 0.00
% 2.72/1.66  Index Matching       : 0.00
% 2.72/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
