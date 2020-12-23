%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:24 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  80 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    k2_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_405,plain,(
    ! [C_47,A_48,B_49] :
      ( k2_xboole_0(k10_relat_1(C_47,A_48),k10_relat_1(C_47,B_49)) = k10_relat_1(C_47,k2_xboole_0(A_48,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_531,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k10_relat_1(C_56,A_57),k10_relat_1(C_56,k2_xboole_0(A_57,B_58)))
      | ~ v1_relat_1(C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_6])).

tff(c_565,plain,(
    ! [C_60] :
      ( r1_tarski(k10_relat_1(C_60,k9_relat_1('#skF_3','#skF_1')),k10_relat_1(C_60,'#skF_2'))
      | ~ v1_relat_1(C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_531])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2704,plain,(
    ! [C_163] :
      ( k2_xboole_0(k10_relat_1(C_163,k9_relat_1('#skF_3','#skF_1')),k10_relat_1(C_163,'#skF_2')) = k10_relat_1(C_163,'#skF_2')
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_565,c_4])).

tff(c_152,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k10_relat_1(B_29,k9_relat_1(B_29,A_28)))
      | ~ r1_tarski(A_28,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1292,plain,(
    ! [A_100,B_101] :
      ( k2_xboole_0(A_100,k10_relat_1(B_101,k9_relat_1(B_101,A_100))) = k10_relat_1(B_101,k9_relat_1(B_101,A_100))
      | ~ r1_tarski(A_100,k1_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_152,c_4])).

tff(c_51,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(k2_xboole_0(A_17,B_19),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_17,B_19,B_7] : r1_tarski(A_17,k2_xboole_0(k2_xboole_0(A_17,B_19),B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_1464,plain,(
    ! [A_100,B_101,B_7] :
      ( r1_tarski(A_100,k2_xboole_0(k10_relat_1(B_101,k9_relat_1(B_101,A_100)),B_7))
      | ~ r1_tarski(A_100,k1_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_62])).

tff(c_2714,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2704,c_1464])).

tff(c_2783,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_16,c_2714])).

tff(c_2785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_2783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:13:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.74  
% 4.47/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.74  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.47/1.74  
% 4.47/1.74  %Foreground sorts:
% 4.47/1.74  
% 4.47/1.74  
% 4.47/1.74  %Background operators:
% 4.47/1.74  
% 4.47/1.74  
% 4.47/1.74  %Foreground operators:
% 4.47/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.47/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.47/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.47/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.74  
% 4.47/1.75  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.47/1.75  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.47/1.75  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 4.47/1.75  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.47/1.75  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.47/1.75  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.47/1.75  tff(c_12, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.75  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.75  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.75  tff(c_14, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.75  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.75  tff(c_33, plain, (k2_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_22])).
% 4.47/1.75  tff(c_405, plain, (![C_47, A_48, B_49]: (k2_xboole_0(k10_relat_1(C_47, A_48), k10_relat_1(C_47, B_49))=k10_relat_1(C_47, k2_xboole_0(A_48, B_49)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.47/1.75  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.75  tff(c_531, plain, (![C_56, A_57, B_58]: (r1_tarski(k10_relat_1(C_56, A_57), k10_relat_1(C_56, k2_xboole_0(A_57, B_58))) | ~v1_relat_1(C_56))), inference(superposition, [status(thm), theory('equality')], [c_405, c_6])).
% 4.47/1.75  tff(c_565, plain, (![C_60]: (r1_tarski(k10_relat_1(C_60, k9_relat_1('#skF_3', '#skF_1')), k10_relat_1(C_60, '#skF_2')) | ~v1_relat_1(C_60))), inference(superposition, [status(thm), theory('equality')], [c_33, c_531])).
% 4.47/1.75  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.75  tff(c_2704, plain, (![C_163]: (k2_xboole_0(k10_relat_1(C_163, k9_relat_1('#skF_3', '#skF_1')), k10_relat_1(C_163, '#skF_2'))=k10_relat_1(C_163, '#skF_2') | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_565, c_4])).
% 4.47/1.75  tff(c_152, plain, (![A_28, B_29]: (r1_tarski(A_28, k10_relat_1(B_29, k9_relat_1(B_29, A_28))) | ~r1_tarski(A_28, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.47/1.75  tff(c_1292, plain, (![A_100, B_101]: (k2_xboole_0(A_100, k10_relat_1(B_101, k9_relat_1(B_101, A_100)))=k10_relat_1(B_101, k9_relat_1(B_101, A_100)) | ~r1_tarski(A_100, k1_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_152, c_4])).
% 4.47/1.75  tff(c_51, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(k2_xboole_0(A_17, B_19), C_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.75  tff(c_62, plain, (![A_17, B_19, B_7]: (r1_tarski(A_17, k2_xboole_0(k2_xboole_0(A_17, B_19), B_7)))), inference(resolution, [status(thm)], [c_6, c_51])).
% 4.47/1.75  tff(c_1464, plain, (![A_100, B_101, B_7]: (r1_tarski(A_100, k2_xboole_0(k10_relat_1(B_101, k9_relat_1(B_101, A_100)), B_7)) | ~r1_tarski(A_100, k1_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_62])).
% 4.47/1.75  tff(c_2714, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2704, c_1464])).
% 4.47/1.75  tff(c_2783, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_16, c_2714])).
% 4.47/1.75  tff(c_2785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_2783])).
% 4.47/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.75  
% 4.47/1.75  Inference rules
% 4.47/1.75  ----------------------
% 4.47/1.75  #Ref     : 0
% 4.47/1.75  #Sup     : 691
% 4.47/1.75  #Fact    : 0
% 4.47/1.75  #Define  : 0
% 4.47/1.75  #Split   : 1
% 4.47/1.75  #Chain   : 0
% 4.47/1.75  #Close   : 0
% 4.47/1.75  
% 4.47/1.75  Ordering : KBO
% 4.47/1.75  
% 4.47/1.75  Simplification rules
% 4.47/1.75  ----------------------
% 4.47/1.75  #Subsume      : 100
% 4.47/1.75  #Demod        : 174
% 4.47/1.75  #Tautology    : 178
% 4.47/1.75  #SimpNegUnit  : 1
% 4.47/1.75  #BackRed      : 0
% 4.47/1.75  
% 4.47/1.75  #Partial instantiations: 0
% 4.47/1.75  #Strategies tried      : 1
% 4.47/1.75  
% 4.47/1.75  Timing (in seconds)
% 4.47/1.75  ----------------------
% 4.47/1.75  Preprocessing        : 0.28
% 4.47/1.75  Parsing              : 0.16
% 4.47/1.75  CNF conversion       : 0.02
% 4.47/1.75  Main loop            : 0.77
% 4.47/1.75  Inferencing          : 0.27
% 4.47/1.75  Reduction            : 0.27
% 4.47/1.75  Demodulation         : 0.21
% 4.47/1.75  BG Simplification    : 0.03
% 4.47/1.75  Subsumption          : 0.15
% 4.47/1.75  Abstraction          : 0.04
% 4.47/1.75  MUC search           : 0.00
% 4.47/1.75  Cooper               : 0.00
% 4.47/1.75  Total                : 1.07
% 4.47/1.75  Index Insertion      : 0.00
% 4.47/1.75  Index Deletion       : 0.00
% 4.47/1.75  Index Matching       : 0.00
% 4.47/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
