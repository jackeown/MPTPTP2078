%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 12.25s
% Output     : CNFRefutation 12.25s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [B_27,A_26,C_29] :
      ( r1_tarski(k9_relat_1(B_27,A_26),k9_relat_1(C_29,A_26))
      | ~ r1_tarski(B_27,C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_1918,plain,(
    ! [C_115,A_116,B_117] :
      ( k2_xboole_0(k9_relat_1(C_115,A_116),k9_relat_1(C_115,B_117)) = k9_relat_1(C_115,k2_xboole_0(A_116,B_117))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,C_18)
      | ~ r1_tarski(k2_xboole_0(A_16,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_17028,plain,(
    ! [C_361,A_362,C_363,B_364] :
      ( r1_tarski(k9_relat_1(C_361,A_362),C_363)
      | ~ r1_tarski(k9_relat_1(C_361,k2_xboole_0(A_362,B_364)),C_363)
      | ~ v1_relat_1(C_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1918,c_34])).

tff(c_17253,plain,(
    ! [C_365,C_366] :
      ( r1_tarski(k9_relat_1(C_365,'#skF_4'),C_366)
      | ~ r1_tarski(k9_relat_1(C_365,'#skF_5'),C_366)
      | ~ v1_relat_1(C_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_17028])).

tff(c_23370,plain,(
    ! [B_512,C_513] :
      ( r1_tarski(k9_relat_1(B_512,'#skF_4'),k9_relat_1(C_513,'#skF_5'))
      | ~ r1_tarski(B_512,C_513)
      | ~ v1_relat_1(C_513)
      | ~ v1_relat_1(B_512) ) ),
    inference(resolution,[status(thm)],[c_42,c_17253])).

tff(c_44,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_23378,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_23370,c_44])).

tff(c_23384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_23378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.25/4.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.25/4.70  
% 12.25/4.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.25/4.70  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 12.25/4.70  
% 12.25/4.70  %Foreground sorts:
% 12.25/4.70  
% 12.25/4.70  
% 12.25/4.70  %Background operators:
% 12.25/4.70  
% 12.25/4.70  
% 12.25/4.70  %Foreground operators:
% 12.25/4.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.25/4.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.25/4.70  tff('#skF_7', type, '#skF_7': $i).
% 12.25/4.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.25/4.70  tff('#skF_5', type, '#skF_5': $i).
% 12.25/4.70  tff('#skF_6', type, '#skF_6': $i).
% 12.25/4.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.25/4.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.25/4.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.25/4.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.25/4.70  tff('#skF_4', type, '#skF_4': $i).
% 12.25/4.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.25/4.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.25/4.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.25/4.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.25/4.70  
% 12.25/4.71  tff(f_84, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 12.25/4.71  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 12.25/4.71  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.25/4.71  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 12.25/4.71  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.25/4.71  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.25/4.71  tff(c_50, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.25/4.71  tff(c_48, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.25/4.71  tff(c_42, plain, (![B_27, A_26, C_29]: (r1_tarski(k9_relat_1(B_27, A_26), k9_relat_1(C_29, A_26)) | ~r1_tarski(B_27, C_29) | ~v1_relat_1(C_29) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.25/4.71  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.25/4.71  tff(c_105, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.25/4.71  tff(c_125, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_105])).
% 12.25/4.71  tff(c_1918, plain, (![C_115, A_116, B_117]: (k2_xboole_0(k9_relat_1(C_115, A_116), k9_relat_1(C_115, B_117))=k9_relat_1(C_115, k2_xboole_0(A_116, B_117)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.25/4.71  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, C_18) | ~r1_tarski(k2_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.25/4.71  tff(c_17028, plain, (![C_361, A_362, C_363, B_364]: (r1_tarski(k9_relat_1(C_361, A_362), C_363) | ~r1_tarski(k9_relat_1(C_361, k2_xboole_0(A_362, B_364)), C_363) | ~v1_relat_1(C_361))), inference(superposition, [status(thm), theory('equality')], [c_1918, c_34])).
% 12.25/4.71  tff(c_17253, plain, (![C_365, C_366]: (r1_tarski(k9_relat_1(C_365, '#skF_4'), C_366) | ~r1_tarski(k9_relat_1(C_365, '#skF_5'), C_366) | ~v1_relat_1(C_365))), inference(superposition, [status(thm), theory('equality')], [c_125, c_17028])).
% 12.25/4.71  tff(c_23370, plain, (![B_512, C_513]: (r1_tarski(k9_relat_1(B_512, '#skF_4'), k9_relat_1(C_513, '#skF_5')) | ~r1_tarski(B_512, C_513) | ~v1_relat_1(C_513) | ~v1_relat_1(B_512))), inference(resolution, [status(thm)], [c_42, c_17253])).
% 12.25/4.71  tff(c_44, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.25/4.71  tff(c_23378, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_23370, c_44])).
% 12.25/4.71  tff(c_23384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_23378])).
% 12.25/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.25/4.71  
% 12.25/4.71  Inference rules
% 12.25/4.71  ----------------------
% 12.25/4.71  #Ref     : 0
% 12.25/4.71  #Sup     : 5573
% 12.25/4.71  #Fact    : 12
% 12.25/4.71  #Define  : 0
% 12.25/4.71  #Split   : 6
% 12.25/4.71  #Chain   : 0
% 12.25/4.71  #Close   : 0
% 12.25/4.71  
% 12.25/4.71  Ordering : KBO
% 12.25/4.71  
% 12.25/4.71  Simplification rules
% 12.25/4.71  ----------------------
% 12.25/4.71  #Subsume      : 1098
% 12.25/4.71  #Demod        : 4638
% 12.25/4.71  #Tautology    : 2593
% 12.25/4.71  #SimpNegUnit  : 0
% 12.25/4.71  #BackRed      : 0
% 12.25/4.71  
% 12.25/4.71  #Partial instantiations: 0
% 12.25/4.71  #Strategies tried      : 1
% 12.25/4.71  
% 12.25/4.71  Timing (in seconds)
% 12.25/4.71  ----------------------
% 12.25/4.71  Preprocessing        : 0.29
% 12.25/4.71  Parsing              : 0.16
% 12.25/4.71  CNF conversion       : 0.02
% 12.25/4.71  Main loop            : 3.66
% 12.25/4.71  Inferencing          : 0.73
% 12.25/4.71  Reduction            : 1.77
% 12.25/4.71  Demodulation         : 1.51
% 12.25/4.71  BG Simplification    : 0.08
% 12.25/4.71  Subsumption          : 0.87
% 12.25/4.71  Abstraction          : 0.11
% 12.25/4.71  MUC search           : 0.00
% 12.25/4.71  Cooper               : 0.00
% 12.25/4.71  Total                : 3.97
% 12.25/4.71  Index Insertion      : 0.00
% 12.25/4.71  Index Deletion       : 0.00
% 12.25/4.71  Index Matching       : 0.00
% 12.25/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
