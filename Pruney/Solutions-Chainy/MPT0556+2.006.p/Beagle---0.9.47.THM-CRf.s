%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 16.57s
% Output     : CNFRefutation 16.57s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_85,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_22,plain,(
    ! [B_22,A_21,C_24] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k9_relat_1(C_24,A_21))
      | ~ r1_tarski(B_22,C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_854,plain,(
    ! [C_77,A_78,B_79] :
      ( k2_xboole_0(k9_relat_1(C_77,A_78),k9_relat_1(C_77,B_79)) = k9_relat_1(C_77,k2_xboole_0(A_78,B_79))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7327,plain,(
    ! [C_170,A_171,C_172,B_173] :
      ( r1_tarski(k9_relat_1(C_170,A_171),C_172)
      | ~ r1_tarski(k9_relat_1(C_170,k2_xboole_0(A_171,B_173)),C_172)
      | ~ v1_relat_1(C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_10])).

tff(c_67180,plain,(
    ! [B_578,A_579,C_580,B_581] :
      ( r1_tarski(k9_relat_1(B_578,A_579),k9_relat_1(C_580,k2_xboole_0(A_579,B_581)))
      | ~ r1_tarski(B_578,C_580)
      | ~ v1_relat_1(C_580)
      | ~ v1_relat_1(B_578) ) ),
    inference(resolution,[status(thm)],[c_22,c_7327])).

tff(c_71101,plain,(
    ! [B_594,C_595] :
      ( r1_tarski(k9_relat_1(B_594,'#skF_1'),k9_relat_1(C_595,'#skF_2'))
      | ~ r1_tarski(B_594,C_595)
      | ~ v1_relat_1(C_595)
      | ~ v1_relat_1(B_594) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_67180])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71111,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71101,c_24])).

tff(c_71118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_71111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.57/9.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.57/9.36  
% 16.57/9.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.57/9.36  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.57/9.36  
% 16.57/9.36  %Foreground sorts:
% 16.57/9.36  
% 16.57/9.36  
% 16.57/9.36  %Background operators:
% 16.57/9.36  
% 16.57/9.36  
% 16.57/9.36  %Foreground operators:
% 16.57/9.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.57/9.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.57/9.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.57/9.36  tff('#skF_2', type, '#skF_2': $i).
% 16.57/9.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.57/9.36  tff('#skF_3', type, '#skF_3': $i).
% 16.57/9.36  tff('#skF_1', type, '#skF_1': $i).
% 16.57/9.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.57/9.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.57/9.36  tff('#skF_4', type, '#skF_4': $i).
% 16.57/9.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.57/9.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.57/9.36  
% 16.57/9.37  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 16.57/9.37  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.57/9.37  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 16.57/9.37  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 16.57/9.37  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 16.57/9.37  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.57/9.37  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.57/9.37  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.57/9.37  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.57/9.37  tff(c_85, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.57/9.37  tff(c_105, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_85])).
% 16.57/9.37  tff(c_22, plain, (![B_22, A_21, C_24]: (r1_tarski(k9_relat_1(B_22, A_21), k9_relat_1(C_24, A_21)) | ~r1_tarski(B_22, C_24) | ~v1_relat_1(C_24) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.57/9.37  tff(c_854, plain, (![C_77, A_78, B_79]: (k2_xboole_0(k9_relat_1(C_77, A_78), k9_relat_1(C_77, B_79))=k9_relat_1(C_77, k2_xboole_0(A_78, B_79)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.57/9.37  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.57/9.37  tff(c_7327, plain, (![C_170, A_171, C_172, B_173]: (r1_tarski(k9_relat_1(C_170, A_171), C_172) | ~r1_tarski(k9_relat_1(C_170, k2_xboole_0(A_171, B_173)), C_172) | ~v1_relat_1(C_170))), inference(superposition, [status(thm), theory('equality')], [c_854, c_10])).
% 16.57/9.37  tff(c_67180, plain, (![B_578, A_579, C_580, B_581]: (r1_tarski(k9_relat_1(B_578, A_579), k9_relat_1(C_580, k2_xboole_0(A_579, B_581))) | ~r1_tarski(B_578, C_580) | ~v1_relat_1(C_580) | ~v1_relat_1(B_578))), inference(resolution, [status(thm)], [c_22, c_7327])).
% 16.57/9.37  tff(c_71101, plain, (![B_594, C_595]: (r1_tarski(k9_relat_1(B_594, '#skF_1'), k9_relat_1(C_595, '#skF_2')) | ~r1_tarski(B_594, C_595) | ~v1_relat_1(C_595) | ~v1_relat_1(B_594))), inference(superposition, [status(thm), theory('equality')], [c_105, c_67180])).
% 16.57/9.37  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.57/9.37  tff(c_71111, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71101, c_24])).
% 16.57/9.37  tff(c_71118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_71111])).
% 16.57/9.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.57/9.37  
% 16.57/9.37  Inference rules
% 16.57/9.37  ----------------------
% 16.57/9.37  #Ref     : 0
% 16.57/9.37  #Sup     : 17049
% 16.57/9.37  #Fact    : 0
% 16.57/9.37  #Define  : 0
% 16.57/9.37  #Split   : 4
% 16.57/9.37  #Chain   : 0
% 16.57/9.37  #Close   : 0
% 16.57/9.37  
% 16.57/9.37  Ordering : KBO
% 16.57/9.37  
% 16.57/9.37  Simplification rules
% 16.57/9.37  ----------------------
% 16.57/9.37  #Subsume      : 1987
% 16.57/9.37  #Demod        : 13216
% 16.57/9.37  #Tautology    : 9454
% 16.57/9.37  #SimpNegUnit  : 0
% 16.57/9.37  #BackRed      : 22
% 16.57/9.37  
% 16.57/9.37  #Partial instantiations: 0
% 16.57/9.37  #Strategies tried      : 1
% 16.57/9.37  
% 16.57/9.37  Timing (in seconds)
% 16.57/9.37  ----------------------
% 16.57/9.37  Preprocessing        : 0.29
% 16.57/9.37  Parsing              : 0.16
% 16.57/9.37  CNF conversion       : 0.02
% 16.57/9.37  Main loop            : 8.33
% 16.57/9.37  Inferencing          : 1.19
% 16.57/9.37  Reduction            : 4.88
% 16.57/9.37  Demodulation         : 4.41
% 16.57/9.37  BG Simplification    : 0.13
% 16.57/9.37  Subsumption          : 1.78
% 16.57/9.37  Abstraction          : 0.22
% 16.57/9.37  MUC search           : 0.00
% 16.57/9.38  Cooper               : 0.00
% 16.57/9.38  Total                : 8.64
% 16.57/9.38  Index Insertion      : 0.00
% 16.57/9.38  Index Deletion       : 0.00
% 16.57/9.38  Index Matching       : 0.00
% 16.57/9.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
