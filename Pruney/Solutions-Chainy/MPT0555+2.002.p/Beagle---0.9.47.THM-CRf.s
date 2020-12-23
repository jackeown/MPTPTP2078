%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   41 (  89 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 216 expanded)
%              Number of equality atoms :    3 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7,A_5,D_9,B_6] :
      ( r1_tarski(k7_relat_1(C_7,A_5),k7_relat_1(D_9,B_6))
      | ~ r1_tarski(A_5,B_6)
      | ~ r1_tarski(C_7,D_9)
      | ~ v1_relat_1(D_9)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k2_relat_1(A_23),k2_relat_1(B_24))
      | ~ r1_tarski(A_23,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [B_42,A_43,B_44] :
      ( r1_tarski(k9_relat_1(B_42,A_43),k2_relat_1(B_44))
      | ~ r1_tarski(k7_relat_1(B_42,A_43),B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_344,plain,(
    ! [B_87,A_88,B_89,A_90] :
      ( r1_tarski(k9_relat_1(B_87,A_88),k9_relat_1(B_89,A_90))
      | ~ r1_tarski(k7_relat_1(B_87,A_88),k7_relat_1(B_89,A_90))
      | ~ v1_relat_1(k7_relat_1(B_89,A_90))
      | ~ v1_relat_1(k7_relat_1(B_87,A_88))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_357,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_18])).

tff(c_365,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_357])).

tff(c_366,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_369,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_366])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_369])).

tff(c_374,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_376,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_379,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_376])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_6,c_379])).

tff(c_384,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_388,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_384])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:18:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.33  
% 2.40/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.33  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.33  
% 2.40/1.33  %Foreground sorts:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Background operators:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Foreground operators:
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.40/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.40/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.33  
% 2.70/1.35  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 2.70/1.35  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.70/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.35  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 2.70/1.35  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.70/1.35  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.70/1.35  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.35  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.35  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.35  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.35  tff(c_10, plain, (![C_7, A_5, D_9, B_6]: (r1_tarski(k7_relat_1(C_7, A_5), k7_relat_1(D_9, B_6)) | ~r1_tarski(A_5, B_6) | ~r1_tarski(C_7, D_9) | ~v1_relat_1(D_9) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.35  tff(c_12, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.35  tff(c_48, plain, (![A_23, B_24]: (r1_tarski(k2_relat_1(A_23), k2_relat_1(B_24)) | ~r1_tarski(A_23, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.35  tff(c_153, plain, (![B_42, A_43, B_44]: (r1_tarski(k9_relat_1(B_42, A_43), k2_relat_1(B_44)) | ~r1_tarski(k7_relat_1(B_42, A_43), B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_48])).
% 2.70/1.35  tff(c_344, plain, (![B_87, A_88, B_89, A_90]: (r1_tarski(k9_relat_1(B_87, A_88), k9_relat_1(B_89, A_90)) | ~r1_tarski(k7_relat_1(B_87, A_88), k7_relat_1(B_89, A_90)) | ~v1_relat_1(k7_relat_1(B_89, A_90)) | ~v1_relat_1(k7_relat_1(B_87, A_88)) | ~v1_relat_1(B_87) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_12, c_153])).
% 2.70/1.35  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.35  tff(c_357, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_344, c_18])).
% 2.70/1.35  tff(c_365, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_357])).
% 2.70/1.35  tff(c_366, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_365])).
% 2.70/1.35  tff(c_369, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_366])).
% 2.70/1.35  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_369])).
% 2.70/1.35  tff(c_374, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_365])).
% 2.70/1.35  tff(c_376, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_374])).
% 2.70/1.35  tff(c_379, plain, (~r1_tarski('#skF_1', '#skF_1') | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_376])).
% 2.70/1.35  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_6, c_379])).
% 2.70/1.35  tff(c_384, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_374])).
% 2.70/1.35  tff(c_388, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_384])).
% 2.70/1.35  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_388])).
% 2.70/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  Inference rules
% 2.70/1.35  ----------------------
% 2.70/1.35  #Ref     : 0
% 2.70/1.35  #Sup     : 82
% 2.70/1.35  #Fact    : 0
% 2.70/1.35  #Define  : 0
% 2.70/1.35  #Split   : 3
% 2.70/1.35  #Chain   : 0
% 2.70/1.35  #Close   : 0
% 2.70/1.35  
% 2.70/1.35  Ordering : KBO
% 2.70/1.35  
% 2.70/1.35  Simplification rules
% 2.70/1.35  ----------------------
% 2.70/1.35  #Subsume      : 8
% 2.70/1.35  #Demod        : 29
% 2.70/1.35  #Tautology    : 14
% 2.70/1.35  #SimpNegUnit  : 0
% 2.70/1.35  #BackRed      : 0
% 2.70/1.35  
% 2.70/1.35  #Partial instantiations: 0
% 2.70/1.35  #Strategies tried      : 1
% 2.70/1.35  
% 2.70/1.35  Timing (in seconds)
% 2.70/1.35  ----------------------
% 2.70/1.35  Preprocessing        : 0.28
% 2.70/1.35  Parsing              : 0.15
% 2.70/1.35  CNF conversion       : 0.02
% 2.70/1.35  Main loop            : 0.32
% 2.70/1.35  Inferencing          : 0.12
% 2.70/1.35  Reduction            : 0.07
% 2.70/1.35  Demodulation         : 0.05
% 2.70/1.35  BG Simplification    : 0.02
% 2.70/1.35  Subsumption          : 0.09
% 2.70/1.35  Abstraction          : 0.02
% 2.70/1.35  MUC search           : 0.00
% 2.70/1.35  Cooper               : 0.00
% 2.70/1.35  Total                : 0.62
% 2.70/1.35  Index Insertion      : 0.00
% 2.70/1.35  Index Deletion       : 0.00
% 2.70/1.35  Index Matching       : 0.00
% 2.70/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
