%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:39 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   51 (  96 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 151 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_22])).

tff(c_127,plain,(
    ! [B_20,A_21] :
      ( k3_xboole_0(k1_relat_1(B_20),A_21) = k1_relat_1(k7_relat_1(B_20,A_21))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_133,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_86])).

tff(c_159,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_8)) = k3_xboole_0(k1_xboole_0,A_8)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_18])).

tff(c_219,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_222,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_228,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_234,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_228,c_16])).

tff(c_240,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_234])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_240])).

tff(c_243,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_290,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k1_relat_1(B_27),A_28) = k1_relat_1(k7_relat_1(B_27,A_28))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_330,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,k1_relat_1(B_31)) = k1_relat_1(k7_relat_1(B_31,A_30))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_278,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_281,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_278,c_244])).

tff(c_286,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_340,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_286])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_243,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:30:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.30  
% 2.06/1.31  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.06/1.31  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.06/1.31  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.06/1.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.06/1.31  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.06/1.31  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.06/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.06/1.31  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.31  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_28, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.31  tff(c_82, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.06/1.31  tff(c_22, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.31  tff(c_121, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_22])).
% 2.06/1.31  tff(c_127, plain, (![B_20, A_21]: (k3_xboole_0(k1_relat_1(B_20), A_21)=k1_relat_1(k7_relat_1(B_20, A_21)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.31  tff(c_86, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_4])).
% 2.06/1.31  tff(c_133, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_86])).
% 2.06/1.31  tff(c_159, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_133])).
% 2.06/1.31  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.31  tff(c_18, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_166, plain, (![A_8]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_8))=k3_xboole_0(k1_xboole_0, A_8) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_159, c_18])).
% 2.06/1.31  tff(c_219, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.06/1.31  tff(c_222, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.06/1.31  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_222])).
% 2.06/1.31  tff(c_228, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_166])).
% 2.06/1.31  tff(c_16, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.31  tff(c_234, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_228, c_16])).
% 2.06/1.31  tff(c_240, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_159, c_234])).
% 2.06/1.31  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_240])).
% 2.06/1.31  tff(c_243, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.06/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.31  tff(c_290, plain, (![B_27, A_28]: (k3_xboole_0(k1_relat_1(B_27), A_28)=k1_relat_1(k7_relat_1(B_27, A_28)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_330, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k1_relat_1(B_31))=k1_relat_1(k7_relat_1(B_31, A_30)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_290])).
% 2.06/1.31  tff(c_278, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.31  tff(c_244, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.06/1.31  tff(c_281, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_278, c_244])).
% 2.06/1.31  tff(c_286, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_281])).
% 2.06/1.31  tff(c_340, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_330, c_286])).
% 2.06/1.31  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_243, c_340])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 83
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 6
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.32  Simplification rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Subsume      : 8
% 2.06/1.32  #Demod        : 22
% 2.06/1.32  #Tautology    : 41
% 2.06/1.32  #SimpNegUnit  : 2
% 2.06/1.32  #BackRed      : 0
% 2.06/1.32  
% 2.06/1.32  #Partial instantiations: 0
% 2.06/1.32  #Strategies tried      : 1
% 2.06/1.32  
% 2.06/1.32  Timing (in seconds)
% 2.06/1.32  ----------------------
% 2.06/1.32  Preprocessing        : 0.28
% 2.06/1.32  Parsing              : 0.16
% 2.06/1.32  CNF conversion       : 0.01
% 2.06/1.32  Main loop            : 0.20
% 2.06/1.32  Inferencing          : 0.07
% 2.06/1.32  Reduction            : 0.06
% 2.06/1.32  Demodulation         : 0.05
% 2.06/1.32  BG Simplification    : 0.01
% 2.06/1.32  Subsumption          : 0.04
% 2.06/1.32  Abstraction          : 0.01
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.51
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
