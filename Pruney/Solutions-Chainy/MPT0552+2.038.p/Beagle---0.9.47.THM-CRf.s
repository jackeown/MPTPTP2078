%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  66 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 130 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [C_17,A_18,B_19] :
      ( k3_xboole_0(k7_relat_1(C_17,A_18),k7_relat_1(C_17,B_19)) = k7_relat_1(C_17,k3_xboole_0(A_18,B_19))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_8,B_10)),k3_xboole_0(k2_relat_1(A_8),k2_relat_1(B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    ! [C_26,A_27,B_28] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_26,k3_xboole_0(A_27,B_28))),k3_xboole_0(k2_relat_1(k7_relat_1(C_26,A_27)),k2_relat_1(k7_relat_1(C_26,B_28))))
      | ~ v1_relat_1(k7_relat_1(C_26,B_28))
      | ~ v1_relat_1(k7_relat_1(C_26,A_27))
      | ~ v1_relat_1(C_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_92,plain,(
    ! [B_35,A_36,B_37] :
      ( r1_tarski(k9_relat_1(B_35,k3_xboole_0(A_36,B_37)),k3_xboole_0(k2_relat_1(k7_relat_1(B_35,A_36)),k2_relat_1(k7_relat_1(B_35,B_37))))
      | ~ v1_relat_1(k7_relat_1(B_35,B_37))
      | ~ v1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_114,plain,(
    ! [B_45,A_46,B_47] :
      ( r1_tarski(k9_relat_1(B_45,k3_xboole_0(A_46,B_47)),k3_xboole_0(k9_relat_1(B_45,A_46),k2_relat_1(k7_relat_1(B_45,B_47))))
      | ~ v1_relat_1(k7_relat_1(B_45,B_47))
      | ~ v1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_128,plain,(
    ! [B_51,A_52,A_53] :
      ( r1_tarski(k9_relat_1(B_51,k3_xboole_0(A_52,A_53)),k3_xboole_0(k9_relat_1(B_51,A_52),k9_relat_1(B_51,A_53)))
      | ~ v1_relat_1(k7_relat_1(B_51,A_53))
      | ~ v1_relat_1(k7_relat_1(B_51,A_52))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_10,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_10])).

tff(c_137,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_138,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_157,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_138])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_157])).

tff(c_162,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_166,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_162])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:42:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.23  
% 2.19/1.24  tff(f_49, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 2.19/1.24  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.19/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.19/1.24  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 2.19/1.24  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.19/1.24  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.24  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.24  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.24  tff(c_30, plain, (![C_17, A_18, B_19]: (k3_xboole_0(k7_relat_1(C_17, A_18), k7_relat_1(C_17, B_19))=k7_relat_1(C_17, k3_xboole_0(A_18, B_19)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.24  tff(c_8, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k3_xboole_0(A_8, B_10)), k3_xboole_0(k2_relat_1(A_8), k2_relat_1(B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.24  tff(c_56, plain, (![C_26, A_27, B_28]: (r1_tarski(k2_relat_1(k7_relat_1(C_26, k3_xboole_0(A_27, B_28))), k3_xboole_0(k2_relat_1(k7_relat_1(C_26, A_27)), k2_relat_1(k7_relat_1(C_26, B_28)))) | ~v1_relat_1(k7_relat_1(C_26, B_28)) | ~v1_relat_1(k7_relat_1(C_26, A_27)) | ~v1_relat_1(C_26))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 2.19/1.24  tff(c_92, plain, (![B_35, A_36, B_37]: (r1_tarski(k9_relat_1(B_35, k3_xboole_0(A_36, B_37)), k3_xboole_0(k2_relat_1(k7_relat_1(B_35, A_36)), k2_relat_1(k7_relat_1(B_35, B_37)))) | ~v1_relat_1(k7_relat_1(B_35, B_37)) | ~v1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_56])).
% 2.19/1.24  tff(c_114, plain, (![B_45, A_46, B_47]: (r1_tarski(k9_relat_1(B_45, k3_xboole_0(A_46, B_47)), k3_xboole_0(k9_relat_1(B_45, A_46), k2_relat_1(k7_relat_1(B_45, B_47)))) | ~v1_relat_1(k7_relat_1(B_45, B_47)) | ~v1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45) | ~v1_relat_1(B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_92])).
% 2.19/1.24  tff(c_128, plain, (![B_51, A_52, A_53]: (r1_tarski(k9_relat_1(B_51, k3_xboole_0(A_52, A_53)), k3_xboole_0(k9_relat_1(B_51, A_52), k9_relat_1(B_51, A_53))) | ~v1_relat_1(k7_relat_1(B_51, A_53)) | ~v1_relat_1(k7_relat_1(B_51, A_52)) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 2.19/1.24  tff(c_10, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.24  tff(c_131, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_10])).
% 2.19/1.24  tff(c_137, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 2.19/1.24  tff(c_138, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.19/1.24  tff(c_157, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_138])).
% 2.19/1.24  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_157])).
% 2.19/1.24  tff(c_162, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_137])).
% 2.19/1.24  tff(c_166, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_162])).
% 2.19/1.24  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 39
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 1
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 7
% 2.19/1.24  #Demod        : 3
% 2.19/1.24  #Tautology    : 4
% 2.19/1.24  #SimpNegUnit  : 0
% 2.19/1.24  #BackRed      : 0
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.24  Preprocessing        : 0.25
% 2.19/1.24  Parsing              : 0.14
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.21
% 2.19/1.24  Inferencing          : 0.09
% 2.19/1.24  Reduction            : 0.05
% 2.19/1.24  Demodulation         : 0.04
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.05
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.49
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
