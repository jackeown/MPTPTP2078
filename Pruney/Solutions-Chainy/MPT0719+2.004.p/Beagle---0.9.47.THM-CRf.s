%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:43 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 (  76 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_24] :
      ( v1_relat_1(A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_38,plain,(
    ! [A_25] :
      ( v1_funct_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_26,plain,(
    ! [A_14,B_20] :
      ( r2_hidden('#skF_3'(A_14,B_20),k1_relat_1(B_20))
      | v5_funct_1(B_20,A_14)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_128,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(k4_tarski(A_50,'#skF_2'(A_50,B_51,C_52)),C_52)
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [C_53,A_54,B_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ r2_hidden(A_54,k10_relat_1(C_53,B_55))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_216,plain,(
    ! [A_75,A_76] :
      ( ~ v1_xboole_0(A_75)
      | ~ r2_hidden(A_76,k1_relat_1(A_75))
      | ~ v1_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_143])).

tff(c_410,plain,(
    ! [B_136,A_137] :
      ( ~ v1_xboole_0(B_136)
      | v5_funct_1(B_136,A_137)
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_26,c_216])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_413,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_410,c_28])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_37,c_42,c_6,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.35  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.55/1.35  
% 2.55/1.35  %Foreground sorts:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Background operators:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Foreground operators:
% 2.55/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.55/1.35  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.55/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.55/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.35  
% 2.55/1.36  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.55/1.36  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.36  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.55/1.36  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.55/1.36  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.55/1.36  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.55/1.36  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.55/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.55/1.36  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.36  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.36  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.36  tff(c_33, plain, (![A_24]: (v1_relat_1(A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.36  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_33])).
% 2.55/1.36  tff(c_38, plain, (![A_25]: (v1_funct_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.36  tff(c_42, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.55/1.36  tff(c_26, plain, (![A_14, B_20]: (r2_hidden('#skF_3'(A_14, B_20), k1_relat_1(B_20)) | v5_funct_1(B_20, A_14) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.36  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.55/1.36  tff(c_128, plain, (![A_50, B_51, C_52]: (r2_hidden(k4_tarski(A_50, '#skF_2'(A_50, B_51, C_52)), C_52) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.36  tff(c_143, plain, (![C_53, A_54, B_55]: (~v1_xboole_0(C_53) | ~r2_hidden(A_54, k10_relat_1(C_53, B_55)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_128, c_2])).
% 2.55/1.36  tff(c_216, plain, (![A_75, A_76]: (~v1_xboole_0(A_75) | ~r2_hidden(A_76, k1_relat_1(A_75)) | ~v1_relat_1(A_75) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_18, c_143])).
% 2.55/1.36  tff(c_410, plain, (![B_136, A_137]: (~v1_xboole_0(B_136) | v5_funct_1(B_136, A_137) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_26, c_216])).
% 2.55/1.36  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.36  tff(c_413, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_410, c_28])).
% 2.55/1.36  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_37, c_42, c_6, c_413])).
% 2.55/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  Inference rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Ref     : 0
% 2.55/1.36  #Sup     : 82
% 2.55/1.36  #Fact    : 0
% 2.55/1.36  #Define  : 0
% 2.55/1.36  #Split   : 0
% 2.55/1.36  #Chain   : 0
% 2.55/1.36  #Close   : 0
% 2.55/1.36  
% 2.55/1.36  Ordering : KBO
% 2.55/1.36  
% 2.55/1.36  Simplification rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Subsume      : 10
% 2.55/1.36  #Demod        : 5
% 2.55/1.36  #Tautology    : 4
% 2.55/1.36  #SimpNegUnit  : 0
% 2.55/1.36  #BackRed      : 0
% 2.55/1.36  
% 2.55/1.36  #Partial instantiations: 0
% 2.55/1.36  #Strategies tried      : 1
% 2.55/1.36  
% 2.55/1.36  Timing (in seconds)
% 2.55/1.36  ----------------------
% 2.55/1.37  Preprocessing        : 0.28
% 2.55/1.37  Parsing              : 0.15
% 2.55/1.37  CNF conversion       : 0.02
% 2.55/1.37  Main loop            : 0.32
% 2.55/1.37  Inferencing          : 0.14
% 2.55/1.37  Reduction            : 0.06
% 2.55/1.37  Demodulation         : 0.04
% 2.55/1.37  BG Simplification    : 0.02
% 2.55/1.37  Subsumption          : 0.08
% 2.55/1.37  Abstraction          : 0.01
% 2.55/1.37  MUC search           : 0.00
% 2.55/1.37  Cooper               : 0.00
% 2.55/1.37  Total                : 0.63
% 2.55/1.37  Index Insertion      : 0.00
% 2.55/1.37  Index Deletion       : 0.00
% 2.55/1.37  Index Matching       : 0.00
% 2.55/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
