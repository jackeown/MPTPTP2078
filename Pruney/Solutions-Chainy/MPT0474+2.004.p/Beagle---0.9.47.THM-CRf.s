%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  54 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_65,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    ! [A_27] :
      ( v1_relat_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_26,plain,(
    ! [A_23] :
      ( v1_relat_1(k4_relat_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | r2_hidden(k4_tarski('#skF_5'(A_24),'#skF_6'(A_24)),A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,(
    ! [D_40,C_41,A_42] :
      ( r2_hidden(k4_tarski(D_40,C_41),A_42)
      | ~ r2_hidden(k4_tarski(C_41,D_40),k4_relat_1(A_42))
      | ~ v1_relat_1(k4_relat_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_43] :
      ( r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_43)),'#skF_5'(k4_relat_1(A_43))),A_43)
      | ~ v1_relat_1(A_43)
      | k4_relat_1(A_43) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_53,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | k4_xboole_0(A_32,k1_tarski(B_31)) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [B_31] : ~ r2_hidden(B_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_113,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_105,c_58])).

tff(c_117,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_113])).

tff(c_118,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_117])).

tff(c_121,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.78/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.14  tff('#skF_6', type, '#skF_6': $i > $i).
% 1.78/1.14  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.78/1.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.78/1.14  
% 1.78/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.78/1.14  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.78/1.14  tff(f_55, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.78/1.14  tff(f_65, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.78/1.14  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.78/1.14  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 1.78/1.14  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.78/1.14  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.78/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.78/1.14  tff(c_31, plain, (![A_27]: (v1_relat_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.14  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_31])).
% 1.78/1.14  tff(c_26, plain, (![A_23]: (v1_relat_1(k4_relat_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.14  tff(c_30, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.78/1.14  tff(c_28, plain, (![A_24]: (k1_xboole_0=A_24 | r2_hidden(k4_tarski('#skF_5'(A_24), '#skF_6'(A_24)), A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.78/1.14  tff(c_95, plain, (![D_40, C_41, A_42]: (r2_hidden(k4_tarski(D_40, C_41), A_42) | ~r2_hidden(k4_tarski(C_41, D_40), k4_relat_1(A_42)) | ~v1_relat_1(k4_relat_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.14  tff(c_105, plain, (![A_43]: (r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_43)), '#skF_5'(k4_relat_1(A_43))), A_43) | ~v1_relat_1(A_43) | k4_relat_1(A_43)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_43)))), inference(resolution, [status(thm)], [c_28, c_95])).
% 1.78/1.14  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.78/1.14  tff(c_53, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | k4_xboole_0(A_32, k1_tarski(B_31))!=A_32)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.14  tff(c_58, plain, (![B_31]: (~r2_hidden(B_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.78/1.14  tff(c_113, plain, (~v1_relat_1(k1_xboole_0) | k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_58])).
% 1.78/1.14  tff(c_117, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_113])).
% 1.78/1.14  tff(c_118, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_30, c_117])).
% 1.78/1.14  tff(c_121, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_118])).
% 1.78/1.14  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_121])).
% 1.78/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  Inference rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Ref     : 0
% 1.78/1.14  #Sup     : 17
% 1.78/1.14  #Fact    : 0
% 1.78/1.14  #Define  : 0
% 1.78/1.14  #Split   : 0
% 1.78/1.14  #Chain   : 0
% 1.78/1.14  #Close   : 0
% 1.78/1.14  
% 1.78/1.14  Ordering : KBO
% 1.78/1.14  
% 1.78/1.14  Simplification rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Subsume      : 0
% 1.78/1.14  #Demod        : 3
% 1.78/1.14  #Tautology    : 11
% 1.78/1.14  #SimpNegUnit  : 3
% 1.78/1.14  #BackRed      : 0
% 1.78/1.14  
% 1.78/1.14  #Partial instantiations: 0
% 1.78/1.14  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.29
% 1.78/1.15  Parsing              : 0.15
% 1.78/1.15  CNF conversion       : 0.02
% 1.78/1.15  Main loop            : 0.11
% 1.78/1.15  Inferencing          : 0.04
% 1.78/1.15  Reduction            : 0.03
% 1.78/1.15  Demodulation         : 0.02
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.02
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.42
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
