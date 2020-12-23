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
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  74 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_89,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_52)
      | r2_hidden('#skF_2'(A_51,B_52),A_51)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [A_9,C_43] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_65,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_111,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_52),B_52)
      | k1_xboole_0 = B_52 ) ),
    inference(resolution,[status(thm)],[c_89,c_65])).

tff(c_22,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4'(A_11),A_11)
      | v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_263,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_7'(A_70,B_71,C_72),k2_relat_1(C_72))
      | ~ r2_hidden(A_70,k10_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_266,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_7'(A_70,B_71,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_70,k10_relat_1(k1_xboole_0,B_71))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_263])).

tff(c_268,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_7'(A_70,B_71,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_70,k10_relat_1(k1_xboole_0,B_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_266])).

tff(c_270,plain,(
    ! [A_73,B_74] : ~ r2_hidden(A_73,k10_relat_1(k1_xboole_0,B_74)) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_268])).

tff(c_299,plain,(
    ! [B_74] : k10_relat_1(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_270])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.03/1.29  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.29  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.03/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.03/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.29  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.03/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.29  
% 2.03/1.30  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.03/1.30  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.30  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.03/1.30  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.03/1.30  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.03/1.30  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.03/1.30  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.03/1.30  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.03/1.30  tff(c_89, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), B_52) | r2_hidden('#skF_2'(A_51, B_52), A_51) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.30  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.30  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.30  tff(c_55, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.30  tff(c_62, plain, (![A_9, C_43]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_55])).
% 2.03/1.30  tff(c_65, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 2.03/1.30  tff(c_111, plain, (![B_52]: (r2_hidden('#skF_1'(k1_xboole_0, B_52), B_52) | k1_xboole_0=B_52)), inference(resolution, [status(thm)], [c_89, c_65])).
% 2.03/1.30  tff(c_22, plain, (![A_11]: (r2_hidden('#skF_4'(A_11), A_11) | v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.30  tff(c_66, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 2.03/1.30  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_66])).
% 2.03/1.30  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.30  tff(c_263, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_7'(A_70, B_71, C_72), k2_relat_1(C_72)) | ~r2_hidden(A_70, k10_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.30  tff(c_266, plain, (![A_70, B_71]: (r2_hidden('#skF_7'(A_70, B_71, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_70, k10_relat_1(k1_xboole_0, B_71)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_263])).
% 2.03/1.30  tff(c_268, plain, (![A_70, B_71]: (r2_hidden('#skF_7'(A_70, B_71, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_70, k10_relat_1(k1_xboole_0, B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_266])).
% 2.03/1.30  tff(c_270, plain, (![A_73, B_74]: (~r2_hidden(A_73, k10_relat_1(k1_xboole_0, B_74)))), inference(negUnitSimplification, [status(thm)], [c_65, c_268])).
% 2.03/1.30  tff(c_299, plain, (![B_74]: (k10_relat_1(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_270])).
% 2.03/1.30  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.30  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_36])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 56
% 2.03/1.30  #Fact    : 0
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 0
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 9
% 2.03/1.30  #Demod        : 17
% 2.03/1.30  #Tautology    : 25
% 2.03/1.30  #SimpNegUnit  : 2
% 2.03/1.30  #BackRed      : 2
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.31  Preprocessing        : 0.31
% 2.03/1.31  Parsing              : 0.17
% 2.03/1.31  CNF conversion       : 0.03
% 2.03/1.31  Main loop            : 0.20
% 2.03/1.31  Inferencing          : 0.09
% 2.03/1.31  Reduction            : 0.05
% 2.03/1.31  Demodulation         : 0.04
% 2.03/1.31  BG Simplification    : 0.01
% 2.03/1.31  Subsumption          : 0.03
% 2.03/1.31  Abstraction          : 0.01
% 2.03/1.31  MUC search           : 0.00
% 2.03/1.31  Cooper               : 0.00
% 2.03/1.31  Total                : 0.53
% 2.03/1.31  Index Insertion      : 0.00
% 2.03/1.31  Index Deletion       : 0.00
% 2.03/1.31  Index Matching       : 0.00
% 2.03/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
