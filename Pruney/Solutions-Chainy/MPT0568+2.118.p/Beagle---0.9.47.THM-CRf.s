%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  50 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_132,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r2_hidden('#skF_2'(A_31,B_32),A_31)
      | B_32 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,A_29)
      | k4_xboole_0(A_29,k1_tarski(B_28)) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [B_28] : ~ r2_hidden(B_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_139,plain,(
    ! [B_32] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_32),B_32)
      | k1_xboole_0 = B_32 ) ),
    inference(resolution,[status(thm)],[c_132,c_130])).

tff(c_48,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_276,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_3'(A_51,B_52,C_53),k2_relat_1(C_53))
      | ~ r2_hidden(A_51,k10_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_279,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51,B_52,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_51,k10_relat_1(k1_xboole_0,B_52))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_276])).

tff(c_281,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51,B_52,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_51,k10_relat_1(k1_xboole_0,B_52)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_279])).

tff(c_283,plain,(
    ! [A_54,B_55] : ~ r2_hidden(A_54,k10_relat_1(k1_xboole_0,B_55)) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_281])).

tff(c_307,plain,(
    ! [B_55] : k10_relat_1(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_283])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.29  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.01/1.29  
% 2.01/1.29  %Foreground sorts:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Background operators:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Foreground operators:
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.01/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.01/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.29  
% 2.01/1.30  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.01/1.30  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.01/1.30  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.01/1.30  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.01/1.30  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.01/1.30  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.01/1.30  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.01/1.30  tff(f_66, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.01/1.30  tff(c_132, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), B_32) | r2_hidden('#skF_2'(A_31, B_32), A_31) | B_32=A_31)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.30  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.01/1.30  tff(c_121, plain, (![B_28, A_29]: (~r2_hidden(B_28, A_29) | k4_xboole_0(A_29, k1_tarski(B_28))!=A_29)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.01/1.30  tff(c_130, plain, (![B_28]: (~r2_hidden(B_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_121])).
% 2.01/1.30  tff(c_139, plain, (![B_32]: (r2_hidden('#skF_1'(k1_xboole_0, B_32), B_32) | k1_xboole_0=B_32)), inference(resolution, [status(thm)], [c_132, c_130])).
% 2.01/1.30  tff(c_48, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.30  tff(c_24, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.30  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_24])).
% 2.01/1.30  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.30  tff(c_276, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_3'(A_51, B_52, C_53), k2_relat_1(C_53)) | ~r2_hidden(A_51, k10_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.30  tff(c_279, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51, B_52, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_51, k10_relat_1(k1_xboole_0, B_52)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_276])).
% 2.01/1.30  tff(c_281, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51, B_52, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_51, k10_relat_1(k1_xboole_0, B_52)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_279])).
% 2.01/1.30  tff(c_283, plain, (![A_54, B_55]: (~r2_hidden(A_54, k10_relat_1(k1_xboole_0, B_55)))), inference(negUnitSimplification, [status(thm)], [c_130, c_281])).
% 2.01/1.30  tff(c_307, plain, (![B_55]: (k10_relat_1(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_139, c_283])).
% 2.01/1.30  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.30  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_38])).
% 2.01/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  
% 2.01/1.30  Inference rules
% 2.01/1.30  ----------------------
% 2.01/1.30  #Ref     : 0
% 2.01/1.30  #Sup     : 60
% 2.01/1.30  #Fact    : 0
% 2.01/1.30  #Define  : 0
% 2.01/1.30  #Split   : 0
% 2.01/1.30  #Chain   : 0
% 2.01/1.30  #Close   : 0
% 2.01/1.30  
% 2.01/1.30  Ordering : KBO
% 2.01/1.30  
% 2.01/1.30  Simplification rules
% 2.01/1.30  ----------------------
% 2.01/1.30  #Subsume      : 11
% 2.01/1.30  #Demod        : 11
% 2.01/1.30  #Tautology    : 32
% 2.01/1.30  #SimpNegUnit  : 1
% 2.01/1.30  #BackRed      : 2
% 2.01/1.30  
% 2.01/1.30  #Partial instantiations: 0
% 2.01/1.30  #Strategies tried      : 1
% 2.01/1.30  
% 2.01/1.30  Timing (in seconds)
% 2.01/1.30  ----------------------
% 2.01/1.30  Preprocessing        : 0.30
% 2.01/1.30  Parsing              : 0.16
% 2.01/1.30  CNF conversion       : 0.02
% 2.01/1.30  Main loop            : 0.18
% 2.01/1.30  Inferencing          : 0.07
% 2.01/1.30  Reduction            : 0.05
% 2.01/1.30  Demodulation         : 0.04
% 2.01/1.30  BG Simplification    : 0.01
% 2.01/1.30  Subsumption          : 0.03
% 2.01/1.30  Abstraction          : 0.01
% 2.01/1.30  MUC search           : 0.00
% 2.01/1.30  Cooper               : 0.00
% 2.01/1.30  Total                : 0.50
% 2.01/1.30  Index Insertion      : 0.00
% 2.01/1.30  Index Deletion       : 0.00
% 2.01/1.30  Index Matching       : 0.00
% 2.01/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
