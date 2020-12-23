%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  79 expanded)
%              Number of equality atoms :   20 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_66,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34),A_34)
      | v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_66,c_64])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_35] :
      ( k8_relat_1(k2_relat_1(A_35),A_35) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_85,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_81])).

tff(c_18,plain,(
    ! [A_24] :
      ( k8_relat_1(k2_relat_1(A_24),A_24) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [B_48,A_49,C_50] :
      ( k8_relat_1(B_48,k8_relat_1(A_49,C_50)) = k8_relat_1(A_49,C_50)
      | ~ r1_tarski(A_49,B_48)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [A_51,B_52] :
      ( k8_relat_1(k2_relat_1(A_51),A_51) = k8_relat_1(B_52,A_51)
      | ~ r1_tarski(k2_relat_1(A_51),B_52)
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_157,plain,(
    ! [B_52] :
      ( k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) = k8_relat_1(B_52,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_52)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_159,plain,(
    ! [B_52] : k8_relat_1(B_52,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_2,c_85,c_22,c_157])).

tff(c_26,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.79/1.18  
% 1.79/1.18  %Foreground sorts:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Background operators:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Foreground operators:
% 1.79/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.79/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.18  
% 1.79/1.19  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.79/1.19  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.79/1.19  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.79/1.19  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.19  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.79/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 1.79/1.19  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.79/1.19  tff(f_62, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.79/1.19  tff(c_66, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.19  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.19  tff(c_58, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.19  tff(c_64, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.79/1.19  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_64])).
% 1.79/1.19  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.19  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.19  tff(c_72, plain, (![A_35]: (k8_relat_1(k2_relat_1(A_35), A_35)=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.19  tff(c_81, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_72])).
% 1.79/1.19  tff(c_85, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_81])).
% 1.79/1.19  tff(c_18, plain, (![A_24]: (k8_relat_1(k2_relat_1(A_24), A_24)=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.19  tff(c_122, plain, (![B_48, A_49, C_50]: (k8_relat_1(B_48, k8_relat_1(A_49, C_50))=k8_relat_1(A_49, C_50) | ~r1_tarski(A_49, B_48) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.79/1.19  tff(c_155, plain, (![A_51, B_52]: (k8_relat_1(k2_relat_1(A_51), A_51)=k8_relat_1(B_52, A_51) | ~r1_tarski(k2_relat_1(A_51), B_52) | ~v1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_18, c_122])).
% 1.79/1.19  tff(c_157, plain, (![B_52]: (k8_relat_1(k2_relat_1(k1_xboole_0), k1_xboole_0)=k8_relat_1(B_52, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_52) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_155])).
% 1.79/1.19  tff(c_159, plain, (![B_52]: (k8_relat_1(B_52, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_2, c_85, c_22, c_157])).
% 1.79/1.19  tff(c_26, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.79/1.19  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_26])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 1
% 1.79/1.19  #Sup     : 33
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 0
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 1
% 1.79/1.19  #Demod        : 11
% 1.79/1.19  #Tautology    : 24
% 1.79/1.19  #SimpNegUnit  : 0
% 1.79/1.19  #BackRed      : 1
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.19  Preprocessing        : 0.27
% 1.79/1.19  Parsing              : 0.15
% 1.79/1.19  CNF conversion       : 0.02
% 1.79/1.19  Main loop            : 0.14
% 1.79/1.19  Inferencing          : 0.06
% 1.79/1.19  Reduction            : 0.04
% 1.79/1.19  Demodulation         : 0.03
% 1.79/1.19  BG Simplification    : 0.01
% 1.79/1.19  Subsumption          : 0.02
% 1.79/1.19  Abstraction          : 0.01
% 1.79/1.19  MUC search           : 0.00
% 1.79/1.19  Cooper               : 0.00
% 1.79/1.19  Total                : 0.43
% 1.79/1.19  Index Insertion      : 0.00
% 1.79/1.19  Index Deletion       : 0.00
% 1.79/1.19  Index Matching       : 0.00
% 1.79/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
