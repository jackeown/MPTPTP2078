%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  54 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

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

tff(c_61,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_66,c_61])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [B_42,A_43] :
      ( k7_relat_1(B_42,A_43) = B_42
      | ~ r1_tarski(k1_relat_1(B_42),A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [A_43] :
      ( k7_relat_1(k1_xboole_0,A_43) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_43)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_93])).

tff(c_109,plain,(
    ! [A_46] : k7_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2,c_96])).

tff(c_18,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [A_46] :
      ( k9_relat_1(k1_xboole_0,A_46) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_18])).

tff(c_119,plain,(
    ! [A_46] : k9_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_20,c_114])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.65/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.65/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.14  
% 1.65/1.14  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.65/1.14  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.65/1.14  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.65/1.14  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.65/1.14  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.65/1.14  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.65/1.14  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.65/1.14  tff(f_62, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.65/1.14  tff(c_66, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.14  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.14  tff(c_58, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.14  tff(c_61, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.65/1.14  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_61])).
% 1.65/1.14  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.65/1.14  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.14  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.65/1.14  tff(c_93, plain, (![B_42, A_43]: (k7_relat_1(B_42, A_43)=B_42 | ~r1_tarski(k1_relat_1(B_42), A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.14  tff(c_96, plain, (![A_43]: (k7_relat_1(k1_xboole_0, A_43)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_43) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_93])).
% 1.65/1.14  tff(c_109, plain, (![A_46]: (k7_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2, c_96])).
% 1.65/1.14  tff(c_18, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.14  tff(c_114, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_109, c_18])).
% 1.65/1.14  tff(c_119, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_20, c_114])).
% 1.65/1.14  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.65/1.14  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_26])).
% 1.65/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  Inference rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Ref     : 0
% 1.65/1.14  #Sup     : 24
% 1.65/1.14  #Fact    : 0
% 1.65/1.14  #Define  : 0
% 1.65/1.14  #Split   : 0
% 1.65/1.14  #Chain   : 0
% 1.65/1.14  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 1
% 1.65/1.15  #Demod        : 5
% 1.65/1.15  #Tautology    : 18
% 1.65/1.15  #SimpNegUnit  : 0
% 1.65/1.15  #BackRed      : 1
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.27
% 1.65/1.15  Parsing              : 0.15
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.11
% 1.65/1.15  Inferencing          : 0.05
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.02
% 1.65/1.15  Abstraction          : 0.00
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.40
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
