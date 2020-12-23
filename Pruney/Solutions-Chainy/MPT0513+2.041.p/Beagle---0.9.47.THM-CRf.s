%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

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

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [A_35] :
      ( k7_relat_1(A_35,k1_relat_1(A_35)) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_85,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_81])).

tff(c_24,plain,(
    ! [A_27] :
      ( k7_relat_1(A_27,k1_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,(
    ! [C_48,A_49,B_50] :
      ( k7_relat_1(k7_relat_1(C_48,A_49),B_50) = k7_relat_1(C_48,A_49)
      | ~ r1_tarski(A_49,B_50)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,(
    ! [A_51,B_52] :
      ( k7_relat_1(A_51,k1_relat_1(A_51)) = k7_relat_1(A_51,B_52)
      | ~ r1_tarski(k1_relat_1(A_51),B_52)
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_157,plain,(
    ! [B_52] :
      ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k7_relat_1(k1_xboole_0,B_52)
      | ~ r1_tarski(k1_xboole_0,B_52)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_159,plain,(
    ! [B_52] : k7_relat_1(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_2,c_85,c_22,c_157])).

tff(c_26,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.28  
% 1.92/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.92/1.28  
% 1.92/1.28  %Foreground sorts:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Background operators:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Foreground operators:
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.92/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.28  
% 1.92/1.29  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.92/1.29  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.29  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.29  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.92/1.29  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.29  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.92/1.29  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.92/1.29  tff(f_62, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.92/1.29  tff(c_66, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.29  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.29  tff(c_58, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.29  tff(c_61, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.92/1.29  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_61])).
% 1.92/1.29  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.29  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.29  tff(c_72, plain, (![A_35]: (k7_relat_1(A_35, k1_relat_1(A_35))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.29  tff(c_81, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_72])).
% 1.92/1.29  tff(c_85, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_81])).
% 1.92/1.29  tff(c_24, plain, (![A_27]: (k7_relat_1(A_27, k1_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.29  tff(c_122, plain, (![C_48, A_49, B_50]: (k7_relat_1(k7_relat_1(C_48, A_49), B_50)=k7_relat_1(C_48, A_49) | ~r1_tarski(A_49, B_50) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.29  tff(c_155, plain, (![A_51, B_52]: (k7_relat_1(A_51, k1_relat_1(A_51))=k7_relat_1(A_51, B_52) | ~r1_tarski(k1_relat_1(A_51), B_52) | ~v1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_24, c_122])).
% 1.92/1.29  tff(c_157, plain, (![B_52]: (k7_relat_1(k1_xboole_0, k1_relat_1(k1_xboole_0))=k7_relat_1(k1_xboole_0, B_52) | ~r1_tarski(k1_xboole_0, B_52) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_155])).
% 1.92/1.29  tff(c_159, plain, (![B_52]: (k7_relat_1(k1_xboole_0, B_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_2, c_85, c_22, c_157])).
% 1.92/1.29  tff(c_26, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.29  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_26])).
% 1.92/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  Inference rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Ref     : 1
% 1.92/1.29  #Sup     : 33
% 1.92/1.29  #Fact    : 0
% 1.92/1.29  #Define  : 0
% 1.92/1.29  #Split   : 0
% 1.92/1.29  #Chain   : 0
% 1.92/1.29  #Close   : 0
% 1.92/1.29  
% 1.92/1.29  Ordering : KBO
% 1.92/1.29  
% 1.92/1.29  Simplification rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Subsume      : 1
% 1.92/1.29  #Demod        : 11
% 1.92/1.29  #Tautology    : 24
% 1.92/1.29  #SimpNegUnit  : 0
% 1.92/1.29  #BackRed      : 1
% 1.92/1.29  
% 1.92/1.29  #Partial instantiations: 0
% 1.92/1.29  #Strategies tried      : 1
% 1.92/1.29  
% 1.92/1.29  Timing (in seconds)
% 1.92/1.29  ----------------------
% 1.92/1.29  Preprocessing        : 0.33
% 1.92/1.29  Parsing              : 0.17
% 1.92/1.29  CNF conversion       : 0.02
% 1.92/1.29  Main loop            : 0.15
% 1.92/1.29  Inferencing          : 0.06
% 1.92/1.29  Reduction            : 0.04
% 1.92/1.29  Demodulation         : 0.03
% 1.92/1.29  BG Simplification    : 0.01
% 1.92/1.29  Subsumption          : 0.02
% 1.92/1.29  Abstraction          : 0.01
% 1.92/1.29  MUC search           : 0.00
% 1.92/1.29  Cooper               : 0.00
% 1.92/1.29  Total                : 0.50
% 1.92/1.29  Index Insertion      : 0.00
% 1.92/1.29  Index Deletion       : 0.00
% 1.92/1.29  Index Matching       : 0.00
% 1.92/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
