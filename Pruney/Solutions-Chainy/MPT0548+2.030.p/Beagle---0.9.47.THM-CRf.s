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
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  54 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_70,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_65])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( k5_relat_1(k6_relat_1(A_47),B_48) = k7_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_23] : k5_relat_1(k6_relat_1(A_23),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_141,plain,(
    ! [A_47] :
      ( k7_relat_1(k1_xboole_0,A_47) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_84])).

tff(c_154,plain,(
    ! [A_49] : k7_relat_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_141])).

tff(c_18,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [A_49] :
      ( k9_relat_1(k1_xboole_0,A_49) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_164,plain,(
    ! [A_49] : k9_relat_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_20,c_159])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.69/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.69/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.14  
% 1.69/1.15  tff(f_44, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.69/1.15  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.69/1.15  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.69/1.15  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.69/1.15  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.69/1.15  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.69/1.15  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.69/1.15  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.69/1.15  tff(f_66, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.69/1.15  tff(c_70, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.15  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.15  tff(c_62, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.69/1.15  tff(c_65, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 1.69/1.15  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_65])).
% 1.69/1.15  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.69/1.15  tff(c_134, plain, (![A_47, B_48]: (k5_relat_1(k6_relat_1(A_47), B_48)=k7_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.69/1.15  tff(c_16, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.15  tff(c_76, plain, (![A_36]: (k5_relat_1(A_36, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.69/1.15  tff(c_84, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_76])).
% 1.69/1.15  tff(c_141, plain, (![A_47]: (k7_relat_1(k1_xboole_0, A_47)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_84])).
% 1.69/1.15  tff(c_154, plain, (![A_49]: (k7_relat_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_141])).
% 1.69/1.15  tff(c_18, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.15  tff(c_159, plain, (![A_49]: (k9_relat_1(k1_xboole_0, A_49)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 1.69/1.15  tff(c_164, plain, (![A_49]: (k9_relat_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_20, c_159])).
% 1.69/1.15  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.69/1.15  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_30])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 34
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 0
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 1
% 1.69/1.15  #Demod        : 7
% 1.69/1.15  #Tautology    : 26
% 1.69/1.15  #SimpNegUnit  : 0
% 1.69/1.15  #BackRed      : 1
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.15  Timing (in seconds)
% 1.69/1.15  ----------------------
% 1.69/1.15  Preprocessing        : 0.28
% 1.69/1.15  Parsing              : 0.15
% 1.69/1.15  CNF conversion       : 0.02
% 1.69/1.15  Main loop            : 0.13
% 1.69/1.15  Inferencing          : 0.05
% 1.69/1.15  Reduction            : 0.04
% 1.69/1.15  Demodulation         : 0.03
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.02
% 1.69/1.15  Abstraction          : 0.01
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.43
% 1.69/1.16  Index Insertion      : 0.00
% 1.69/1.16  Index Deletion       : 0.00
% 1.69/1.16  Index Matching       : 0.00
% 1.69/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
