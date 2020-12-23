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
% DateTime   : Thu Dec  3 09:59:24 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_28,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_85,c_80])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_41] : k5_xboole_0(k1_xboole_0,A_41) = k2_xboole_0(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_4,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_44] :
      ( k2_xboole_0(k1_relat_1(A_44),k2_relat_1(A_44)) = k3_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_156,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_147])).

tff(c_163,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_115,c_26,c_156])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  %$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.60/1.17  
% 1.60/1.17  %Foreground sorts:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Background operators:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Foreground operators:
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.60/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.60/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.17  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.60/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.60/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.60/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.60/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.17  
% 1.60/1.18  tff(f_59, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.60/1.18  tff(f_50, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.60/1.18  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.60/1.18  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.60/1.18  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.60/1.18  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.60/1.18  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.60/1.18  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.60/1.18  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.60/1.18  tff(c_28, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.60/1.18  tff(c_85, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.60/1.18  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.18  tff(c_77, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.18  tff(c_80, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_77])).
% 1.60/1.18  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_80])).
% 1.60/1.18  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.18  tff(c_92, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.18  tff(c_104, plain, (![A_41]: (k5_xboole_0(k1_xboole_0, A_41)=k2_xboole_0(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 1.60/1.18  tff(c_4, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.18  tff(c_115, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_104, c_4])).
% 1.60/1.18  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.60/1.18  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.60/1.18  tff(c_147, plain, (![A_44]: (k2_xboole_0(k1_relat_1(A_44), k2_relat_1(A_44))=k3_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.18  tff(c_156, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_147])).
% 1.60/1.18  tff(c_163, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_115, c_26, c_156])).
% 1.60/1.18  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_163])).
% 1.60/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.18  
% 1.60/1.18  Inference rules
% 1.60/1.18  ----------------------
% 1.60/1.18  #Ref     : 0
% 1.60/1.18  #Sup     : 34
% 1.60/1.18  #Fact    : 0
% 1.60/1.18  #Define  : 0
% 1.60/1.18  #Split   : 0
% 1.60/1.18  #Chain   : 0
% 1.60/1.18  #Close   : 0
% 1.60/1.18  
% 1.60/1.18  Ordering : KBO
% 1.60/1.18  
% 1.60/1.18  Simplification rules
% 1.60/1.18  ----------------------
% 1.60/1.18  #Subsume      : 1
% 1.60/1.18  #Demod        : 6
% 1.60/1.18  #Tautology    : 27
% 1.60/1.18  #SimpNegUnit  : 1
% 1.60/1.18  #BackRed      : 0
% 1.60/1.18  
% 1.60/1.18  #Partial instantiations: 0
% 1.60/1.18  #Strategies tried      : 1
% 1.60/1.18  
% 1.60/1.18  Timing (in seconds)
% 1.60/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.28
% 1.82/1.18  Parsing              : 0.16
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.12
% 1.82/1.18  Inferencing          : 0.05
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.02
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.43
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
