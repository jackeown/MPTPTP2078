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
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_70,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_68])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_23] : k7_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [B_38,A_39] :
      ( k2_relat_1(k7_relat_1(B_38,A_39)) = k9_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_23] :
      ( k9_relat_1(k1_xboole_0,A_23) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_101,plain,(
    ! [A_23] : k9_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_20,c_97])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.42  
% 2.02/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.42  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.42  
% 2.02/1.42  %Foreground sorts:
% 2.02/1.42  
% 2.02/1.42  
% 2.02/1.42  %Background operators:
% 2.02/1.42  
% 2.02/1.42  
% 2.02/1.42  %Foreground operators:
% 2.02/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.42  
% 2.02/1.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.44  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.02/1.44  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.02/1.44  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.44  tff(f_46, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.02/1.44  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.02/1.44  tff(f_56, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.02/1.44  tff(c_70, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.44  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.44  tff(c_62, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.44  tff(c_68, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 2.02/1.44  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_68])).
% 2.02/1.44  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.44  tff(c_16, plain, (![A_23]: (k7_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.44  tff(c_88, plain, (![B_38, A_39]: (k2_relat_1(k7_relat_1(B_38, A_39))=k9_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.44  tff(c_97, plain, (![A_23]: (k9_relat_1(k1_xboole_0, A_23)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_88])).
% 2.02/1.44  tff(c_101, plain, (![A_23]: (k9_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_20, c_97])).
% 2.02/1.44  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.44  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_24])).
% 2.02/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.44  
% 2.02/1.44  Inference rules
% 2.02/1.44  ----------------------
% 2.02/1.44  #Ref     : 0
% 2.02/1.44  #Sup     : 20
% 2.02/1.44  #Fact    : 0
% 2.02/1.44  #Define  : 0
% 2.02/1.44  #Split   : 0
% 2.02/1.44  #Chain   : 0
% 2.02/1.44  #Close   : 0
% 2.02/1.44  
% 2.02/1.44  Ordering : KBO
% 2.02/1.44  
% 2.02/1.44  Simplification rules
% 2.02/1.44  ----------------------
% 2.02/1.44  #Subsume      : 1
% 2.02/1.44  #Demod        : 3
% 2.02/1.44  #Tautology    : 16
% 2.02/1.44  #SimpNegUnit  : 0
% 2.02/1.44  #BackRed      : 1
% 2.02/1.44  
% 2.02/1.44  #Partial instantiations: 0
% 2.02/1.44  #Strategies tried      : 1
% 2.02/1.44  
% 2.02/1.44  Timing (in seconds)
% 2.02/1.44  ----------------------
% 2.02/1.44  Preprocessing        : 0.45
% 2.02/1.44  Parsing              : 0.24
% 2.02/1.45  CNF conversion       : 0.03
% 2.02/1.45  Main loop            : 0.17
% 2.02/1.45  Inferencing          : 0.08
% 2.02/1.45  Reduction            : 0.05
% 2.02/1.45  Demodulation         : 0.04
% 2.02/1.45  BG Simplification    : 0.01
% 2.02/1.45  Subsumption          : 0.03
% 2.02/1.45  Abstraction          : 0.01
% 2.02/1.45  MUC search           : 0.00
% 2.02/1.45  Cooper               : 0.00
% 2.02/1.45  Total                : 0.66
% 2.02/1.45  Index Insertion      : 0.00
% 2.02/1.45  Index Deletion       : 0.00
% 2.02/1.45  Index Matching       : 0.00
% 2.02/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
