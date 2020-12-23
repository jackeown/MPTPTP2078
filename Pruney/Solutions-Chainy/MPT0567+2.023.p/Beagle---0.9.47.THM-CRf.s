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
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_22,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_2'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_27,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | ~ r1_xboole_0(k1_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_18] : ~ r2_hidden(A_18,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_27])).

tff(c_98,plain,(
    ! [A_38,C_39] :
      ( ~ r2_hidden(A_38,k10_relat_1(C_39,k1_xboole_0))
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_89,c_32])).

tff(c_118,plain,(
    ! [C_43,B_44] :
      ( ~ v1_relat_1(C_43)
      | r1_tarski(k10_relat_1(C_43,k1_xboole_0),B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_128,plain,(
    ! [C_45] :
      ( k10_relat_1(C_45,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_45) ) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_131,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_128])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.85/1.21  
% 1.85/1.21  %Foreground sorts:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Background operators:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Foreground operators:
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.21  
% 1.85/1.22  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.85/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.22  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.85/1.22  tff(f_38, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.85/1.22  tff(f_43, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.85/1.22  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.85/1.22  tff(c_22, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.85/1.22  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.85/1.22  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.22  tff(c_89, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_2'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.22  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.22  tff(c_27, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | ~r1_xboole_0(k1_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.85/1.22  tff(c_32, plain, (![A_18]: (~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_27])).
% 1.85/1.22  tff(c_98, plain, (![A_38, C_39]: (~r2_hidden(A_38, k10_relat_1(C_39, k1_xboole_0)) | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_89, c_32])).
% 1.85/1.22  tff(c_118, plain, (![C_43, B_44]: (~v1_relat_1(C_43) | r1_tarski(k10_relat_1(C_43, k1_xboole_0), B_44))), inference(resolution, [status(thm)], [c_6, c_98])).
% 1.85/1.22  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.22  tff(c_128, plain, (![C_45]: (k10_relat_1(C_45, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_45))), inference(resolution, [status(thm)], [c_118, c_8])).
% 1.85/1.22  tff(c_131, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_128])).
% 1.85/1.22  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_131])).
% 1.85/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  Inference rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Ref     : 0
% 1.85/1.22  #Sup     : 20
% 1.85/1.22  #Fact    : 0
% 1.85/1.22  #Define  : 0
% 1.85/1.22  #Split   : 0
% 1.85/1.22  #Chain   : 0
% 1.85/1.22  #Close   : 0
% 1.85/1.22  
% 1.85/1.22  Ordering : KBO
% 1.85/1.22  
% 1.85/1.22  Simplification rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Subsume      : 1
% 1.85/1.22  #Demod        : 2
% 1.85/1.22  #Tautology    : 5
% 1.85/1.22  #SimpNegUnit  : 1
% 1.85/1.22  #BackRed      : 0
% 1.85/1.22  
% 1.85/1.22  #Partial instantiations: 0
% 1.85/1.22  #Strategies tried      : 1
% 1.85/1.22  
% 1.85/1.22  Timing (in seconds)
% 1.85/1.22  ----------------------
% 1.85/1.23  Preprocessing        : 0.29
% 1.85/1.23  Parsing              : 0.16
% 1.85/1.23  CNF conversion       : 0.02
% 1.85/1.23  Main loop            : 0.14
% 1.85/1.23  Inferencing          : 0.06
% 1.85/1.23  Reduction            : 0.03
% 1.85/1.23  Demodulation         : 0.02
% 1.85/1.23  BG Simplification    : 0.01
% 1.85/1.23  Subsumption          : 0.03
% 1.85/1.23  Abstraction          : 0.01
% 1.85/1.23  MUC search           : 0.00
% 1.85/1.23  Cooper               : 0.00
% 1.85/1.23  Total                : 0.45
% 1.85/1.23  Index Insertion      : 0.00
% 1.85/1.23  Index Deletion       : 0.00
% 1.85/1.23  Index Matching       : 0.00
% 1.85/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
