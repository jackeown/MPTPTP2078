%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  55 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [B_35,A_36] :
      ( k3_xboole_0(B_35,k2_zfmisc_1(A_36,k2_relat_1(B_35))) = k7_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k4_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_99,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_31])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,C_23)
      | ~ r1_xboole_0(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_22] :
      ( r1_xboole_0(A_22,'#skF_2')
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_54,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,A_29) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_28),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [B_34] :
      ( k7_relat_1(B_34,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_34)
      | ~ r1_tarski(k1_relat_1(B_34),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_45,c_54])).

tff(c_150,plain,(
    ! [B_43] :
      ( k7_relat_1(k7_relat_1(B_43,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_43,'#skF_1'))
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_156,plain,(
    ! [B_44] :
      ( k7_relat_1(k7_relat_1(B_44,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_99,c_150])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_171,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.22  
% 1.96/1.23  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.96/1.23  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 1.96/1.23  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.96/1.23  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 1.96/1.23  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.96/1.23  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.96/1.23  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.96/1.23  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.23  tff(c_90, plain, (![B_35, A_36]: (k3_xboole_0(B_35, k2_zfmisc_1(A_36, k2_relat_1(B_35)))=k7_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.23  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.23  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k4_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.23  tff(c_31, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6])).
% 1.96/1.23  tff(c_99, plain, (![B_35, A_36]: (v1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_90, c_31])).
% 1.96/1.23  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.23  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.23  tff(c_42, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, C_23) | ~r1_xboole_0(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.23  tff(c_45, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_2') | ~r1_tarski(A_22, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_42])).
% 1.96/1.23  tff(c_54, plain, (![B_28, A_29]: (k7_relat_1(B_28, A_29)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_28), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_84, plain, (![B_34]: (k7_relat_1(B_34, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_34) | ~r1_tarski(k1_relat_1(B_34), '#skF_1'))), inference(resolution, [status(thm)], [c_45, c_54])).
% 1.96/1.23  tff(c_150, plain, (![B_43]: (k7_relat_1(k7_relat_1(B_43, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_43, '#skF_1')) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_8, c_84])).
% 1.96/1.23  tff(c_156, plain, (![B_44]: (k7_relat_1(k7_relat_1(B_44, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_99, c_150])).
% 1.96/1.23  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.23  tff(c_171, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 1.96/1.23  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_171])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 39
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 0
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 3
% 1.96/1.23  #Demod        : 4
% 1.96/1.23  #Tautology    : 13
% 1.96/1.23  #SimpNegUnit  : 0
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.96/1.24  Preprocessing        : 0.28
% 1.96/1.24  Parsing              : 0.16
% 1.96/1.24  CNF conversion       : 0.02
% 1.96/1.24  Main loop            : 0.16
% 1.96/1.24  Inferencing          : 0.07
% 1.96/1.24  Reduction            : 0.04
% 1.96/1.24  Demodulation         : 0.03
% 1.96/1.24  BG Simplification    : 0.01
% 1.96/1.24  Subsumption          : 0.03
% 1.96/1.24  Abstraction          : 0.01
% 1.96/1.24  MUC search           : 0.00
% 1.96/1.24  Cooper               : 0.00
% 1.96/1.24  Total                : 0.46
% 1.96/1.24  Index Insertion      : 0.00
% 1.96/1.24  Index Deletion       : 0.00
% 1.96/1.24  Index Matching       : 0.00
% 1.96/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
