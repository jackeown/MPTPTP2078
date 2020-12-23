%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_10,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( ~ r1_xboole_0(A_5,B_6)
      | r1_xboole_0(k2_zfmisc_1(A_5,C_7),k2_zfmisc_1(B_6,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_20,C_21,B_22,D_23] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_xboole_0(B_22,D_23)
      | ~ r1_tarski(C_21,D_23)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [C_29,A_31,B_28,D_27,C_26,A_30] :
      ( r1_xboole_0(A_31,C_26)
      | ~ r1_tarski(C_26,k2_zfmisc_1(B_28,D_27))
      | ~ r1_tarski(A_31,k2_zfmisc_1(A_30,C_29))
      | ~ r1_xboole_0(A_30,B_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

tff(c_35,plain,(
    ! [A_32,A_33,A_34,C_35] :
      ( r1_xboole_0(A_32,A_33)
      | ~ r1_tarski(A_32,k2_zfmisc_1(A_34,C_35))
      | ~ r1_xboole_0(A_34,k1_relat_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_39,plain,(
    ! [A_36,A_37] :
      ( r1_xboole_0(A_36,A_37)
      | ~ r1_xboole_0(k1_relat_1(A_36),k1_relat_1(A_37))
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_8,c_35])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_45,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_42])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.32  
% 1.92/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.32  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.32  
% 1.92/1.32  %Foreground sorts:
% 1.92/1.32  
% 1.92/1.32  
% 1.92/1.32  %Background operators:
% 1.92/1.32  
% 1.92/1.32  
% 1.92/1.32  %Foreground operators:
% 1.92/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.32  
% 1.92/1.33  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 1.92/1.33  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.92/1.33  tff(f_39, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.92/1.33  tff(f_33, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.92/1.33  tff(c_10, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.33  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.33  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.33  tff(c_12, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.33  tff(c_8, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.33  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (~r1_xboole_0(A_5, B_6) | r1_xboole_0(k2_zfmisc_1(A_5, C_7), k2_zfmisc_1(B_6, D_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.33  tff(c_20, plain, (![A_20, C_21, B_22, D_23]: (r1_xboole_0(A_20, C_21) | ~r1_xboole_0(B_22, D_23) | ~r1_tarski(C_21, D_23) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.33  tff(c_31, plain, (![C_29, A_31, B_28, D_27, C_26, A_30]: (r1_xboole_0(A_31, C_26) | ~r1_tarski(C_26, k2_zfmisc_1(B_28, D_27)) | ~r1_tarski(A_31, k2_zfmisc_1(A_30, C_29)) | ~r1_xboole_0(A_30, B_28))), inference(resolution, [status(thm)], [c_6, c_20])).
% 1.92/1.33  tff(c_35, plain, (![A_32, A_33, A_34, C_35]: (r1_xboole_0(A_32, A_33) | ~r1_tarski(A_32, k2_zfmisc_1(A_34, C_35)) | ~r1_xboole_0(A_34, k1_relat_1(A_33)) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.92/1.33  tff(c_39, plain, (![A_36, A_37]: (r1_xboole_0(A_36, A_37) | ~r1_xboole_0(k1_relat_1(A_36), k1_relat_1(A_37)) | ~v1_relat_1(A_37) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_8, c_35])).
% 1.92/1.33  tff(c_42, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.92/1.33  tff(c_45, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_42])).
% 1.92/1.33  tff(c_47, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_45])).
% 1.92/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.33  
% 1.92/1.33  Inference rules
% 1.92/1.33  ----------------------
% 1.92/1.33  #Ref     : 0
% 1.92/1.33  #Sup     : 6
% 1.92/1.33  #Fact    : 0
% 1.92/1.33  #Define  : 0
% 1.92/1.33  #Split   : 0
% 1.92/1.33  #Chain   : 0
% 1.92/1.33  #Close   : 0
% 1.92/1.33  
% 1.92/1.33  Ordering : KBO
% 1.92/1.33  
% 1.92/1.33  Simplification rules
% 1.92/1.33  ----------------------
% 1.92/1.33  #Subsume      : 0
% 1.92/1.33  #Demod        : 2
% 1.92/1.33  #Tautology    : 0
% 1.92/1.33  #SimpNegUnit  : 1
% 1.92/1.33  #BackRed      : 0
% 1.92/1.33  
% 1.92/1.33  #Partial instantiations: 0
% 1.92/1.33  #Strategies tried      : 1
% 1.92/1.33  
% 1.92/1.33  Timing (in seconds)
% 1.92/1.33  ----------------------
% 1.92/1.33  Preprocessing        : 0.36
% 1.92/1.33  Parsing              : 0.20
% 1.92/1.33  CNF conversion       : 0.02
% 1.92/1.33  Main loop            : 0.12
% 1.92/1.33  Inferencing          : 0.05
% 1.92/1.33  Reduction            : 0.02
% 1.92/1.33  Demodulation         : 0.02
% 1.92/1.33  BG Simplification    : 0.01
% 1.92/1.33  Subsumption          : 0.02
% 1.92/1.33  Abstraction          : 0.01
% 1.92/1.33  MUC search           : 0.00
% 1.92/1.33  Cooper               : 0.00
% 1.92/1.33  Total                : 0.50
% 1.92/1.33  Index Insertion      : 0.00
% 1.92/1.33  Index Deletion       : 0.00
% 1.92/1.33  Index Matching       : 0.00
% 1.92/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
