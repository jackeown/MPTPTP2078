%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.81s
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
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

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
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_7,D_8,A_5,B_6] :
      ( ~ r1_xboole_0(C_7,D_8)
      | r1_xboole_0(k2_zfmisc_1(A_5,C_7),k2_zfmisc_1(B_6,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_20,C_21,B_22,D_23] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_xboole_0(B_22,D_23)
      | ~ r1_tarski(C_21,D_23)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [D_39,A_42,C_38,A_43,C_41,B_40] :
      ( r1_xboole_0(A_43,C_38)
      | ~ r1_tarski(C_38,k2_zfmisc_1(B_40,D_39))
      | ~ r1_tarski(A_43,k2_zfmisc_1(A_42,C_41))
      | ~ r1_xboole_0(C_41,D_39) ) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

tff(c_44,plain,(
    ! [A_44,A_45,A_46,C_47] :
      ( r1_xboole_0(A_44,A_45)
      | ~ r1_tarski(A_44,k2_zfmisc_1(A_46,C_47))
      | ~ r1_xboole_0(C_47,k2_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_48,plain,(
    ! [A_48,A_49] :
      ( r1_xboole_0(A_48,A_49)
      | ~ r1_xboole_0(k2_relat_1(A_48),k2_relat_1(A_49))
      | ~ v1_relat_1(A_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_51,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_54,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.60/1.17  
% 1.60/1.17  %Foreground sorts:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Background operators:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Foreground operators:
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.17  
% 1.81/1.18  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 1.81/1.18  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.81/1.18  tff(f_39, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.81/1.18  tff(f_33, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.81/1.18  tff(c_10, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.18  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.18  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.18  tff(c_12, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.18  tff(c_8, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.18  tff(c_4, plain, (![C_7, D_8, A_5, B_6]: (~r1_xboole_0(C_7, D_8) | r1_xboole_0(k2_zfmisc_1(A_5, C_7), k2_zfmisc_1(B_6, D_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.18  tff(c_20, plain, (![A_20, C_21, B_22, D_23]: (r1_xboole_0(A_20, C_21) | ~r1_xboole_0(B_22, D_23) | ~r1_tarski(C_21, D_23) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.18  tff(c_40, plain, (![D_39, A_42, C_38, A_43, C_41, B_40]: (r1_xboole_0(A_43, C_38) | ~r1_tarski(C_38, k2_zfmisc_1(B_40, D_39)) | ~r1_tarski(A_43, k2_zfmisc_1(A_42, C_41)) | ~r1_xboole_0(C_41, D_39))), inference(resolution, [status(thm)], [c_4, c_20])).
% 1.81/1.18  tff(c_44, plain, (![A_44, A_45, A_46, C_47]: (r1_xboole_0(A_44, A_45) | ~r1_tarski(A_44, k2_zfmisc_1(A_46, C_47)) | ~r1_xboole_0(C_47, k2_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_8, c_40])).
% 1.81/1.18  tff(c_48, plain, (![A_48, A_49]: (r1_xboole_0(A_48, A_49) | ~r1_xboole_0(k2_relat_1(A_48), k2_relat_1(A_49)) | ~v1_relat_1(A_49) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.81/1.18  tff(c_51, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_48])).
% 1.81/1.18  tff(c_54, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_51])).
% 1.81/1.18  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_54])).
% 1.81/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  Inference rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Ref     : 0
% 1.81/1.18  #Sup     : 8
% 1.81/1.18  #Fact    : 0
% 1.81/1.18  #Define  : 0
% 1.81/1.18  #Split   : 0
% 1.81/1.18  #Chain   : 0
% 1.81/1.18  #Close   : 0
% 1.81/1.18  
% 1.81/1.18  Ordering : KBO
% 1.81/1.18  
% 1.81/1.18  Simplification rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Subsume      : 0
% 1.81/1.18  #Demod        : 2
% 1.81/1.18  #Tautology    : 0
% 1.81/1.18  #SimpNegUnit  : 1
% 1.81/1.18  #BackRed      : 0
% 1.81/1.18  
% 1.81/1.18  #Partial instantiations: 0
% 1.81/1.18  #Strategies tried      : 1
% 1.81/1.18  
% 1.81/1.18  Timing (in seconds)
% 1.81/1.18  ----------------------
% 1.81/1.18  Preprocessing        : 0.25
% 1.81/1.18  Parsing              : 0.14
% 1.81/1.18  CNF conversion       : 0.02
% 1.81/1.18  Main loop            : 0.12
% 1.81/1.18  Inferencing          : 0.05
% 1.81/1.18  Reduction            : 0.03
% 1.81/1.18  Demodulation         : 0.02
% 1.81/1.18  BG Simplification    : 0.01
% 1.81/1.18  Subsumption          : 0.03
% 1.81/1.18  Abstraction          : 0.00
% 1.81/1.18  MUC search           : 0.00
% 1.81/1.18  Cooper               : 0.00
% 1.81/1.18  Total                : 0.40
% 1.81/1.18  Index Insertion      : 0.00
% 1.81/1.18  Index Deletion       : 0.00
% 1.81/1.18  Index Matching       : 0.00
% 1.81/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
