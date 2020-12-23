%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [C_20,A_18,B_19] :
      ( r1_tarski(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19))
      | ~ r1_tarski(A_18,B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [B_25,A_26] : r1_tarski(k3_xboole_0(B_25,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_452,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,k9_relat_1(B_81,k1_relat_1(B_81))) = k9_relat_1(B_81,k10_relat_1(B_81,A_80))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_705,plain,(
    ! [A_96,A_97,B_98] :
      ( r1_tarski(A_96,A_97)
      | ~ r1_tarski(A_96,k9_relat_1(B_98,k10_relat_1(B_98,A_97)))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_6])).

tff(c_2414,plain,(
    ! [C_216,A_217,A_218] :
      ( r1_tarski(k9_relat_1(C_216,A_217),A_218)
      | ~ v1_funct_1(C_216)
      | ~ r1_tarski(A_217,k10_relat_1(C_216,A_218))
      | ~ v1_relat_1(C_216) ) ),
    inference(resolution,[status(thm)],[c_16,c_705])).

tff(c_212,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k3_xboole_0(B_52,C_53))
      | ~ r1_tarski(A_51,C_53)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_225,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_25])).

tff(c_413,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_2421,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2414,c_413])).

tff(c_2437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_22,c_2421])).

tff(c_2438,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_2478,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_2438])).

tff(c_2482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4,c_2478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n011.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 20:48:27 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.85  
% 4.52/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.85  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.52/1.85  
% 4.52/1.85  %Foreground sorts:
% 4.52/1.85  
% 4.52/1.85  
% 4.52/1.85  %Background operators:
% 4.52/1.85  
% 4.52/1.85  
% 4.52/1.85  %Foreground operators:
% 4.52/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.52/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.52/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.52/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.52/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.52/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.52/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.52/1.85  
% 4.52/1.86  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 4.52/1.86  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.52/1.86  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.52/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.52/1.86  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 4.52/1.86  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.52/1.86  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.52/1.86  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.52/1.86  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.52/1.86  tff(c_16, plain, (![C_20, A_18, B_19]: (r1_tarski(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19)) | ~r1_tarski(A_18, B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.52/1.86  tff(c_27, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.86  tff(c_42, plain, (![B_25, A_26]: (r1_tarski(k3_xboole_0(B_25, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 4.52/1.86  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.52/1.86  tff(c_452, plain, (![A_80, B_81]: (k3_xboole_0(A_80, k9_relat_1(B_81, k1_relat_1(B_81)))=k9_relat_1(B_81, k10_relat_1(B_81, A_80)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.52/1.86  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.86  tff(c_705, plain, (![A_96, A_97, B_98]: (r1_tarski(A_96, A_97) | ~r1_tarski(A_96, k9_relat_1(B_98, k10_relat_1(B_98, A_97))) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_452, c_6])).
% 4.52/1.86  tff(c_2414, plain, (![C_216, A_217, A_218]: (r1_tarski(k9_relat_1(C_216, A_217), A_218) | ~v1_funct_1(C_216) | ~r1_tarski(A_217, k10_relat_1(C_216, A_218)) | ~v1_relat_1(C_216))), inference(resolution, [status(thm)], [c_16, c_705])).
% 4.52/1.86  tff(c_212, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k3_xboole_0(B_52, C_53)) | ~r1_tarski(A_51, C_53) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.86  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.52/1.86  tff(c_25, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 4.52/1.86  tff(c_225, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_212, c_25])).
% 4.52/1.86  tff(c_413, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_225])).
% 4.52/1.86  tff(c_2421, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2414, c_413])).
% 4.52/1.86  tff(c_2437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_22, c_2421])).
% 4.52/1.86  tff(c_2438, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_225])).
% 4.52/1.86  tff(c_2478, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_2438])).
% 4.52/1.86  tff(c_2482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_4, c_2478])).
% 4.52/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.86  
% 4.52/1.86  Inference rules
% 4.52/1.86  ----------------------
% 4.52/1.86  #Ref     : 0
% 4.52/1.86  #Sup     : 559
% 4.52/1.86  #Fact    : 0
% 4.52/1.86  #Define  : 0
% 4.52/1.87  #Split   : 1
% 4.52/1.87  #Chain   : 0
% 4.52/1.87  #Close   : 0
% 4.52/1.87  
% 4.52/1.87  Ordering : KBO
% 4.52/1.87  
% 4.52/1.87  Simplification rules
% 4.52/1.87  ----------------------
% 4.52/1.87  #Subsume      : 28
% 4.52/1.87  #Demod        : 206
% 4.52/1.87  #Tautology    : 221
% 4.52/1.87  #SimpNegUnit  : 0
% 4.52/1.87  #BackRed      : 0
% 4.52/1.87  
% 4.52/1.87  #Partial instantiations: 0
% 4.52/1.87  #Strategies tried      : 1
% 4.52/1.87  
% 4.52/1.87  Timing (in seconds)
% 4.52/1.87  ----------------------
% 4.52/1.87  Preprocessing        : 0.30
% 4.52/1.87  Parsing              : 0.16
% 4.52/1.87  CNF conversion       : 0.02
% 4.52/1.87  Main loop            : 0.83
% 4.52/1.87  Inferencing          : 0.25
% 4.52/1.87  Reduction            : 0.34
% 4.52/1.87  Demodulation         : 0.29
% 4.52/1.87  BG Simplification    : 0.03
% 4.52/1.87  Subsumption          : 0.17
% 4.52/1.87  Abstraction          : 0.03
% 4.52/1.87  MUC search           : 0.00
% 4.52/1.87  Cooper               : 0.00
% 4.52/1.87  Total                : 1.16
% 4.52/1.87  Index Insertion      : 0.00
% 4.52/1.87  Index Deletion       : 0.00
% 4.52/1.87  Index Matching       : 0.00
% 4.52/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
