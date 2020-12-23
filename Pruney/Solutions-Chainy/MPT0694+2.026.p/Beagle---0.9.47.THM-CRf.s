%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  96 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [A_33,B_34] : r1_tarski(k3_xboole_0(A_33,B_34),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_18,plain,(
    ! [C_22,A_20,B_21] :
      ( r1_tarski(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21))
      | ~ r1_tarski(A_20,B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_35,B_36] : r1_tarski(k3_xboole_0(A_35,B_36),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_101,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_317,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k9_relat_1(B_72,k10_relat_1(B_72,A_73)),A_73)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1298,plain,(
    ! [A_151,A_152,B_153] :
      ( r1_tarski(A_151,A_152)
      | ~ r1_tarski(A_151,k9_relat_1(B_153,k10_relat_1(B_153,A_152)))
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_4903,plain,(
    ! [C_263,A_264,A_265] :
      ( r1_tarski(k9_relat_1(C_263,A_264),A_265)
      | ~ v1_funct_1(C_263)
      | ~ r1_tarski(A_264,k10_relat_1(C_263,A_265))
      | ~ v1_relat_1(C_263) ) ),
    inference(resolution,[status(thm)],[c_18,c_1298])).

tff(c_232,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k3_xboole_0(B_61,C_62))
      | ~ r1_tarski(A_60,C_62)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_245,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_27])).

tff(c_353,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_4951,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4903,c_353])).

tff(c_4980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_101,c_24,c_4951])).

tff(c_4981,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_5183,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4981])).

tff(c_5187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89,c_5183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:44:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/2.09  
% 5.10/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.09  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.18/2.09  
% 5.18/2.09  %Foreground sorts:
% 5.18/2.09  
% 5.18/2.09  
% 5.18/2.09  %Background operators:
% 5.18/2.09  
% 5.18/2.09  
% 5.18/2.09  %Foreground operators:
% 5.18/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.18/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.18/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.18/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.18/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.18/2.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.18/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.18/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.18/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.18/2.09  
% 5.18/2.11  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 5.18/2.11  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.18/2.11  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.18/2.11  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 5.18/2.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.18/2.11  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 5.18/2.11  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.18/2.11  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.18/2.11  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.18/2.11  tff(c_80, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.18/2.11  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.18/2.11  tff(c_89, plain, (![A_33, B_34]: (r1_tarski(k3_xboole_0(A_33, B_34), A_33))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 5.18/2.11  tff(c_18, plain, (![C_22, A_20, B_21]: (r1_tarski(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21)) | ~r1_tarski(A_20, B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.18/2.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/2.11  tff(c_98, plain, (![A_35, B_36]: (r1_tarski(k3_xboole_0(A_35, B_36), A_35))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 5.18/2.11  tff(c_101, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 5.18/2.11  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.18/2.11  tff(c_317, plain, (![B_72, A_73]: (r1_tarski(k9_relat_1(B_72, k10_relat_1(B_72, A_73)), A_73) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.18/2.11  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.18/2.11  tff(c_1298, plain, (![A_151, A_152, B_153]: (r1_tarski(A_151, A_152) | ~r1_tarski(A_151, k9_relat_1(B_153, k10_relat_1(B_153, A_152))) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(resolution, [status(thm)], [c_317, c_6])).
% 5.18/2.11  tff(c_4903, plain, (![C_263, A_264, A_265]: (r1_tarski(k9_relat_1(C_263, A_264), A_265) | ~v1_funct_1(C_263) | ~r1_tarski(A_264, k10_relat_1(C_263, A_265)) | ~v1_relat_1(C_263))), inference(resolution, [status(thm)], [c_18, c_1298])).
% 5.18/2.11  tff(c_232, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k3_xboole_0(B_61, C_62)) | ~r1_tarski(A_60, C_62) | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.18/2.11  tff(c_22, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.18/2.11  tff(c_27, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 5.18/2.11  tff(c_245, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_232, c_27])).
% 5.18/2.11  tff(c_353, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_245])).
% 5.18/2.11  tff(c_4951, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4903, c_353])).
% 5.18/2.11  tff(c_4980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_101, c_24, c_4951])).
% 5.18/2.11  tff(c_4981, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_245])).
% 5.18/2.11  tff(c_5183, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_4981])).
% 5.18/2.11  tff(c_5187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_89, c_5183])).
% 5.18/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.11  
% 5.18/2.11  Inference rules
% 5.18/2.11  ----------------------
% 5.18/2.11  #Ref     : 0
% 5.18/2.11  #Sup     : 1121
% 5.18/2.11  #Fact    : 0
% 5.18/2.11  #Define  : 0
% 5.18/2.11  #Split   : 1
% 5.18/2.11  #Chain   : 0
% 5.18/2.11  #Close   : 0
% 5.18/2.11  
% 5.18/2.11  Ordering : KBO
% 5.18/2.11  
% 5.18/2.11  Simplification rules
% 5.18/2.11  ----------------------
% 5.18/2.11  #Subsume      : 48
% 5.18/2.11  #Demod        : 300
% 5.18/2.11  #Tautology    : 322
% 5.18/2.11  #SimpNegUnit  : 0
% 5.18/2.11  #BackRed      : 0
% 5.18/2.11  
% 5.18/2.11  #Partial instantiations: 0
% 5.18/2.11  #Strategies tried      : 1
% 5.18/2.11  
% 5.18/2.11  Timing (in seconds)
% 5.18/2.11  ----------------------
% 5.18/2.11  Preprocessing        : 0.31
% 5.18/2.11  Parsing              : 0.17
% 5.18/2.11  CNF conversion       : 0.02
% 5.18/2.11  Main loop            : 0.97
% 5.18/2.11  Inferencing          : 0.27
% 5.18/2.11  Reduction            : 0.39
% 5.18/2.11  Demodulation         : 0.32
% 5.18/2.11  BG Simplification    : 0.03
% 5.18/2.11  Subsumption          : 0.21
% 5.18/2.11  Abstraction          : 0.04
% 5.18/2.11  MUC search           : 0.00
% 5.18/2.11  Cooper               : 0.00
% 5.18/2.11  Total                : 1.31
% 5.18/2.11  Index Insertion      : 0.00
% 5.18/2.11  Index Deletion       : 0.00
% 5.18/2.11  Index Matching       : 0.00
% 5.18/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
