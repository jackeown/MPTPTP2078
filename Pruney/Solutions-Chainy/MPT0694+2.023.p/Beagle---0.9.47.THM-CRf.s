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
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  90 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [C_21,A_19,B_20] :
      ( r1_tarski(k9_relat_1(C_21,A_19),k9_relat_1(C_21,B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [B_26,A_27] : r1_tarski(k3_xboole_0(B_26,A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_6])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k9_relat_1(B_50,k10_relat_1(B_50,A_51)),A_51)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_764,plain,(
    ! [A_106,A_107,B_108] :
      ( r1_tarski(A_106,A_107)
      | ~ r1_tarski(A_106,k9_relat_1(B_108,k10_relat_1(B_108,A_107)))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_187,c_10])).

tff(c_4721,plain,(
    ! [C_293,A_294,A_295] :
      ( r1_tarski(k9_relat_1(C_293,A_294),A_295)
      | ~ v1_funct_1(C_293)
      | ~ r1_tarski(A_294,k10_relat_1(C_293,A_295))
      | ~ v1_relat_1(C_293) ) ),
    inference(resolution,[status(thm)],[c_16,c_764])).

tff(c_249,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_tarski(A_58,k3_xboole_0(B_59,C_60))
      | ~ r1_tarski(A_58,C_60)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_266,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_25])).

tff(c_334,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_4771,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4721,c_334])).

tff(c_4803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_22,c_4771])).

tff(c_4804,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_4885,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_4804])).

tff(c_4889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6,c_4885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.32  
% 6.24/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.32  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.24/2.32  
% 6.24/2.32  %Foreground sorts:
% 6.24/2.32  
% 6.24/2.32  
% 6.24/2.32  %Background operators:
% 6.24/2.32  
% 6.24/2.32  
% 6.24/2.32  %Foreground operators:
% 6.24/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.24/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.24/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.24/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.24/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.24/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.24/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.24/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.24/2.32  
% 6.24/2.33  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 6.24/2.33  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.24/2.33  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 6.24/2.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.24/2.33  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.24/2.33  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.24/2.33  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.24/2.33  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.24/2.33  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.24/2.33  tff(c_16, plain, (![C_21, A_19, B_20]: (r1_tarski(k9_relat_1(C_21, A_19), k9_relat_1(C_21, B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.24/2.33  tff(c_27, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.24/2.33  tff(c_42, plain, (![B_26, A_27]: (r1_tarski(k3_xboole_0(B_26, A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_27, c_6])).
% 6.24/2.33  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.24/2.33  tff(c_187, plain, (![B_50, A_51]: (r1_tarski(k9_relat_1(B_50, k10_relat_1(B_50, A_51)), A_51) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.24/2.33  tff(c_10, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.24/2.33  tff(c_764, plain, (![A_106, A_107, B_108]: (r1_tarski(A_106, A_107) | ~r1_tarski(A_106, k9_relat_1(B_108, k10_relat_1(B_108, A_107))) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_187, c_10])).
% 6.24/2.33  tff(c_4721, plain, (![C_293, A_294, A_295]: (r1_tarski(k9_relat_1(C_293, A_294), A_295) | ~v1_funct_1(C_293) | ~r1_tarski(A_294, k10_relat_1(C_293, A_295)) | ~v1_relat_1(C_293))), inference(resolution, [status(thm)], [c_16, c_764])).
% 6.24/2.33  tff(c_249, plain, (![A_58, B_59, C_60]: (r1_tarski(A_58, k3_xboole_0(B_59, C_60)) | ~r1_tarski(A_58, C_60) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.24/2.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.24/2.33  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.24/2.33  tff(c_25, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 6.24/2.33  tff(c_266, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_249, c_25])).
% 6.24/2.33  tff(c_334, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_266])).
% 6.24/2.33  tff(c_4771, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4721, c_334])).
% 6.24/2.33  tff(c_4803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_22, c_4771])).
% 6.24/2.33  tff(c_4804, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_266])).
% 6.24/2.33  tff(c_4885, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_4804])).
% 6.24/2.33  tff(c_4889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_6, c_4885])).
% 6.24/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.33  
% 6.24/2.33  Inference rules
% 6.24/2.33  ----------------------
% 6.24/2.33  #Ref     : 0
% 6.24/2.33  #Sup     : 1159
% 6.24/2.33  #Fact    : 0
% 6.24/2.33  #Define  : 0
% 6.24/2.33  #Split   : 1
% 6.24/2.33  #Chain   : 0
% 6.24/2.33  #Close   : 0
% 6.24/2.33  
% 6.24/2.33  Ordering : KBO
% 6.24/2.33  
% 6.24/2.33  Simplification rules
% 6.24/2.33  ----------------------
% 6.24/2.33  #Subsume      : 104
% 6.24/2.33  #Demod        : 234
% 6.24/2.33  #Tautology    : 240
% 6.24/2.33  #SimpNegUnit  : 0
% 6.24/2.33  #BackRed      : 0
% 6.24/2.33  
% 6.24/2.33  #Partial instantiations: 0
% 6.24/2.33  #Strategies tried      : 1
% 6.24/2.33  
% 6.24/2.33  Timing (in seconds)
% 6.24/2.33  ----------------------
% 6.24/2.34  Preprocessing        : 0.28
% 6.24/2.34  Parsing              : 0.16
% 6.24/2.34  CNF conversion       : 0.02
% 6.24/2.34  Main loop            : 1.29
% 6.24/2.34  Inferencing          : 0.30
% 6.24/2.34  Reduction            : 0.49
% 6.24/2.34  Demodulation         : 0.42
% 6.24/2.34  BG Simplification    : 0.04
% 6.24/2.34  Subsumption          : 0.37
% 6.24/2.34  Abstraction          : 0.04
% 6.24/2.34  MUC search           : 0.00
% 6.24/2.34  Cooper               : 0.00
% 6.24/2.34  Total                : 1.60
% 6.24/2.34  Index Insertion      : 0.00
% 6.24/2.34  Index Deletion       : 0.00
% 6.24/2.34  Index Matching       : 0.00
% 6.24/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
