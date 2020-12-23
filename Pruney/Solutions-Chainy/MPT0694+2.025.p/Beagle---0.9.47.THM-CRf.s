%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  90 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3439,plain,(
    ! [C_256,A_257,B_258] :
      ( r1_tarski(k9_relat_1(C_256,A_257),k9_relat_1(C_256,B_258))
      | ~ r1_tarski(A_257,B_258)
      | ~ v1_relat_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [B_25,A_26] : r1_tarski(k3_xboole_0(B_25,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [C_20,A_18,B_19] :
      ( r1_tarski(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19))
      | ~ r1_tarski(A_18,B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_230,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k9_relat_1(B_54,k10_relat_1(B_54,A_55)),A_55)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_591,plain,(
    ! [A_93,A_94,B_95] :
      ( r1_tarski(A_93,A_94)
      | ~ r1_tarski(A_93,k9_relat_1(B_95,k10_relat_1(B_95,A_94)))
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_230,c_8])).

tff(c_3172,plain,(
    ! [C_233,A_234,A_235] :
      ( r1_tarski(k9_relat_1(C_233,A_234),A_235)
      | ~ v1_funct_1(C_233)
      | ~ r1_tarski(A_234,k10_relat_1(C_233,A_235))
      | ~ v1_relat_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_16,c_591])).

tff(c_286,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k3_xboole_0(B_60,C_61))
      | ~ r1_tarski(A_59,C_61)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_306,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_25])).

tff(c_382,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_3208,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3172,c_382])).

tff(c_3235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_22,c_3208])).

tff(c_3236,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_3442,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3439,c_3236])).

tff(c_3448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4,c_3442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:56:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.94  
% 4.66/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.94  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.66/1.94  
% 4.66/1.94  %Foreground sorts:
% 4.66/1.94  
% 4.66/1.94  
% 4.66/1.94  %Background operators:
% 4.66/1.94  
% 4.66/1.94  
% 4.66/1.94  %Foreground operators:
% 4.66/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.66/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.66/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.66/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.66/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.66/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/1.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.66/1.94  
% 4.66/1.95  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 4.66/1.95  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.66/1.95  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.66/1.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.66/1.95  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.66/1.95  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.66/1.95  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.66/1.95  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/1.95  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.95  tff(c_3439, plain, (![C_256, A_257, B_258]: (r1_tarski(k9_relat_1(C_256, A_257), k9_relat_1(C_256, B_258)) | ~r1_tarski(A_257, B_258) | ~v1_relat_1(C_256))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.95  tff(c_27, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.95  tff(c_42, plain, (![B_25, A_26]: (r1_tarski(k3_xboole_0(B_25, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 4.66/1.95  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/1.95  tff(c_16, plain, (![C_20, A_18, B_19]: (r1_tarski(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19)) | ~r1_tarski(A_18, B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.95  tff(c_230, plain, (![B_54, A_55]: (r1_tarski(k9_relat_1(B_54, k10_relat_1(B_54, A_55)), A_55) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.66/1.95  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.66/1.95  tff(c_591, plain, (![A_93, A_94, B_95]: (r1_tarski(A_93, A_94) | ~r1_tarski(A_93, k9_relat_1(B_95, k10_relat_1(B_95, A_94))) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_230, c_8])).
% 4.66/1.95  tff(c_3172, plain, (![C_233, A_234, A_235]: (r1_tarski(k9_relat_1(C_233, A_234), A_235) | ~v1_funct_1(C_233) | ~r1_tarski(A_234, k10_relat_1(C_233, A_235)) | ~v1_relat_1(C_233))), inference(resolution, [status(thm)], [c_16, c_591])).
% 4.66/1.95  tff(c_286, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k3_xboole_0(B_60, C_61)) | ~r1_tarski(A_59, C_61) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.95  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/1.95  tff(c_25, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 4.66/1.95  tff(c_306, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_286, c_25])).
% 4.66/1.95  tff(c_382, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_306])).
% 4.66/1.95  tff(c_3208, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3172, c_382])).
% 4.66/1.95  tff(c_3235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_22, c_3208])).
% 4.66/1.95  tff(c_3236, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_306])).
% 4.66/1.95  tff(c_3442, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3439, c_3236])).
% 4.66/1.95  tff(c_3448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_4, c_3442])).
% 4.66/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.95  
% 4.66/1.95  Inference rules
% 4.66/1.95  ----------------------
% 4.66/1.95  #Ref     : 0
% 4.66/1.95  #Sup     : 784
% 4.66/1.95  #Fact    : 0
% 4.66/1.95  #Define  : 0
% 4.66/1.95  #Split   : 1
% 4.66/1.95  #Chain   : 0
% 4.66/1.95  #Close   : 0
% 4.66/1.95  
% 4.66/1.95  Ordering : KBO
% 4.66/1.95  
% 4.66/1.95  Simplification rules
% 4.66/1.95  ----------------------
% 4.66/1.95  #Subsume      : 39
% 4.66/1.95  #Demod        : 187
% 4.66/1.95  #Tautology    : 197
% 4.66/1.95  #SimpNegUnit  : 0
% 4.66/1.95  #BackRed      : 0
% 4.66/1.95  
% 4.66/1.95  #Partial instantiations: 0
% 4.66/1.95  #Strategies tried      : 1
% 4.66/1.95  
% 4.66/1.95  Timing (in seconds)
% 4.66/1.95  ----------------------
% 4.66/1.96  Preprocessing        : 0.29
% 4.66/1.96  Parsing              : 0.15
% 4.66/1.96  CNF conversion       : 0.02
% 4.66/1.96  Main loop            : 0.92
% 4.66/1.96  Inferencing          : 0.26
% 4.66/1.96  Reduction            : 0.37
% 4.66/1.96  Demodulation         : 0.32
% 4.66/1.96  BG Simplification    : 0.03
% 4.66/1.96  Subsumption          : 0.20
% 4.66/1.96  Abstraction          : 0.03
% 4.66/1.96  MUC search           : 0.00
% 4.66/1.96  Cooper               : 0.00
% 4.66/1.96  Total                : 1.23
% 4.66/1.96  Index Insertion      : 0.00
% 4.66/1.96  Index Deletion       : 0.00
% 4.66/1.96  Index Matching       : 0.00
% 4.66/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
