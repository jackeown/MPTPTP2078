%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:25 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 106 expanded)
%              Number of equality atoms :    7 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [A_90,B_91] :
      ( k2_xboole_0(k2_relat_1(A_90),k2_relat_1(B_91)) = k2_relat_1(k2_xboole_0(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(A_54,k2_xboole_0(B_55,C_56))
      | ~ r1_tarski(k4_xboole_0(A_54,B_55),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(B_55,k4_xboole_0(A_54,B_55))) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_109,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(B_55,A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_303,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(k2_relat_1(B_92),k2_relat_1(k2_xboole_0(A_93,B_92)))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_109])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k4_xboole_0(A_29,B_30))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k4_xboole_0(A_51,B_52),C_53)
      | ~ r1_tarski(A_51,k2_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_27,B_28] : k6_subset_1(A_27,B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_35,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_30])).

tff(c_97,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_91,c_35])).

tff(c_273,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_97])).

tff(c_291,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_273])).

tff(c_293,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_296,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_296])).

tff(c_301,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_306,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_303,c_301])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > #skF_2 > #skF_1
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.28  
% 2.12/1.29  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 2.12/1.29  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 2.12/1.29  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.12/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.29  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.12/1.29  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.12/1.29  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.12/1.29  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.12/1.29  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.29  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.29  tff(c_252, plain, (![A_90, B_91]: (k2_xboole_0(k2_relat_1(A_90), k2_relat_1(B_91))=k2_relat_1(k2_xboole_0(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.29  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.29  tff(c_99, plain, (![A_54, B_55, C_56]: (r1_tarski(A_54, k2_xboole_0(B_55, C_56)) | ~r1_tarski(k4_xboole_0(A_54, B_55), C_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.29  tff(c_106, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(B_55, k4_xboole_0(A_54, B_55))))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.12/1.29  tff(c_109, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(B_55, A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 2.12/1.29  tff(c_303, plain, (![B_92, A_93]: (r1_tarski(k2_relat_1(B_92), k2_relat_1(k2_xboole_0(A_93, B_92))) | ~v1_relat_1(B_92) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_252, c_109])).
% 2.12/1.29  tff(c_26, plain, (![A_29, B_30]: (v1_relat_1(k4_xboole_0(A_29, B_30)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.29  tff(c_91, plain, (![A_51, B_52, C_53]: (r1_tarski(k4_xboole_0(A_51, B_52), C_53) | ~r1_tarski(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.29  tff(c_24, plain, (![A_27, B_28]: (k6_subset_1(A_27, B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.29  tff(c_30, plain, (~r1_tarski(k6_subset_1(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.29  tff(c_35, plain, (~r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_30])).
% 2.12/1.29  tff(c_97, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_91, c_35])).
% 2.12/1.29  tff(c_273, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_252, c_97])).
% 2.12/1.29  tff(c_291, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_273])).
% 2.12/1.29  tff(c_293, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_291])).
% 2.12/1.29  tff(c_296, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_293])).
% 2.12/1.29  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_296])).
% 2.12/1.29  tff(c_301, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_291])).
% 2.12/1.29  tff(c_306, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_303, c_301])).
% 2.12/1.29  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_306])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 67
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 1
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 0
% 2.12/1.29  #Demod        : 15
% 2.12/1.29  #Tautology    : 23
% 2.12/1.29  #SimpNegUnit  : 0
% 2.12/1.29  #BackRed      : 0
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.30  Preprocessing        : 0.30
% 2.12/1.30  Parsing              : 0.16
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.21
% 2.12/1.30  Inferencing          : 0.08
% 2.12/1.30  Reduction            : 0.07
% 2.12/1.30  Demodulation         : 0.05
% 2.12/1.30  BG Simplification    : 0.01
% 2.12/1.30  Subsumption          : 0.04
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.54
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
