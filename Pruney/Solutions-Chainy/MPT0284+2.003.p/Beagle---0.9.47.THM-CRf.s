%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  67 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_311,plain,(
    ! [A_57,B_58] : k2_xboole_0(k4_xboole_0(A_57,B_58),k4_xboole_0(B_58,A_57)) = k5_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [B_28,A_29] : k3_tarski(k2_tarski(B_28,A_29)) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_20,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_20])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(k2_xboole_0(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_169,plain,(
    ! [A_29,B_28] : r1_tarski(A_29,k2_xboole_0(B_28,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_162])).

tff(c_329,plain,(
    ! [B_58,A_57] : r1_tarski(k4_xboole_0(B_58,A_57),k5_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_169])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_zfmisc_1(A_19),k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_161,plain,(
    ! [A_34,B_36] : r1_tarski(A_34,k2_xboole_0(A_34,B_36)) ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_332,plain,(
    ! [A_57,B_58] : r1_tarski(k4_xboole_0(A_57,B_58),k5_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_161])).

tff(c_368,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(k2_xboole_0(A_63,C_64),B_65)
      | ~ r1_tarski(C_64,B_65)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_388,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_368,c_24])).

tff(c_741,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_1216,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_741])).

tff(c_1220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_1216])).

tff(c_1221,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_1912,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_1221])).

tff(c_1916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.61  
% 3.36/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.61  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.36/1.61  
% 3.36/1.61  %Foreground sorts:
% 3.36/1.61  
% 3.36/1.61  
% 3.36/1.61  %Background operators:
% 3.36/1.61  
% 3.36/1.61  
% 3.36/1.61  %Foreground operators:
% 3.36/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.61  
% 3.36/1.62  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.36/1.62  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.36/1.62  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.36/1.62  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.62  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.36/1.62  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.36/1.62  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.36/1.62  tff(f_58, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 3.36/1.62  tff(c_311, plain, (![A_57, B_58]: (k2_xboole_0(k4_xboole_0(A_57, B_58), k4_xboole_0(B_58, A_57))=k5_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.62  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.62  tff(c_60, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.62  tff(c_84, plain, (![B_28, A_29]: (k3_tarski(k2_tarski(B_28, A_29))=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_16, c_60])).
% 3.36/1.62  tff(c_20, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.62  tff(c_90, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_84, c_20])).
% 3.36/1.62  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.62  tff(c_150, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(k2_xboole_0(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.62  tff(c_162, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(resolution, [status(thm)], [c_8, c_150])).
% 3.36/1.62  tff(c_169, plain, (![A_29, B_28]: (r1_tarski(A_29, k2_xboole_0(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_162])).
% 3.36/1.62  tff(c_329, plain, (![B_58, A_57]: (r1_tarski(k4_xboole_0(B_58, A_57), k5_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_169])).
% 3.36/1.62  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(k1_zfmisc_1(A_19), k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.62  tff(c_161, plain, (![A_34, B_36]: (r1_tarski(A_34, k2_xboole_0(A_34, B_36)))), inference(resolution, [status(thm)], [c_8, c_150])).
% 3.36/1.62  tff(c_332, plain, (![A_57, B_58]: (r1_tarski(k4_xboole_0(A_57, B_58), k5_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_161])).
% 3.36/1.62  tff(c_368, plain, (![A_63, C_64, B_65]: (r1_tarski(k2_xboole_0(A_63, C_64), B_65) | ~r1_tarski(C_64, B_65) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.62  tff(c_24, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.62  tff(c_388, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_368, c_24])).
% 3.36/1.62  tff(c_741, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_388])).
% 3.36/1.62  tff(c_1216, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_741])).
% 3.36/1.62  tff(c_1220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_1216])).
% 3.36/1.62  tff(c_1221, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_388])).
% 3.36/1.62  tff(c_1912, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_1221])).
% 3.36/1.62  tff(c_1916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_1912])).
% 3.36/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.62  
% 3.36/1.62  Inference rules
% 3.36/1.62  ----------------------
% 3.36/1.62  #Ref     : 0
% 3.36/1.62  #Sup     : 467
% 3.36/1.62  #Fact    : 0
% 3.36/1.62  #Define  : 0
% 3.36/1.62  #Split   : 1
% 3.36/1.62  #Chain   : 0
% 3.36/1.62  #Close   : 0
% 3.36/1.62  
% 3.36/1.62  Ordering : KBO
% 3.36/1.62  
% 3.36/1.62  Simplification rules
% 3.36/1.62  ----------------------
% 3.36/1.62  #Subsume      : 25
% 3.36/1.62  #Demod        : 341
% 3.36/1.62  #Tautology    : 289
% 3.36/1.62  #SimpNegUnit  : 0
% 3.36/1.62  #BackRed      : 0
% 3.36/1.62  
% 3.36/1.62  #Partial instantiations: 0
% 3.36/1.62  #Strategies tried      : 1
% 3.36/1.62  
% 3.36/1.62  Timing (in seconds)
% 3.36/1.62  ----------------------
% 3.36/1.62  Preprocessing        : 0.33
% 3.36/1.62  Parsing              : 0.17
% 3.36/1.62  CNF conversion       : 0.02
% 3.36/1.62  Main loop            : 0.47
% 3.36/1.62  Inferencing          : 0.15
% 3.36/1.62  Reduction            : 0.20
% 3.36/1.62  Demodulation         : 0.17
% 3.36/1.62  BG Simplification    : 0.02
% 3.36/1.62  Subsumption          : 0.07
% 3.36/1.62  Abstraction          : 0.03
% 3.36/1.62  MUC search           : 0.00
% 3.36/1.62  Cooper               : 0.00
% 3.36/1.62  Total                : 0.83
% 3.36/1.62  Index Insertion      : 0.00
% 3.36/1.62  Index Deletion       : 0.00
% 3.36/1.62  Index Matching       : 0.00
% 3.36/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
