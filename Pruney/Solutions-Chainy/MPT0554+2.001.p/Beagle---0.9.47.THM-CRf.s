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
% DateTime   : Thu Dec  3 10:01:03 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 (  83 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(B_32,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_78])).

tff(c_20,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    ! [B_32,A_31] : k2_xboole_0(B_32,A_31) = k2_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_186,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,'#skF_2')
      | ~ r1_tarski(A_39,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_186])).

tff(c_399,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k2_xboole_0(B_66,C_67))
      | ~ r1_tarski(k4_xboole_0(A_65,B_66),C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_485,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,k2_xboole_0(B_74,'#skF_2'))
      | ~ r1_tarski(k4_xboole_0(A_73,B_74),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_198,c_399])).

tff(c_710,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,k2_xboole_0(B_93,'#skF_2'))
      | ~ r1_tarski(A_92,k2_xboole_0(B_93,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_485])).

tff(c_751,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,'#skF_2')
      | ~ r1_tarski(A_92,k2_xboole_0('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_710])).

tff(c_762,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,'#skF_2')
      | ~ r1_tarski(A_94,k2_xboole_0('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_751])).

tff(c_800,plain,(
    r1_tarski(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_762])).

tff(c_130,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(B_38,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [B_38,A_37] :
      ( k2_xboole_0(B_38,A_37) = A_37
      | ~ r1_tarski(k2_xboole_0(B_38,A_37),A_37) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_836,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_800,c_181])).

tff(c_541,plain,(
    ! [C_79,A_80,B_81] :
      ( k2_xboole_0(k9_relat_1(C_79,A_80),k9_relat_1(C_79,B_81)) = k9_relat_1(C_79,k2_xboole_0(A_80,B_81))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_574,plain,(
    ! [C_79,A_80,B_81] :
      ( r1_tarski(k9_relat_1(C_79,A_80),k9_relat_1(C_79,k2_xboole_0(A_80,B_81)))
      | ~ v1_relat_1(C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_16])).

tff(c_992,plain,(
    ! [C_101] :
      ( r1_tarski(k9_relat_1(C_101,'#skF_1'),k9_relat_1(C_101,'#skF_2'))
      | ~ v1_relat_1(C_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_574])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1001,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_992,c_24])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.43  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.63/1.43  
% 2.63/1.43  %Foreground sorts:
% 2.63/1.43  
% 2.63/1.43  
% 2.63/1.43  %Background operators:
% 2.63/1.43  
% 2.63/1.43  
% 2.63/1.43  %Foreground operators:
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.43  
% 3.01/1.44  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.01/1.44  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.01/1.44  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.01/1.44  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.01/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.01/1.44  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.01/1.44  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.01/1.44  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.01/1.44  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.01/1.44  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 3.01/1.44  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.44  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.44  tff(c_18, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.44  tff(c_78, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.45  tff(c_93, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(B_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_18, c_78])).
% 3.01/1.45  tff(c_20, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.45  tff(c_99, plain, (![B_32, A_31]: (k2_xboole_0(B_32, A_31)=k2_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 3.01/1.45  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.45  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.45  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.45  tff(c_186, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.45  tff(c_198, plain, (![A_39]: (r1_tarski(A_39, '#skF_2') | ~r1_tarski(A_39, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_186])).
% 3.01/1.45  tff(c_399, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k2_xboole_0(B_66, C_67)) | ~r1_tarski(k4_xboole_0(A_65, B_66), C_67))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.01/1.45  tff(c_485, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(B_74, '#skF_2')) | ~r1_tarski(k4_xboole_0(A_73, B_74), '#skF_1'))), inference(resolution, [status(thm)], [c_198, c_399])).
% 3.01/1.45  tff(c_710, plain, (![A_92, B_93]: (r1_tarski(A_92, k2_xboole_0(B_93, '#skF_2')) | ~r1_tarski(A_92, k2_xboole_0(B_93, '#skF_1')))), inference(resolution, [status(thm)], [c_12, c_485])).
% 3.01/1.45  tff(c_751, plain, (![A_92]: (r1_tarski(A_92, '#skF_2') | ~r1_tarski(A_92, k2_xboole_0('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_710])).
% 3.01/1.45  tff(c_762, plain, (![A_94]: (r1_tarski(A_94, '#skF_2') | ~r1_tarski(A_94, k2_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_751])).
% 3.01/1.45  tff(c_800, plain, (r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_8, c_762])).
% 3.01/1.45  tff(c_130, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 3.01/1.45  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.45  tff(c_169, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(B_38, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 3.01/1.45  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.45  tff(c_181, plain, (![B_38, A_37]: (k2_xboole_0(B_38, A_37)=A_37 | ~r1_tarski(k2_xboole_0(B_38, A_37), A_37))), inference(resolution, [status(thm)], [c_169, c_4])).
% 3.01/1.45  tff(c_836, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_800, c_181])).
% 3.01/1.45  tff(c_541, plain, (![C_79, A_80, B_81]: (k2_xboole_0(k9_relat_1(C_79, A_80), k9_relat_1(C_79, B_81))=k9_relat_1(C_79, k2_xboole_0(A_80, B_81)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.45  tff(c_574, plain, (![C_79, A_80, B_81]: (r1_tarski(k9_relat_1(C_79, A_80), k9_relat_1(C_79, k2_xboole_0(A_80, B_81))) | ~v1_relat_1(C_79))), inference(superposition, [status(thm), theory('equality')], [c_541, c_16])).
% 3.01/1.45  tff(c_992, plain, (![C_101]: (r1_tarski(k9_relat_1(C_101, '#skF_1'), k9_relat_1(C_101, '#skF_2')) | ~v1_relat_1(C_101))), inference(superposition, [status(thm), theory('equality')], [c_836, c_574])).
% 3.01/1.45  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.45  tff(c_1001, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_992, c_24])).
% 3.01/1.45  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1001])).
% 3.01/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.45  
% 3.01/1.45  Inference rules
% 3.01/1.45  ----------------------
% 3.01/1.45  #Ref     : 0
% 3.01/1.45  #Sup     : 244
% 3.01/1.45  #Fact    : 0
% 3.01/1.45  #Define  : 0
% 3.01/1.45  #Split   : 1
% 3.01/1.45  #Chain   : 0
% 3.01/1.45  #Close   : 0
% 3.01/1.45  
% 3.01/1.45  Ordering : KBO
% 3.01/1.45  
% 3.01/1.45  Simplification rules
% 3.01/1.45  ----------------------
% 3.01/1.45  #Subsume      : 59
% 3.01/1.45  #Demod        : 79
% 3.01/1.45  #Tautology    : 76
% 3.01/1.45  #SimpNegUnit  : 0
% 3.01/1.45  #BackRed      : 1
% 3.01/1.45  
% 3.01/1.45  #Partial instantiations: 0
% 3.01/1.45  #Strategies tried      : 1
% 3.01/1.45  
% 3.01/1.45  Timing (in seconds)
% 3.01/1.45  ----------------------
% 3.01/1.45  Preprocessing        : 0.28
% 3.01/1.45  Parsing              : 0.16
% 3.01/1.45  CNF conversion       : 0.02
% 3.01/1.45  Main loop            : 0.40
% 3.01/1.45  Inferencing          : 0.14
% 3.01/1.45  Reduction            : 0.13
% 3.01/1.45  Demodulation         : 0.10
% 3.01/1.45  BG Simplification    : 0.02
% 3.01/1.45  Subsumption          : 0.09
% 3.01/1.45  Abstraction          : 0.02
% 3.01/1.45  MUC search           : 0.00
% 3.01/1.45  Cooper               : 0.00
% 3.01/1.45  Total                : 0.71
% 3.01/1.45  Index Insertion      : 0.00
% 3.01/1.45  Index Deletion       : 0.00
% 3.01/1.45  Index Matching       : 0.00
% 3.01/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
