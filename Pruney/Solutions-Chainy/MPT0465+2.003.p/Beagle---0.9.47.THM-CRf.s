%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   51 (  84 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 137 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k6_subset_1(k5_relat_1(A,B),k5_relat_1(A,C)),k5_relat_1(A,k6_subset_1(B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(A,k2_xboole_0(B,C)) = k2_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_247,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_xboole_0(k5_relat_1(A_60,B_61),k5_relat_1(A_60,C_62)) = k5_relat_1(A_60,k2_xboole_0(B_61,C_62))
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [B_37,A_38] : k3_tarski(k2_tarski(B_37,A_38)) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_491,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(k5_relat_1(A_91,C_92),k5_relat_1(A_91,k2_xboole_0(B_93,C_92)))
      | ~ v1_relat_1(C_92)
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_123])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k4_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,B_20,C_22] :
      ( k2_xboole_0(k5_relat_1(A_16,B_20),k5_relat_1(A_16,C_22)) = k5_relat_1(A_16,k2_xboole_0(B_20,C_22))
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k4_xboole_0(A_49,B_50),C_51)
      | ~ r1_tarski(A_49,k2_xboole_0(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k6_subset_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_18])).

tff(c_201,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k2_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_197,c_25])).

tff(c_321,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_201])).

tff(c_323,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_2,c_321])).

tff(c_356,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_372,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_356])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_372])).

tff(c_377,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_494,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_491,c_377])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_22,c_494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.43  
% 2.34/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.43  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.34/1.43  
% 2.34/1.43  %Foreground sorts:
% 2.34/1.43  
% 2.34/1.43  
% 2.34/1.43  %Background operators:
% 2.34/1.43  
% 2.34/1.43  
% 2.34/1.43  %Foreground operators:
% 2.34/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.34/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.34/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.34/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.43  
% 2.34/1.44  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k5_relat_1(A, B), k5_relat_1(A, C)), k5_relat_1(A, k6_subset_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relat_1)).
% 2.34/1.44  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(A, k2_xboole_0(B, C)) = k2_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_relat_1)).
% 2.34/1.44  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.34/1.44  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.34/1.44  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.34/1.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.34/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.34/1.44  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.34/1.44  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.34/1.44  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.44  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.44  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.44  tff(c_247, plain, (![A_60, B_61, C_62]: (k2_xboole_0(k5_relat_1(A_60, B_61), k5_relat_1(A_60, C_62))=k5_relat_1(A_60, k2_xboole_0(B_61, C_62)) | ~v1_relat_1(C_62) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.44  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.44  tff(c_70, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.44  tff(c_85, plain, (![B_37, A_38]: (k3_tarski(k2_tarski(B_37, A_38))=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_70])).
% 2.34/1.44  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.44  tff(c_108, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 2.34/1.44  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.44  tff(c_123, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6])).
% 2.34/1.44  tff(c_491, plain, (![A_91, C_92, B_93]: (r1_tarski(k5_relat_1(A_91, C_92), k5_relat_1(A_91, k2_xboole_0(B_93, C_92))) | ~v1_relat_1(C_92) | ~v1_relat_1(B_93) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_247, c_123])).
% 2.34/1.44  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k4_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.44  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.44  tff(c_16, plain, (![A_16, B_20, C_22]: (k2_xboole_0(k5_relat_1(A_16, B_20), k5_relat_1(A_16, C_22))=k5_relat_1(A_16, k2_xboole_0(B_20, C_22)) | ~v1_relat_1(C_22) | ~v1_relat_1(B_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.44  tff(c_197, plain, (![A_49, B_50, C_51]: (r1_tarski(k4_xboole_0(A_49, B_50), C_51) | ~r1_tarski(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.44  tff(c_12, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.44  tff(c_18, plain, (~r1_tarski(k6_subset_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k6_subset_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.44  tff(c_25, plain, (~r1_tarski(k4_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_18])).
% 2.34/1.44  tff(c_201, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k2_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_197, c_25])).
% 2.34/1.44  tff(c_321, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3')))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_201])).
% 2.34/1.44  tff(c_323, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_2, c_321])).
% 2.34/1.44  tff(c_356, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_323])).
% 2.34/1.44  tff(c_372, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_356])).
% 2.34/1.44  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_372])).
% 2.34/1.44  tff(c_377, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_323])).
% 2.34/1.44  tff(c_494, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_491, c_377])).
% 2.34/1.44  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_22, c_494])).
% 2.34/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.44  
% 2.34/1.44  Inference rules
% 2.34/1.44  ----------------------
% 2.34/1.44  #Ref     : 0
% 2.34/1.44  #Sup     : 128
% 2.34/1.44  #Fact    : 0
% 2.34/1.44  #Define  : 0
% 2.34/1.44  #Split   : 1
% 2.34/1.44  #Chain   : 0
% 2.34/1.44  #Close   : 0
% 2.34/1.44  
% 2.34/1.44  Ordering : KBO
% 2.34/1.44  
% 2.34/1.44  Simplification rules
% 2.34/1.44  ----------------------
% 2.34/1.44  #Subsume      : 1
% 2.34/1.44  #Demod        : 39
% 2.34/1.44  #Tautology    : 56
% 2.34/1.44  #SimpNegUnit  : 0
% 2.34/1.44  #BackRed      : 0
% 2.34/1.44  
% 2.34/1.44  #Partial instantiations: 0
% 2.34/1.44  #Strategies tried      : 1
% 2.34/1.44  
% 2.34/1.44  Timing (in seconds)
% 2.34/1.44  ----------------------
% 2.34/1.45  Preprocessing        : 0.36
% 2.34/1.45  Parsing              : 0.19
% 2.34/1.45  CNF conversion       : 0.02
% 2.34/1.45  Main loop            : 0.29
% 2.34/1.45  Inferencing          : 0.10
% 2.34/1.45  Reduction            : 0.10
% 2.34/1.45  Demodulation         : 0.08
% 2.34/1.45  BG Simplification    : 0.02
% 2.34/1.45  Subsumption          : 0.06
% 2.34/1.45  Abstraction          : 0.01
% 2.34/1.45  MUC search           : 0.00
% 2.34/1.45  Cooper               : 0.00
% 2.34/1.45  Total                : 0.68
% 2.34/1.45  Index Insertion      : 0.00
% 2.34/1.45  Index Deletion       : 0.00
% 2.34/1.45  Index Matching       : 0.00
% 2.34/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
