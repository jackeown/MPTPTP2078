%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  86 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_60,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [B_34,A_35] :
      ( k9_relat_1(B_34,k10_relat_1(B_34,A_35)) = A_35
      | ~ r1_tarski(A_35,k2_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,(
    ! [A_13,A_35] :
      ( k9_relat_1(k6_relat_1(A_13),k10_relat_1(k6_relat_1(A_13),A_35)) = A_35
      | ~ r1_tarski(A_35,A_13)
      | ~ v1_funct_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_99,plain,(
    ! [A_13,A_35] :
      ( k9_relat_1(k6_relat_1(A_13),k10_relat_1(k6_relat_1(A_13),A_35)) = A_35
      | ~ r1_tarski(A_35,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_97])).

tff(c_24,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [B_38,C_39,A_40] :
      ( k9_relat_1(k5_relat_1(B_38,C_39),A_40) = k9_relat_1(C_39,k9_relat_1(B_38,A_40))
      | ~ v1_relat_1(C_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_118,plain,(
    ! [A_17,B_18,A_40] :
      ( k9_relat_1(k6_relat_1(A_17),k9_relat_1(k6_relat_1(B_18),A_40)) = k9_relat_1(k6_relat_1(k3_xboole_0(A_17,B_18)),A_40)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(B_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_123,plain,(
    ! [A_41,B_42,A_43] : k9_relat_1(k6_relat_1(A_41),k9_relat_1(k6_relat_1(B_42),A_43)) = k9_relat_1(k6_relat_1(k3_xboole_0(A_41,B_42)),A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_118])).

tff(c_281,plain,(
    ! [A_54,A_55,A_56] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(A_54,A_55)),k10_relat_1(k6_relat_1(A_55),A_56)) = k9_relat_1(k6_relat_1(A_54),A_56)
      | ~ r1_tarski(A_56,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_123])).

tff(c_321,plain,(
    ! [A_57,A_58] :
      ( k9_relat_1(k6_relat_1(A_57),k10_relat_1(k6_relat_1(A_57),A_58)) = k9_relat_1(k6_relat_1(A_57),A_58)
      | ~ r1_tarski(A_58,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_370,plain,(
    ! [A_59,A_60] :
      ( k9_relat_1(k6_relat_1(A_59),A_60) = A_60
      | ~ r1_tarski(A_60,A_59)
      | ~ r1_tarski(A_60,A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_99])).

tff(c_26,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_406,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_26])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:33:10 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.37  
% 2.57/1.40  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.57/1.40  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.57/1.40  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.57/1.40  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.57/1.40  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.57/1.40  tff(f_60, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.57/1.40  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.57/1.40  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.40  tff(c_77, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.40  tff(c_85, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.57/1.40  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.40  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.57/1.40  tff(c_20, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.57/1.40  tff(c_16, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.40  tff(c_95, plain, (![B_34, A_35]: (k9_relat_1(B_34, k10_relat_1(B_34, A_35))=A_35 | ~r1_tarski(A_35, k2_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.40  tff(c_97, plain, (![A_13, A_35]: (k9_relat_1(k6_relat_1(A_13), k10_relat_1(k6_relat_1(A_13), A_35))=A_35 | ~r1_tarski(A_35, A_13) | ~v1_funct_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_95])).
% 2.57/1.40  tff(c_99, plain, (![A_13, A_35]: (k9_relat_1(k6_relat_1(A_13), k10_relat_1(k6_relat_1(A_13), A_35))=A_35 | ~r1_tarski(A_35, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_97])).
% 2.57/1.40  tff(c_24, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.40  tff(c_109, plain, (![B_38, C_39, A_40]: (k9_relat_1(k5_relat_1(B_38, C_39), A_40)=k9_relat_1(C_39, k9_relat_1(B_38, A_40)) | ~v1_relat_1(C_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.40  tff(c_118, plain, (![A_17, B_18, A_40]: (k9_relat_1(k6_relat_1(A_17), k9_relat_1(k6_relat_1(B_18), A_40))=k9_relat_1(k6_relat_1(k3_xboole_0(A_17, B_18)), A_40) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(B_18)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_109])).
% 2.57/1.40  tff(c_123, plain, (![A_41, B_42, A_43]: (k9_relat_1(k6_relat_1(A_41), k9_relat_1(k6_relat_1(B_42), A_43))=k9_relat_1(k6_relat_1(k3_xboole_0(A_41, B_42)), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_118])).
% 2.57/1.40  tff(c_281, plain, (![A_54, A_55, A_56]: (k9_relat_1(k6_relat_1(k3_xboole_0(A_54, A_55)), k10_relat_1(k6_relat_1(A_55), A_56))=k9_relat_1(k6_relat_1(A_54), A_56) | ~r1_tarski(A_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_99, c_123])).
% 2.57/1.40  tff(c_321, plain, (![A_57, A_58]: (k9_relat_1(k6_relat_1(A_57), k10_relat_1(k6_relat_1(A_57), A_58))=k9_relat_1(k6_relat_1(A_57), A_58) | ~r1_tarski(A_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_2, c_281])).
% 2.57/1.40  tff(c_370, plain, (![A_59, A_60]: (k9_relat_1(k6_relat_1(A_59), A_60)=A_60 | ~r1_tarski(A_60, A_59) | ~r1_tarski(A_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_321, c_99])).
% 2.57/1.40  tff(c_26, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.40  tff(c_406, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_370, c_26])).
% 2.57/1.40  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_406])).
% 2.57/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  Inference rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Ref     : 0
% 2.57/1.40  #Sup     : 95
% 2.57/1.40  #Fact    : 0
% 2.57/1.40  #Define  : 0
% 2.57/1.40  #Split   : 0
% 2.57/1.40  #Chain   : 0
% 2.57/1.40  #Close   : 0
% 2.57/1.40  
% 2.57/1.40  Ordering : KBO
% 2.57/1.40  
% 2.57/1.40  Simplification rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Subsume      : 0
% 2.57/1.40  #Demod        : 45
% 2.57/1.40  #Tautology    : 34
% 2.57/1.40  #SimpNegUnit  : 0
% 2.57/1.40  #BackRed      : 0
% 2.57/1.40  
% 2.57/1.40  #Partial instantiations: 0
% 2.57/1.40  #Strategies tried      : 1
% 2.57/1.40  
% 2.57/1.40  Timing (in seconds)
% 2.57/1.40  ----------------------
% 2.57/1.40  Preprocessing        : 0.29
% 2.57/1.40  Parsing              : 0.15
% 2.57/1.40  CNF conversion       : 0.02
% 2.57/1.40  Main loop            : 0.28
% 2.57/1.40  Inferencing          : 0.11
% 2.57/1.40  Reduction            : 0.10
% 2.57/1.40  Demodulation         : 0.08
% 2.57/1.41  BG Simplification    : 0.02
% 2.57/1.41  Subsumption          : 0.04
% 2.57/1.41  Abstraction          : 0.03
% 2.57/1.41  MUC search           : 0.00
% 2.57/1.41  Cooper               : 0.00
% 2.57/1.41  Total                : 0.61
% 2.57/1.41  Index Insertion      : 0.00
% 2.57/1.41  Index Deletion       : 0.00
% 2.57/1.41  Index Matching       : 0.00
% 2.57/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
