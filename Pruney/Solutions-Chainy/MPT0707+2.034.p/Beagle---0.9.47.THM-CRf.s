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
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  86 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_58,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_57,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_11] : v1_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [B_33,A_34] :
      ( k9_relat_1(B_33,k10_relat_1(B_33,A_34)) = A_34
      | ~ r1_tarski(A_34,k2_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_109,plain,(
    ! [A_10,A_34] :
      ( k9_relat_1(k6_relat_1(A_10),k10_relat_1(k6_relat_1(A_10),A_34)) = A_34
      | ~ r1_tarski(A_34,A_10)
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_107])).

tff(c_112,plain,(
    ! [A_35,A_36] :
      ( k9_relat_1(k6_relat_1(A_35),k10_relat_1(k6_relat_1(A_35),A_36)) = A_36
      | ~ r1_tarski(A_36,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_109])).

tff(c_22,plain,(
    ! [B_15,A_14] : k5_relat_1(k6_relat_1(B_15),k6_relat_1(A_14)) = k6_relat_1(k3_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [B_27,C_28,A_29] :
      ( k9_relat_1(k5_relat_1(B_27,C_28),A_29) = k9_relat_1(C_28,k9_relat_1(B_27,A_29))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [A_14,B_15,A_29] :
      ( k9_relat_1(k6_relat_1(A_14),k9_relat_1(k6_relat_1(B_15),A_29)) = k9_relat_1(k6_relat_1(k3_xboole_0(A_14,B_15)),A_29)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_76])).

tff(c_89,plain,(
    ! [A_14,B_15,A_29] : k9_relat_1(k6_relat_1(A_14),k9_relat_1(k6_relat_1(B_15),A_29)) = k9_relat_1(k6_relat_1(k3_xboole_0(A_14,B_15)),A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_85])).

tff(c_208,plain,(
    ! [A_44,A_45,A_46] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(A_44,A_45)),k10_relat_1(k6_relat_1(A_45),A_46)) = k9_relat_1(k6_relat_1(A_44),A_46)
      | ~ r1_tarski(A_46,A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_89])).

tff(c_240,plain,(
    ! [A_47,A_48] :
      ( k9_relat_1(k6_relat_1(A_47),k10_relat_1(k6_relat_1(A_47),A_48)) = k9_relat_1(k6_relat_1(A_47),A_48)
      | ~ r1_tarski(A_48,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_111,plain,(
    ! [A_10,A_34] :
      ( k9_relat_1(k6_relat_1(A_10),k10_relat_1(k6_relat_1(A_10),A_34)) = A_34
      | ~ r1_tarski(A_34,A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_109])).

tff(c_279,plain,(
    ! [A_49,A_50] :
      ( k9_relat_1(k6_relat_1(A_49),A_50) = A_50
      | ~ r1_tarski(A_50,A_49)
      | ~ r1_tarski(A_50,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_111])).

tff(c_24,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_311,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_24])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.10/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.10/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.26  
% 2.26/1.27  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.26/1.27  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.26/1.27  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.26/1.27  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.26/1.27  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.26/1.27  tff(f_58, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.26/1.27  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.26/1.27  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.27  tff(c_57, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.27  tff(c_61, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.26/1.27  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.27  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.27  tff(c_18, plain, (![A_11]: (v1_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.27  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.27  tff(c_107, plain, (![B_33, A_34]: (k9_relat_1(B_33, k10_relat_1(B_33, A_34))=A_34 | ~r1_tarski(A_34, k2_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.27  tff(c_109, plain, (![A_10, A_34]: (k9_relat_1(k6_relat_1(A_10), k10_relat_1(k6_relat_1(A_10), A_34))=A_34 | ~r1_tarski(A_34, A_10) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_107])).
% 2.26/1.27  tff(c_112, plain, (![A_35, A_36]: (k9_relat_1(k6_relat_1(A_35), k10_relat_1(k6_relat_1(A_35), A_36))=A_36 | ~r1_tarski(A_36, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_109])).
% 2.26/1.27  tff(c_22, plain, (![B_15, A_14]: (k5_relat_1(k6_relat_1(B_15), k6_relat_1(A_14))=k6_relat_1(k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.27  tff(c_76, plain, (![B_27, C_28, A_29]: (k9_relat_1(k5_relat_1(B_27, C_28), A_29)=k9_relat_1(C_28, k9_relat_1(B_27, A_29)) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.27  tff(c_85, plain, (![A_14, B_15, A_29]: (k9_relat_1(k6_relat_1(A_14), k9_relat_1(k6_relat_1(B_15), A_29))=k9_relat_1(k6_relat_1(k3_xboole_0(A_14, B_15)), A_29) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(B_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_76])).
% 2.26/1.27  tff(c_89, plain, (![A_14, B_15, A_29]: (k9_relat_1(k6_relat_1(A_14), k9_relat_1(k6_relat_1(B_15), A_29))=k9_relat_1(k6_relat_1(k3_xboole_0(A_14, B_15)), A_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_85])).
% 2.26/1.27  tff(c_208, plain, (![A_44, A_45, A_46]: (k9_relat_1(k6_relat_1(k3_xboole_0(A_44, A_45)), k10_relat_1(k6_relat_1(A_45), A_46))=k9_relat_1(k6_relat_1(A_44), A_46) | ~r1_tarski(A_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_112, c_89])).
% 2.26/1.27  tff(c_240, plain, (![A_47, A_48]: (k9_relat_1(k6_relat_1(A_47), k10_relat_1(k6_relat_1(A_47), A_48))=k9_relat_1(k6_relat_1(A_47), A_48) | ~r1_tarski(A_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 2.26/1.27  tff(c_111, plain, (![A_10, A_34]: (k9_relat_1(k6_relat_1(A_10), k10_relat_1(k6_relat_1(A_10), A_34))=A_34 | ~r1_tarski(A_34, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_109])).
% 2.26/1.27  tff(c_279, plain, (![A_49, A_50]: (k9_relat_1(k6_relat_1(A_49), A_50)=A_50 | ~r1_tarski(A_50, A_49) | ~r1_tarski(A_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_240, c_111])).
% 2.26/1.27  tff(c_24, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.27  tff(c_311, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_24])).
% 2.26/1.27  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_311])).
% 2.26/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.27  
% 2.26/1.27  Inference rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Ref     : 0
% 2.26/1.27  #Sup     : 73
% 2.26/1.27  #Fact    : 0
% 2.26/1.27  #Define  : 0
% 2.26/1.27  #Split   : 0
% 2.26/1.27  #Chain   : 0
% 2.26/1.27  #Close   : 0
% 2.26/1.27  
% 2.26/1.27  Ordering : KBO
% 2.26/1.27  
% 2.26/1.27  Simplification rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Subsume      : 0
% 2.26/1.27  #Demod        : 35
% 2.26/1.27  #Tautology    : 27
% 2.26/1.27  #SimpNegUnit  : 0
% 2.26/1.27  #BackRed      : 0
% 2.26/1.27  
% 2.26/1.27  #Partial instantiations: 0
% 2.26/1.27  #Strategies tried      : 1
% 2.26/1.27  
% 2.26/1.27  Timing (in seconds)
% 2.26/1.27  ----------------------
% 2.26/1.27  Preprocessing        : 0.28
% 2.26/1.27  Parsing              : 0.16
% 2.26/1.27  CNF conversion       : 0.02
% 2.26/1.27  Main loop            : 0.23
% 2.26/1.27  Inferencing          : 0.10
% 2.26/1.27  Reduction            : 0.08
% 2.26/1.27  Demodulation         : 0.06
% 2.26/1.27  BG Simplification    : 0.02
% 2.26/1.28  Subsumption          : 0.03
% 2.26/1.28  Abstraction          : 0.02
% 2.26/1.28  MUC search           : 0.00
% 2.26/1.28  Cooper               : 0.00
% 2.26/1.28  Total                : 0.54
% 2.26/1.28  Index Insertion      : 0.00
% 2.26/1.28  Index Deletion       : 0.00
% 2.26/1.28  Index Matching       : 0.00
% 2.26/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
