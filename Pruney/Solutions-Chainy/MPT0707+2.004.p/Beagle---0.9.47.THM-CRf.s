%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [B_33,A_34] : k1_setfam_1(k2_tarski(B_33,A_34)) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_8])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_89,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_83,c_89])).

tff(c_160,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_93])).

tff(c_14,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_207,plain,(
    ! [B_39,A_40] :
      ( k9_relat_1(B_39,k2_relat_1(A_40)) = k2_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_216,plain,(
    ! [A_15,B_39] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_15),B_39)) = k9_relat_1(B_39,A_15)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_221,plain,(
    ! [A_41,B_42] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_41),B_42)) = k9_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_216])).

tff(c_233,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_16,B_17))) = k9_relat_1(k6_relat_1(A_16),B_17)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_221])).

tff(c_237,plain,(
    ! [A_16,B_17] : k9_relat_1(k6_relat_1(A_16),B_17) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_233])).

tff(c_24,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_238,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_24])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.58  
% 2.33/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.58  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.33/1.58  
% 2.33/1.58  %Foreground sorts:
% 2.33/1.58  
% 2.33/1.58  
% 2.33/1.58  %Background operators:
% 2.33/1.58  
% 2.33/1.58  
% 2.33/1.58  %Foreground operators:
% 2.33/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.33/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.58  
% 2.33/1.60  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.33/1.60  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.33/1.60  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.33/1.60  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.60  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.33/1.60  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.33/1.60  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.33/1.60  tff(f_54, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.33/1.60  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.33/1.60  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.60  tff(c_107, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.60  tff(c_122, plain, (![B_33, A_34]: (k1_setfam_1(k2_tarski(B_33, A_34))=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 2.33/1.60  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.60  tff(c_145, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_122, c_8])).
% 2.33/1.60  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.60  tff(c_79, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.60  tff(c_83, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.33/1.60  tff(c_89, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.60  tff(c_93, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_83, c_89])).
% 2.33/1.60  tff(c_160, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_145, c_93])).
% 2.33/1.60  tff(c_14, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.60  tff(c_20, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.60  tff(c_22, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.60  tff(c_207, plain, (![B_39, A_40]: (k9_relat_1(B_39, k2_relat_1(A_40))=k2_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.60  tff(c_216, plain, (![A_15, B_39]: (k2_relat_1(k5_relat_1(k6_relat_1(A_15), B_39))=k9_relat_1(B_39, A_15) | ~v1_relat_1(B_39) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_207])).
% 2.33/1.60  tff(c_221, plain, (![A_41, B_42]: (k2_relat_1(k5_relat_1(k6_relat_1(A_41), B_42))=k9_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_216])).
% 2.33/1.60  tff(c_233, plain, (![A_16, B_17]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_16, B_17)))=k9_relat_1(k6_relat_1(A_16), B_17) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_221])).
% 2.33/1.60  tff(c_237, plain, (![A_16, B_17]: (k9_relat_1(k6_relat_1(A_16), B_17)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_233])).
% 2.33/1.60  tff(c_24, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.60  tff(c_238, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_24])).
% 2.33/1.60  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_238])).
% 2.33/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.60  
% 2.33/1.60  Inference rules
% 2.33/1.60  ----------------------
% 2.33/1.60  #Ref     : 0
% 2.33/1.60  #Sup     : 52
% 2.33/1.60  #Fact    : 0
% 2.33/1.60  #Define  : 0
% 2.33/1.60  #Split   : 0
% 2.33/1.60  #Chain   : 0
% 2.33/1.60  #Close   : 0
% 2.33/1.60  
% 2.33/1.60  Ordering : KBO
% 2.33/1.60  
% 2.33/1.60  Simplification rules
% 2.33/1.60  ----------------------
% 2.33/1.60  #Subsume      : 1
% 2.33/1.60  #Demod        : 11
% 2.33/1.60  #Tautology    : 43
% 2.33/1.60  #SimpNegUnit  : 0
% 2.33/1.60  #BackRed      : 1
% 2.33/1.60  
% 2.33/1.60  #Partial instantiations: 0
% 2.33/1.60  #Strategies tried      : 1
% 2.33/1.60  
% 2.33/1.60  Timing (in seconds)
% 2.33/1.60  ----------------------
% 2.33/1.60  Preprocessing        : 0.45
% 2.33/1.60  Parsing              : 0.23
% 2.33/1.60  CNF conversion       : 0.03
% 2.33/1.60  Main loop            : 0.25
% 2.33/1.60  Inferencing          : 0.10
% 2.33/1.60  Reduction            : 0.09
% 2.33/1.60  Demodulation         : 0.07
% 2.33/1.61  BG Simplification    : 0.02
% 2.33/1.61  Subsumption          : 0.03
% 2.33/1.61  Abstraction          : 0.02
% 2.33/1.61  MUC search           : 0.00
% 2.33/1.61  Cooper               : 0.00
% 2.33/1.61  Total                : 0.75
% 2.33/1.61  Index Insertion      : 0.00
% 2.33/1.61  Index Deletion       : 0.00
% 2.33/1.61  Index Matching       : 0.00
% 2.33/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
