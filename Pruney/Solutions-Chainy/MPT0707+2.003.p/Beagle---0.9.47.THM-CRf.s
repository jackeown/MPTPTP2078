%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   54 (  60 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  56 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_151,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(B_43,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_12])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_117,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_117])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_189,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_125])).

tff(c_18,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [B_22,A_21] : k5_relat_1(k6_relat_1(B_22),k6_relat_1(A_21)) = k6_relat_1(k3_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    ! [B_49,A_50] :
      ( k9_relat_1(B_49,k2_relat_1(A_50)) = k2_relat_1(k5_relat_1(A_50,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_245,plain,(
    ! [A_20,B_49] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_20),B_49)) = k9_relat_1(B_49,A_20)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_236])).

tff(c_250,plain,(
    ! [A_51,B_52] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_51),B_52)) = k9_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_245])).

tff(c_262,plain,(
    ! [A_21,B_22] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_21,B_22))) = k9_relat_1(k6_relat_1(A_21),B_22)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_250])).

tff(c_266,plain,(
    ! [A_21,B_22] : k9_relat_1(k6_relat_1(A_21),B_22) = k3_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24,c_262])).

tff(c_28,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_267,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_28])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.18  
% 1.93/1.18  %Foreground sorts:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Background operators:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Foreground operators:
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.18  
% 1.93/1.19  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.93/1.19  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.93/1.19  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.93/1.19  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.93/1.19  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.93/1.19  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.93/1.19  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.93/1.19  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.93/1.19  tff(f_58, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.93/1.19  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 1.93/1.19  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.19  tff(c_93, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.19  tff(c_151, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(B_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 1.93/1.19  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.19  tff(c_174, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_151, c_12])).
% 1.93/1.19  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.19  tff(c_108, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.19  tff(c_116, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_108])).
% 1.93/1.19  tff(c_117, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.19  tff(c_121, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_116, c_117])).
% 1.93/1.19  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.19  tff(c_125, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 1.93/1.19  tff(c_189, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_174, c_125])).
% 1.93/1.19  tff(c_18, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.19  tff(c_24, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.19  tff(c_26, plain, (![B_22, A_21]: (k5_relat_1(k6_relat_1(B_22), k6_relat_1(A_21))=k6_relat_1(k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.19  tff(c_236, plain, (![B_49, A_50]: (k9_relat_1(B_49, k2_relat_1(A_50))=k2_relat_1(k5_relat_1(A_50, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.19  tff(c_245, plain, (![A_20, B_49]: (k2_relat_1(k5_relat_1(k6_relat_1(A_20), B_49))=k9_relat_1(B_49, A_20) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_236])).
% 1.93/1.19  tff(c_250, plain, (![A_51, B_52]: (k2_relat_1(k5_relat_1(k6_relat_1(A_51), B_52))=k9_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_245])).
% 1.93/1.19  tff(c_262, plain, (![A_21, B_22]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_21, B_22)))=k9_relat_1(k6_relat_1(A_21), B_22) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_250])).
% 1.93/1.19  tff(c_266, plain, (![A_21, B_22]: (k9_relat_1(k6_relat_1(A_21), B_22)=k3_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24, c_262])).
% 1.93/1.19  tff(c_28, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.19  tff(c_267, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_266, c_28])).
% 1.93/1.19  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_267])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 59
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 0
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 1
% 1.93/1.19  #Demod        : 11
% 1.93/1.19  #Tautology    : 49
% 1.93/1.19  #SimpNegUnit  : 0
% 1.93/1.19  #BackRed      : 1
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.20  Preprocessing        : 0.28
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.16
% 1.93/1.20  Inferencing          : 0.06
% 1.93/1.20  Reduction            : 0.06
% 1.93/1.20  Demodulation         : 0.04
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.02
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.47
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.20  Index Matching       : 0.00
% 1.93/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
