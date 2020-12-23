%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  86 expanded)
%              Number of equality atoms :   35 (  49 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_16,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [B_39,A_40] : k5_relat_1(k6_relat_1(B_39),k6_relat_1(A_40)) = k6_relat_1(k3_xboole_0(A_40,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_187,plain,(
    ! [A_40,B_39] :
      ( k7_relat_1(k6_relat_1(A_40),B_39) = k6_relat_1(k3_xboole_0(A_40,B_39))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_20])).

tff(c_197,plain,(
    ! [A_40,B_39] : k7_relat_1(k6_relat_1(A_40),B_39) = k6_relat_1(k3_xboole_0(A_40,B_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_187])).

tff(c_211,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,(
    ! [A_13,A_44] :
      ( k7_relat_1(k6_relat_1(A_13),A_44) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_44)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_211])).

tff(c_217,plain,(
    ! [A_45,A_46] :
      ( k6_relat_1(k3_xboole_0(A_45,A_46)) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_197,c_214])).

tff(c_235,plain,(
    ! [A_45,A_46] :
      ( k3_xboole_0(A_45,A_46) = k1_relat_1(k6_relat_1(A_45))
      | ~ r1_tarski(A_45,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_16])).

tff(c_258,plain,(
    ! [A_47,A_48] :
      ( k3_xboole_0(A_47,A_48) = A_47
      | ~ r1_tarski(A_47,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_235])).

tff(c_262,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_100,c_258])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(B_34,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_34,A_33] : k3_xboole_0(B_34,A_33) = k3_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_269,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_121])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,(
    ! [B_49,A_50] :
      ( k9_relat_1(B_49,k2_relat_1(A_50)) = k2_relat_1(k5_relat_1(A_50,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_302,plain,(
    ! [A_13,B_49] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_13),B_49)) = k9_relat_1(B_49,A_13)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_293])).

tff(c_372,plain,(
    ! [A_55,B_56] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_55),B_56)) = k9_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_302])).

tff(c_390,plain,(
    ! [A_18,B_19] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_18,B_19))) = k9_relat_1(k6_relat_1(A_18),B_19)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_372])).

tff(c_397,plain,(
    ! [A_18,B_19] : k9_relat_1(k6_relat_1(A_18),B_19) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_390])).

tff(c_26,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_398,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_26])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.18/1.24  
% 2.18/1.24  %Foreground sorts:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Background operators:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Foreground operators:
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.24  
% 2.18/1.26  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.18/1.26  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.26  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.18/1.26  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.18/1.26  tff(f_60, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.18/1.26  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.18/1.26  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.18/1.26  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.18/1.26  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.26  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.18/1.26  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.26  tff(c_96, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.26  tff(c_100, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_96])).
% 2.18/1.26  tff(c_16, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.26  tff(c_12, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.26  tff(c_181, plain, (![B_39, A_40]: (k5_relat_1(k6_relat_1(B_39), k6_relat_1(A_40))=k6_relat_1(k3_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.26  tff(c_20, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.26  tff(c_187, plain, (![A_40, B_39]: (k7_relat_1(k6_relat_1(A_40), B_39)=k6_relat_1(k3_xboole_0(A_40, B_39)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_20])).
% 2.18/1.26  tff(c_197, plain, (![A_40, B_39]: (k7_relat_1(k6_relat_1(A_40), B_39)=k6_relat_1(k3_xboole_0(A_40, B_39)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_187])).
% 2.18/1.26  tff(c_211, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.26  tff(c_214, plain, (![A_13, A_44]: (k7_relat_1(k6_relat_1(A_13), A_44)=k6_relat_1(A_13) | ~r1_tarski(A_13, A_44) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_211])).
% 2.18/1.26  tff(c_217, plain, (![A_45, A_46]: (k6_relat_1(k3_xboole_0(A_45, A_46))=k6_relat_1(A_45) | ~r1_tarski(A_45, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_197, c_214])).
% 2.18/1.26  tff(c_235, plain, (![A_45, A_46]: (k3_xboole_0(A_45, A_46)=k1_relat_1(k6_relat_1(A_45)) | ~r1_tarski(A_45, A_46))), inference(superposition, [status(thm), theory('equality')], [c_217, c_16])).
% 2.18/1.26  tff(c_258, plain, (![A_47, A_48]: (k3_xboole_0(A_47, A_48)=A_47 | ~r1_tarski(A_47, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_235])).
% 2.18/1.26  tff(c_262, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_100, c_258])).
% 2.18/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.26  tff(c_81, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.26  tff(c_115, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(B_34, A_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_81])).
% 2.18/1.26  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.26  tff(c_121, plain, (![B_34, A_33]: (k3_xboole_0(B_34, A_33)=k3_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 2.18/1.26  tff(c_269, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_262, c_121])).
% 2.18/1.26  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.26  tff(c_24, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.26  tff(c_293, plain, (![B_49, A_50]: (k9_relat_1(B_49, k2_relat_1(A_50))=k2_relat_1(k5_relat_1(A_50, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.26  tff(c_302, plain, (![A_13, B_49]: (k2_relat_1(k5_relat_1(k6_relat_1(A_13), B_49))=k9_relat_1(B_49, A_13) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_293])).
% 2.18/1.26  tff(c_372, plain, (![A_55, B_56]: (k2_relat_1(k5_relat_1(k6_relat_1(A_55), B_56))=k9_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_302])).
% 2.18/1.26  tff(c_390, plain, (![A_18, B_19]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_18, B_19)))=k9_relat_1(k6_relat_1(A_18), B_19) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_372])).
% 2.18/1.26  tff(c_397, plain, (![A_18, B_19]: (k9_relat_1(k6_relat_1(A_18), B_19)=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_390])).
% 2.18/1.26  tff(c_26, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.26  tff(c_398, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_26])).
% 2.18/1.26  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_398])).
% 2.18/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  Inference rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Ref     : 0
% 2.18/1.26  #Sup     : 91
% 2.18/1.26  #Fact    : 0
% 2.18/1.26  #Define  : 0
% 2.18/1.26  #Split   : 1
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 7
% 2.18/1.26  #Demod        : 31
% 2.18/1.26  #Tautology    : 57
% 2.18/1.26  #SimpNegUnit  : 0
% 2.18/1.26  #BackRed      : 1
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.29
% 2.18/1.26  Parsing              : 0.16
% 2.18/1.26  CNF conversion       : 0.02
% 2.18/1.26  Main loop            : 0.20
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.07
% 2.18/1.26  Demodulation         : 0.06
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.02
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.53
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
