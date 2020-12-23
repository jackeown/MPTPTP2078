%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 127 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_30,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_18,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_18])).

tff(c_20,plain,(
    ! [A_15] : v4_relat_1(k6_relat_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_15] : v4_relat_1(k6_partfun1(A_15),A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_20])).

tff(c_113,plain,(
    ! [C_40,B_41,A_42] :
      ( v4_relat_1(C_40,B_41)
      | ~ v4_relat_1(C_40,A_42)
      | ~ v1_relat_1(C_40)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    ! [A_15,B_41] :
      ( v4_relat_1(k6_partfun1(A_15),B_41)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ r1_tarski(A_15,B_41) ) ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_119,plain,(
    ! [A_43,B_44] :
      ( v4_relat_1(k6_partfun1(A_43),B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_115])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [A_43,B_44] :
      ( k7_relat_1(k6_partfun1(A_43),B_44) = k6_partfun1(A_43)
      | ~ v1_relat_1(k6_partfun1(A_43))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_130,plain,(
    ! [A_43,B_44] :
      ( k7_relat_1(k6_partfun1(A_43),B_44) = k6_partfun1(A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_124])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_partfun1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_131,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_140,plain,(
    ! [A_45,A_12] :
      ( k1_relat_1(k5_relat_1(A_45,k6_partfun1(A_12))) = k10_relat_1(A_45,A_12)
      | ~ v1_relat_1(k6_partfun1(A_12))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_131])).

tff(c_163,plain,(
    ! [A_49,A_50] :
      ( k1_relat_1(k5_relat_1(A_49,k6_partfun1(A_50))) = k10_relat_1(A_49,A_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_140])).

tff(c_176,plain,(
    ! [A_50,A_13] :
      ( k1_relat_1(k7_relat_1(k6_partfun1(A_50),A_13)) = k10_relat_1(k6_partfun1(A_13),A_50)
      | ~ v1_relat_1(k6_partfun1(A_13))
      | ~ v1_relat_1(k6_partfun1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_163])).

tff(c_181,plain,(
    ! [A_51,A_52] : k1_relat_1(k7_relat_1(k6_partfun1(A_51),A_52)) = k10_relat_1(k6_partfun1(A_52),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_176])).

tff(c_193,plain,(
    ! [B_44,A_43] :
      ( k10_relat_1(k6_partfun1(B_44),A_43) = k1_relat_1(k6_partfun1(A_43))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_181])).

tff(c_199,plain,(
    ! [B_44,A_43] :
      ( k10_relat_1(k6_partfun1(B_44),A_43) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_193])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_252,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k8_relset_1(A_56,B_57,C_58,D_59) = k10_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_259,plain,(
    ! [A_20,D_59] : k8_relset_1(A_20,A_20,k6_partfun1(A_20),D_59) = k10_relat_1(k6_partfun1(A_20),D_59) ),
    inference(resolution,[status(thm)],[c_28,c_252])).

tff(c_32,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_260,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_32])).

tff(c_272,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_260])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.33  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.22/1.33  
% 2.22/1.33  %Foreground sorts:
% 2.22/1.33  
% 2.22/1.33  
% 2.22/1.33  %Background operators:
% 2.22/1.33  
% 2.22/1.33  
% 2.22/1.33  %Foreground operators:
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.22/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.33  
% 2.22/1.34  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.22/1.34  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.34  tff(f_75, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.22/1.34  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.22/1.34  tff(f_65, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.22/1.34  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.22/1.34  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.22/1.34  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.22/1.34  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.22/1.34  tff(f_73, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.22/1.34  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.22/1.34  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.34  tff(c_73, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.34  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.22/1.34  tff(c_30, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.34  tff(c_12, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.34  tff(c_40, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.22/1.34  tff(c_18, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.34  tff(c_37, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_18])).
% 2.22/1.34  tff(c_20, plain, (![A_15]: (v4_relat_1(k6_relat_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.34  tff(c_36, plain, (![A_15]: (v4_relat_1(k6_partfun1(A_15), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_20])).
% 2.22/1.34  tff(c_113, plain, (![C_40, B_41, A_42]: (v4_relat_1(C_40, B_41) | ~v4_relat_1(C_40, A_42) | ~v1_relat_1(C_40) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.34  tff(c_115, plain, (![A_15, B_41]: (v4_relat_1(k6_partfun1(A_15), B_41) | ~v1_relat_1(k6_partfun1(A_15)) | ~r1_tarski(A_15, B_41))), inference(resolution, [status(thm)], [c_36, c_113])).
% 2.22/1.34  tff(c_119, plain, (![A_43, B_44]: (v4_relat_1(k6_partfun1(A_43), B_44) | ~r1_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_115])).
% 2.22/1.34  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.34  tff(c_124, plain, (![A_43, B_44]: (k7_relat_1(k6_partfun1(A_43), B_44)=k6_partfun1(A_43) | ~v1_relat_1(k6_partfun1(A_43)) | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_119, c_8])).
% 2.22/1.34  tff(c_130, plain, (![A_43, B_44]: (k7_relat_1(k6_partfun1(A_43), B_44)=k6_partfun1(A_43) | ~r1_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_124])).
% 2.22/1.34  tff(c_16, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.34  tff(c_38, plain, (![A_13, B_14]: (k5_relat_1(k6_partfun1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.22/1.34  tff(c_131, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.34  tff(c_140, plain, (![A_45, A_12]: (k1_relat_1(k5_relat_1(A_45, k6_partfun1(A_12)))=k10_relat_1(A_45, A_12) | ~v1_relat_1(k6_partfun1(A_12)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_40, c_131])).
% 2.22/1.34  tff(c_163, plain, (![A_49, A_50]: (k1_relat_1(k5_relat_1(A_49, k6_partfun1(A_50)))=k10_relat_1(A_49, A_50) | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_140])).
% 2.22/1.34  tff(c_176, plain, (![A_50, A_13]: (k1_relat_1(k7_relat_1(k6_partfun1(A_50), A_13))=k10_relat_1(k6_partfun1(A_13), A_50) | ~v1_relat_1(k6_partfun1(A_13)) | ~v1_relat_1(k6_partfun1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_163])).
% 2.22/1.34  tff(c_181, plain, (![A_51, A_52]: (k1_relat_1(k7_relat_1(k6_partfun1(A_51), A_52))=k10_relat_1(k6_partfun1(A_52), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_176])).
% 2.22/1.34  tff(c_193, plain, (![B_44, A_43]: (k10_relat_1(k6_partfun1(B_44), A_43)=k1_relat_1(k6_partfun1(A_43)) | ~r1_tarski(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_130, c_181])).
% 2.22/1.34  tff(c_199, plain, (![B_44, A_43]: (k10_relat_1(k6_partfun1(B_44), A_43)=A_43 | ~r1_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_193])).
% 2.22/1.34  tff(c_28, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.34  tff(c_252, plain, (![A_56, B_57, C_58, D_59]: (k8_relset_1(A_56, B_57, C_58, D_59)=k10_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.22/1.34  tff(c_259, plain, (![A_20, D_59]: (k8_relset_1(A_20, A_20, k6_partfun1(A_20), D_59)=k10_relat_1(k6_partfun1(A_20), D_59))), inference(resolution, [status(thm)], [c_28, c_252])).
% 2.22/1.34  tff(c_32, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.34  tff(c_260, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_259, c_32])).
% 2.22/1.34  tff(c_272, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_199, c_260])).
% 2.22/1.34  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_272])).
% 2.22/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  Inference rules
% 2.22/1.34  ----------------------
% 2.22/1.34  #Ref     : 0
% 2.22/1.34  #Sup     : 48
% 2.22/1.34  #Fact    : 0
% 2.22/1.34  #Define  : 0
% 2.22/1.34  #Split   : 0
% 2.22/1.34  #Chain   : 0
% 2.22/1.34  #Close   : 0
% 2.22/1.34  
% 2.22/1.34  Ordering : KBO
% 2.22/1.34  
% 2.22/1.34  Simplification rules
% 2.22/1.34  ----------------------
% 2.22/1.34  #Subsume      : 0
% 2.22/1.34  #Demod        : 21
% 2.22/1.34  #Tautology    : 29
% 2.22/1.34  #SimpNegUnit  : 0
% 2.22/1.34  #BackRed      : 1
% 2.22/1.34  
% 2.22/1.34  #Partial instantiations: 0
% 2.22/1.34  #Strategies tried      : 1
% 2.22/1.34  
% 2.22/1.34  Timing (in seconds)
% 2.22/1.34  ----------------------
% 2.22/1.35  Preprocessing        : 0.31
% 2.22/1.35  Parsing              : 0.15
% 2.22/1.35  CNF conversion       : 0.02
% 2.22/1.35  Main loop            : 0.20
% 2.22/1.35  Inferencing          : 0.08
% 2.22/1.35  Reduction            : 0.07
% 2.22/1.35  Demodulation         : 0.05
% 2.22/1.35  BG Simplification    : 0.01
% 2.22/1.35  Subsumption          : 0.02
% 2.22/1.35  Abstraction          : 0.02
% 2.22/1.35  MUC search           : 0.00
% 2.22/1.35  Cooper               : 0.00
% 2.22/1.35  Total                : 0.56
% 2.22/1.35  Index Insertion      : 0.00
% 2.22/1.35  Index Deletion       : 0.00
% 2.22/1.35  Index Matching       : 0.00
% 2.22/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
