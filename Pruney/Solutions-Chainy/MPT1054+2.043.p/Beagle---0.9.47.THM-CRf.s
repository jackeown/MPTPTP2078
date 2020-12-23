%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   64 (  99 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 129 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_28,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_39,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_18,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18])).

tff(c_20,plain,(
    ! [A_15] : v4_relat_1(k6_relat_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35,plain,(
    ! [A_15] : v4_relat_1(k6_partfun1(A_15),A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20])).

tff(c_111,plain,(
    ! [C_39,B_40,A_41] :
      ( v4_relat_1(C_39,B_40)
      | ~ v4_relat_1(C_39,A_41)
      | ~ v1_relat_1(C_39)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_15,B_40] :
      ( v4_relat_1(k6_partfun1(A_15),B_40)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ r1_tarski(A_15,B_40) ) ),
    inference(resolution,[status(thm)],[c_35,c_111])).

tff(c_117,plain,(
    ! [A_42,B_43] :
      ( v4_relat_1(k6_partfun1(A_42),B_43)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_122,plain,(
    ! [A_42,B_43] :
      ( k7_relat_1(k6_partfun1(A_42),B_43) = k6_partfun1(A_42)
      | ~ v1_relat_1(k6_partfun1(A_42))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_117,c_8])).

tff(c_128,plain,(
    ! [A_42,B_43] :
      ( k7_relat_1(k6_partfun1(A_42),B_43) = k6_partfun1(A_42)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_partfun1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_147,plain,(
    ! [A_46,B_47] :
      ( k10_relat_1(A_46,k1_relat_1(B_47)) = k1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_156,plain,(
    ! [A_46,A_12] :
      ( k1_relat_1(k5_relat_1(A_46,k6_partfun1(A_12))) = k10_relat_1(A_46,A_12)
      | ~ v1_relat_1(k6_partfun1(A_12))
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_147])).

tff(c_161,plain,(
    ! [A_48,A_49] :
      ( k1_relat_1(k5_relat_1(A_48,k6_partfun1(A_49))) = k10_relat_1(A_48,A_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_174,plain,(
    ! [A_49,A_13] :
      ( k1_relat_1(k7_relat_1(k6_partfun1(A_49),A_13)) = k10_relat_1(k6_partfun1(A_13),A_49)
      | ~ v1_relat_1(k6_partfun1(A_13))
      | ~ v1_relat_1(k6_partfun1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_161])).

tff(c_179,plain,(
    ! [A_50,A_51] : k1_relat_1(k7_relat_1(k6_partfun1(A_50),A_51)) = k10_relat_1(k6_partfun1(A_51),A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_174])).

tff(c_191,plain,(
    ! [B_43,A_42] :
      ( k10_relat_1(k6_partfun1(B_43),A_42) = k1_relat_1(k6_partfun1(A_42))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_179])).

tff(c_197,plain,(
    ! [B_43,A_42] :
      ( k10_relat_1(k6_partfun1(B_43),A_42) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_191])).

tff(c_26,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_33,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_257,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k8_relset_1(A_58,B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_263,plain,(
    ! [A_20,D_61] : k8_relset_1(A_20,A_20,k6_partfun1(A_20),D_61) = k10_relat_1(k6_partfun1(A_20),D_61) ),
    inference(resolution,[status(thm)],[c_33,c_257])).

tff(c_30,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_361,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_30])).

tff(c_376,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_361])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.12/1.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.27  
% 2.12/1.29  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.12/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.12/1.29  tff(f_73, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.12/1.29  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.12/1.29  tff(f_65, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.12/1.29  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 2.12/1.29  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.12/1.29  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.12/1.29  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.12/1.29  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.12/1.29  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.12/1.29  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.29  tff(c_70, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.29  tff(c_74, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_70])).
% 2.12/1.29  tff(c_28, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.29  tff(c_12, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.29  tff(c_39, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.12/1.29  tff(c_18, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.29  tff(c_36, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18])).
% 2.12/1.29  tff(c_20, plain, (![A_15]: (v4_relat_1(k6_relat_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.29  tff(c_35, plain, (![A_15]: (v4_relat_1(k6_partfun1(A_15), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20])).
% 2.12/1.29  tff(c_111, plain, (![C_39, B_40, A_41]: (v4_relat_1(C_39, B_40) | ~v4_relat_1(C_39, A_41) | ~v1_relat_1(C_39) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.29  tff(c_113, plain, (![A_15, B_40]: (v4_relat_1(k6_partfun1(A_15), B_40) | ~v1_relat_1(k6_partfun1(A_15)) | ~r1_tarski(A_15, B_40))), inference(resolution, [status(thm)], [c_35, c_111])).
% 2.12/1.29  tff(c_117, plain, (![A_42, B_43]: (v4_relat_1(k6_partfun1(A_42), B_43) | ~r1_tarski(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 2.12/1.29  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.29  tff(c_122, plain, (![A_42, B_43]: (k7_relat_1(k6_partfun1(A_42), B_43)=k6_partfun1(A_42) | ~v1_relat_1(k6_partfun1(A_42)) | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_117, c_8])).
% 2.12/1.29  tff(c_128, plain, (![A_42, B_43]: (k7_relat_1(k6_partfun1(A_42), B_43)=k6_partfun1(A_42) | ~r1_tarski(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_122])).
% 2.12/1.29  tff(c_16, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.29  tff(c_37, plain, (![A_13, B_14]: (k5_relat_1(k6_partfun1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16])).
% 2.12/1.29  tff(c_147, plain, (![A_46, B_47]: (k10_relat_1(A_46, k1_relat_1(B_47))=k1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.29  tff(c_156, plain, (![A_46, A_12]: (k1_relat_1(k5_relat_1(A_46, k6_partfun1(A_12)))=k10_relat_1(A_46, A_12) | ~v1_relat_1(k6_partfun1(A_12)) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_39, c_147])).
% 2.12/1.29  tff(c_161, plain, (![A_48, A_49]: (k1_relat_1(k5_relat_1(A_48, k6_partfun1(A_49)))=k10_relat_1(A_48, A_49) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_156])).
% 2.12/1.29  tff(c_174, plain, (![A_49, A_13]: (k1_relat_1(k7_relat_1(k6_partfun1(A_49), A_13))=k10_relat_1(k6_partfun1(A_13), A_49) | ~v1_relat_1(k6_partfun1(A_13)) | ~v1_relat_1(k6_partfun1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_161])).
% 2.12/1.29  tff(c_179, plain, (![A_50, A_51]: (k1_relat_1(k7_relat_1(k6_partfun1(A_50), A_51))=k10_relat_1(k6_partfun1(A_51), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_174])).
% 2.12/1.29  tff(c_191, plain, (![B_43, A_42]: (k10_relat_1(k6_partfun1(B_43), A_42)=k1_relat_1(k6_partfun1(A_42)) | ~r1_tarski(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_128, c_179])).
% 2.12/1.29  tff(c_197, plain, (![B_43, A_42]: (k10_relat_1(k6_partfun1(B_43), A_42)=A_42 | ~r1_tarski(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_191])).
% 2.12/1.29  tff(c_26, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.29  tff(c_33, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.12/1.29  tff(c_257, plain, (![A_58, B_59, C_60, D_61]: (k8_relset_1(A_58, B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.29  tff(c_263, plain, (![A_20, D_61]: (k8_relset_1(A_20, A_20, k6_partfun1(A_20), D_61)=k10_relat_1(k6_partfun1(A_20), D_61))), inference(resolution, [status(thm)], [c_33, c_257])).
% 2.12/1.29  tff(c_30, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.29  tff(c_361, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_30])).
% 2.12/1.29  tff(c_376, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_197, c_361])).
% 2.12/1.29  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_376])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 70
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 0
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 0
% 2.12/1.29  #Demod        : 29
% 2.12/1.29  #Tautology    : 41
% 2.12/1.29  #SimpNegUnit  : 0
% 2.12/1.29  #BackRed      : 1
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.29  Preprocessing        : 0.30
% 2.12/1.29  Parsing              : 0.16
% 2.12/1.29  CNF conversion       : 0.02
% 2.12/1.29  Main loop            : 0.20
% 2.12/1.29  Inferencing          : 0.08
% 2.12/1.29  Reduction            : 0.06
% 2.12/1.29  Demodulation         : 0.05
% 2.12/1.29  BG Simplification    : 0.01
% 2.12/1.29  Subsumption          : 0.03
% 2.12/1.29  Abstraction          : 0.02
% 2.12/1.29  MUC search           : 0.00
% 2.12/1.29  Cooper               : 0.00
% 2.12/1.29  Total                : 0.53
% 2.12/1.29  Index Insertion      : 0.00
% 2.12/1.29  Index Deletion       : 0.00
% 2.12/1.29  Index Matching       : 0.00
% 2.12/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
