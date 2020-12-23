%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [A_38,A_3] :
      ( r1_tarski(A_38,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_95,plain,(
    ! [A_40,A_41] :
      ( r1_tarski(A_40,A_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(A_41)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_91])).

tff(c_103,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_38,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_30,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_partfun1(B_17),k6_partfun1(A_16)) = k6_partfun1(k3_xboole_0(A_16,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_30])).

tff(c_126,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_135,plain,(
    ! [A_45,A_14] :
      ( k1_relat_1(k5_relat_1(A_45,k6_partfun1(A_14))) = k10_relat_1(A_45,A_14)
      | ~ v1_relat_1(k6_partfun1(A_14))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_126])).

tff(c_149,plain,(
    ! [A_48,A_49] :
      ( k1_relat_1(k5_relat_1(A_48,k6_partfun1(A_49))) = k10_relat_1(A_48,A_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_135])).

tff(c_161,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_16,B_17))) = k10_relat_1(k6_partfun1(B_17),A_16)
      | ~ v1_relat_1(k6_partfun1(B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_149])).

tff(c_165,plain,(
    ! [B_17,A_16] : k10_relat_1(k6_partfun1(B_17),A_16) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_47,c_161])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_242,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k8_relset_1(A_62,B_63,C_64,D_65) = k10_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,(
    ! [A_22,D_65] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_65) = k10_relat_1(k6_partfun1(A_22),D_65) ),
    inference(resolution,[status(thm)],[c_36,c_242])).

tff(c_246,plain,(
    ! [A_22,D_65] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_65) = k3_xboole_0(D_65,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_244])).

tff(c_40,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_247,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_40])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.33  
% 2.06/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  %$ v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.27/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.27/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.27/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  
% 2.27/1.35  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.27/1.35  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.27/1.35  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.27/1.35  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.27/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.27/1.35  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.27/1.35  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.27/1.35  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.27/1.35  tff(f_62, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.27/1.35  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.27/1.35  tff(f_70, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.27/1.35  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.27/1.35  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.35  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.35  tff(c_87, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | v1_xboole_0(B_39) | ~m1_subset_1(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.35  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.35  tff(c_91, plain, (![A_38, A_3]: (r1_tarski(A_38, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_38, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_87, c_4])).
% 2.27/1.35  tff(c_95, plain, (![A_40, A_41]: (r1_tarski(A_40, A_41) | ~m1_subset_1(A_40, k1_zfmisc_1(A_41)))), inference(negUnitSimplification, [status(thm)], [c_16, c_91])).
% 2.27/1.35  tff(c_103, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_95])).
% 2.27/1.35  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.35  tff(c_116, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_103, c_2])).
% 2.27/1.35  tff(c_38, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.35  tff(c_26, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.35  tff(c_45, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26])).
% 2.27/1.35  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.35  tff(c_47, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 2.27/1.35  tff(c_30, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.27/1.35  tff(c_43, plain, (![B_17, A_16]: (k5_relat_1(k6_partfun1(B_17), k6_partfun1(A_16))=k6_partfun1(k3_xboole_0(A_16, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_30])).
% 2.27/1.35  tff(c_126, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.35  tff(c_135, plain, (![A_45, A_14]: (k1_relat_1(k5_relat_1(A_45, k6_partfun1(A_14)))=k10_relat_1(A_45, A_14) | ~v1_relat_1(k6_partfun1(A_14)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_47, c_126])).
% 2.27/1.35  tff(c_149, plain, (![A_48, A_49]: (k1_relat_1(k5_relat_1(A_48, k6_partfun1(A_49)))=k10_relat_1(A_48, A_49) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_135])).
% 2.27/1.35  tff(c_161, plain, (![A_16, B_17]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_16, B_17)))=k10_relat_1(k6_partfun1(B_17), A_16) | ~v1_relat_1(k6_partfun1(B_17)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_149])).
% 2.27/1.35  tff(c_165, plain, (![B_17, A_16]: (k10_relat_1(k6_partfun1(B_17), A_16)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_47, c_161])).
% 2.27/1.35  tff(c_36, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.35  tff(c_242, plain, (![A_62, B_63, C_64, D_65]: (k8_relset_1(A_62, B_63, C_64, D_65)=k10_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.27/1.35  tff(c_244, plain, (![A_22, D_65]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_65)=k10_relat_1(k6_partfun1(A_22), D_65))), inference(resolution, [status(thm)], [c_36, c_242])).
% 2.27/1.35  tff(c_246, plain, (![A_22, D_65]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_65)=k3_xboole_0(D_65, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_244])).
% 2.27/1.35  tff(c_40, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.35  tff(c_247, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_40])).
% 2.27/1.35  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_247])).
% 2.27/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  Inference rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Ref     : 0
% 2.27/1.35  #Sup     : 41
% 2.27/1.35  #Fact    : 0
% 2.27/1.35  #Define  : 0
% 2.27/1.35  #Split   : 0
% 2.27/1.35  #Chain   : 0
% 2.27/1.35  #Close   : 0
% 2.27/1.35  
% 2.27/1.35  Ordering : KBO
% 2.27/1.35  
% 2.27/1.35  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 1
% 2.27/1.35  #Demod        : 26
% 2.27/1.35  #Tautology    : 24
% 2.27/1.35  #SimpNegUnit  : 1
% 2.27/1.35  #BackRed      : 1
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.35  Preprocessing        : 0.36
% 2.27/1.35  Parsing              : 0.19
% 2.27/1.35  CNF conversion       : 0.02
% 2.27/1.35  Main loop            : 0.17
% 2.27/1.35  Inferencing          : 0.07
% 2.27/1.35  Reduction            : 0.06
% 2.27/1.35  Demodulation         : 0.04
% 2.27/1.35  BG Simplification    : 0.02
% 2.27/1.35  Subsumption          : 0.02
% 2.27/1.35  Abstraction          : 0.01
% 2.27/1.35  MUC search           : 0.00
% 2.27/1.35  Cooper               : 0.00
% 2.27/1.35  Total                : 0.57
% 2.27/1.35  Index Insertion      : 0.00
% 2.27/1.35  Index Deletion       : 0.00
% 2.27/1.35  Index Matching       : 0.00
% 2.27/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
