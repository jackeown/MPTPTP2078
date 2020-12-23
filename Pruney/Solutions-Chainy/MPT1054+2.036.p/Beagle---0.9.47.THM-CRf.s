%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:16 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 141 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 176 expanded)
%              Number of equality atoms :   36 (  96 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(f_64,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_30,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_24,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_partfun1(B_17),k6_partfun1(A_16)) = k6_partfun1(k3_xboole_0(A_16,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_24])).

tff(c_157,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_166,plain,(
    ! [A_45,A_10] :
      ( k1_relat_1(k5_relat_1(A_45,k6_partfun1(A_10))) = k10_relat_1(A_45,A_10)
      | ~ v1_relat_1(k6_partfun1(A_10))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_157])).

tff(c_180,plain,(
    ! [A_49,A_50] :
      ( k1_relat_1(k5_relat_1(A_49,k6_partfun1(A_50))) = k10_relat_1(A_49,A_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_166])).

tff(c_192,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_16,B_17))) = k10_relat_1(k6_partfun1(B_17),A_16)
      | ~ v1_relat_1(k6_partfun1(B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_180])).

tff(c_196,plain,(
    ! [B_17,A_16] : k10_relat_1(k6_partfun1(B_17),A_16) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_41,c_192])).

tff(c_28,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_264,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k8_relset_1(A_57,B_58,C_59,D_60) = k10_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_266,plain,(
    ! [A_22,D_60] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_60) = k10_relat_1(k6_partfun1(A_22),D_60) ),
    inference(resolution,[status(thm)],[c_35,c_264])).

tff(c_271,plain,(
    ! [A_22,D_60] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_60) = k3_xboole_0(D_60,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_266])).

tff(c_32,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_273,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_73,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k9_relat_1(k6_relat_1(A_14),B_15) = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    ! [A_38,B_39] :
      ( k9_relat_1(k6_partfun1(A_38),B_39) = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22])).

tff(c_100,plain,(
    ! [B_5,A_4] :
      ( k9_relat_1(k6_partfun1(B_5),A_4) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_18,plain,(
    ! [A_11] : v1_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_11] : v1_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_18])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_171,plain,(
    ! [B_47,A_48] :
      ( k9_relat_1(B_47,k10_relat_1(B_47,A_48)) = A_48
      | ~ r1_tarski(A_48,k2_relat_1(B_47))
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,(
    ! [A_10,A_48] :
      ( k9_relat_1(k6_partfun1(A_10),k10_relat_1(k6_partfun1(A_10),A_48)) = A_48
      | ~ r1_tarski(A_48,A_10)
      | ~ v1_funct_1(k6_partfun1(A_10))
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_171])).

tff(c_179,plain,(
    ! [A_10,A_48] :
      ( k9_relat_1(k6_partfun1(A_10),k10_relat_1(k6_partfun1(A_10),A_48)) = A_48
      | ~ r1_tarski(A_48,A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_38,c_176])).

tff(c_219,plain,(
    ! [A_53,A_54] :
      ( k9_relat_1(k6_partfun1(A_53),k3_xboole_0(A_54,A_53)) = A_54
      | ~ r1_tarski(A_54,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_179])).

tff(c_283,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64)
      | ~ r1_tarski(k3_xboole_0(A_63,B_64),B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_219])).

tff(c_289,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_283])).

tff(c_298,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_289])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.05/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.05/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.30  
% 2.28/1.32  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.28/1.32  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.28/1.32  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.28/1.32  tff(f_64, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.28/1.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.28/1.32  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.28/1.32  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.28/1.32  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.28/1.32  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.28/1.32  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.28/1.32  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.28/1.32  tff(c_30, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.28/1.32  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.32  tff(c_39, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.28/1.32  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.32  tff(c_41, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.28/1.32  tff(c_24, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.32  tff(c_36, plain, (![B_17, A_16]: (k5_relat_1(k6_partfun1(B_17), k6_partfun1(A_16))=k6_partfun1(k3_xboole_0(A_16, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_24])).
% 2.28/1.32  tff(c_157, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.32  tff(c_166, plain, (![A_45, A_10]: (k1_relat_1(k5_relat_1(A_45, k6_partfun1(A_10)))=k10_relat_1(A_45, A_10) | ~v1_relat_1(k6_partfun1(A_10)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_41, c_157])).
% 2.28/1.32  tff(c_180, plain, (![A_49, A_50]: (k1_relat_1(k5_relat_1(A_49, k6_partfun1(A_50)))=k10_relat_1(A_49, A_50) | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_166])).
% 2.28/1.32  tff(c_192, plain, (![A_16, B_17]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_16, B_17)))=k10_relat_1(k6_partfun1(B_17), A_16) | ~v1_relat_1(k6_partfun1(B_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_180])).
% 2.28/1.32  tff(c_196, plain, (![B_17, A_16]: (k10_relat_1(k6_partfun1(B_17), A_16)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_41, c_192])).
% 2.28/1.32  tff(c_28, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.32  tff(c_35, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 2.28/1.32  tff(c_264, plain, (![A_57, B_58, C_59, D_60]: (k8_relset_1(A_57, B_58, C_59, D_60)=k10_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.28/1.32  tff(c_266, plain, (![A_22, D_60]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_60)=k10_relat_1(k6_partfun1(A_22), D_60))), inference(resolution, [status(thm)], [c_35, c_264])).
% 2.28/1.32  tff(c_271, plain, (![A_22, D_60]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_60)=k3_xboole_0(D_60, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_266])).
% 2.28/1.32  tff(c_32, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.28/1.32  tff(c_273, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_32])).
% 2.28/1.32  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.28/1.32  tff(c_73, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.32  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.28/1.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.32  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.32  tff(c_22, plain, (![A_14, B_15]: (k9_relat_1(k6_relat_1(A_14), B_15)=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.32  tff(c_89, plain, (![A_38, B_39]: (k9_relat_1(k6_partfun1(A_38), B_39)=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22])).
% 2.28/1.32  tff(c_100, plain, (![B_5, A_4]: (k9_relat_1(k6_partfun1(B_5), A_4)=A_4 | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_89])).
% 2.28/1.32  tff(c_18, plain, (![A_11]: (v1_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.32  tff(c_38, plain, (![A_11]: (v1_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_18])).
% 2.28/1.32  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.32  tff(c_40, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.28/1.32  tff(c_171, plain, (![B_47, A_48]: (k9_relat_1(B_47, k10_relat_1(B_47, A_48))=A_48 | ~r1_tarski(A_48, k2_relat_1(B_47)) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.32  tff(c_176, plain, (![A_10, A_48]: (k9_relat_1(k6_partfun1(A_10), k10_relat_1(k6_partfun1(A_10), A_48))=A_48 | ~r1_tarski(A_48, A_10) | ~v1_funct_1(k6_partfun1(A_10)) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_171])).
% 2.28/1.32  tff(c_179, plain, (![A_10, A_48]: (k9_relat_1(k6_partfun1(A_10), k10_relat_1(k6_partfun1(A_10), A_48))=A_48 | ~r1_tarski(A_48, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_38, c_176])).
% 2.28/1.32  tff(c_219, plain, (![A_53, A_54]: (k9_relat_1(k6_partfun1(A_53), k3_xboole_0(A_54, A_53))=A_54 | ~r1_tarski(A_54, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_179])).
% 2.28/1.32  tff(c_283, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64) | ~r1_tarski(k3_xboole_0(A_63, B_64), B_64))), inference(superposition, [status(thm), theory('equality')], [c_100, c_219])).
% 2.28/1.32  tff(c_289, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_2, c_283])).
% 2.28/1.32  tff(c_298, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_81, c_289])).
% 2.28/1.32  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_298])).
% 2.28/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  Inference rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Ref     : 0
% 2.28/1.32  #Sup     : 55
% 2.28/1.32  #Fact    : 0
% 2.28/1.32  #Define  : 0
% 2.28/1.32  #Split   : 0
% 2.28/1.32  #Chain   : 0
% 2.28/1.32  #Close   : 0
% 2.28/1.32  
% 2.28/1.32  Ordering : KBO
% 2.28/1.32  
% 2.28/1.32  Simplification rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Subsume      : 2
% 2.28/1.32  #Demod        : 36
% 2.28/1.32  #Tautology    : 35
% 2.28/1.32  #SimpNegUnit  : 1
% 2.28/1.32  #BackRed      : 1
% 2.28/1.32  
% 2.28/1.32  #Partial instantiations: 0
% 2.28/1.32  #Strategies tried      : 1
% 2.28/1.32  
% 2.28/1.32  Timing (in seconds)
% 2.28/1.32  ----------------------
% 2.28/1.32  Preprocessing        : 0.32
% 2.28/1.32  Parsing              : 0.18
% 2.28/1.32  CNF conversion       : 0.02
% 2.28/1.32  Main loop            : 0.18
% 2.28/1.32  Inferencing          : 0.07
% 2.28/1.32  Reduction            : 0.06
% 2.28/1.32  Demodulation         : 0.04
% 2.28/1.32  BG Simplification    : 0.01
% 2.28/1.32  Subsumption          : 0.02
% 2.28/1.32  Abstraction          : 0.01
% 2.28/1.33  MUC search           : 0.00
% 2.28/1.33  Cooper               : 0.00
% 2.28/1.33  Total                : 0.53
% 2.28/1.33  Index Insertion      : 0.00
% 2.28/1.33  Index Deletion       : 0.00
% 2.28/1.33  Index Matching       : 0.00
% 2.28/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
