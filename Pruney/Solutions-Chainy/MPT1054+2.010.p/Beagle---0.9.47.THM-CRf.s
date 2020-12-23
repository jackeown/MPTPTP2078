%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 110 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 122 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_26,plain,(
    ! [A_19] : k6_relat_1(A_19) = k6_partfun1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_9] : k1_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_18,plain,(
    ! [B_13,A_12] : k5_relat_1(k6_relat_1(B_13),k6_relat_1(A_12)) = k6_relat_1(k3_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_31,plain,(
    ! [B_13,A_12] : k5_relat_1(k6_partfun1(B_13),k6_partfun1(A_12)) = k6_partfun1(k3_xboole_0(A_12,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_26,c_18])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ! [A_9] : k2_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [B_35,A_36] :
      ( k5_relat_1(B_35,k6_partfun1(A_36)) = B_35
      | ~ r1_tarski(k2_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_126,plain,(
    ! [A_9,A_36] :
      ( k5_relat_1(k6_partfun1(A_9),k6_partfun1(A_36)) = k6_partfun1(A_9)
      | ~ r1_tarski(A_9,A_36)
      | ~ v1_relat_1(k6_partfun1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_123])).

tff(c_143,plain,(
    ! [A_39,A_40] :
      ( k6_partfun1(k3_xboole_0(A_39,A_40)) = k6_partfun1(A_40)
      | ~ r1_tarski(A_40,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_31,c_126])).

tff(c_161,plain,(
    ! [A_39,A_40] :
      ( k3_xboole_0(A_39,A_40) = k1_relat_1(k6_partfun1(A_40))
      | ~ r1_tarski(A_40,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_34])).

tff(c_186,plain,(
    ! [A_41,A_42] :
      ( k3_xboole_0(A_41,A_42) = A_42
      | ~ r1_tarski(A_42,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_161])).

tff(c_194,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_112,c_186])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_129,plain,(
    ! [A_37,B_38] :
      ( k10_relat_1(A_37,k1_relat_1(B_38)) = k1_relat_1(k5_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_138,plain,(
    ! [A_37,A_9] :
      ( k1_relat_1(k5_relat_1(A_37,k6_partfun1(A_9))) = k10_relat_1(A_37,A_9)
      | ~ v1_relat_1(k6_partfun1(A_9))
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_129])).

tff(c_386,plain,(
    ! [A_55,A_56] :
      ( k1_relat_1(k5_relat_1(A_55,k6_partfun1(A_56))) = k10_relat_1(A_55,A_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_138])).

tff(c_404,plain,(
    ! [A_12,B_13] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_12,B_13))) = k10_relat_1(k6_partfun1(B_13),A_12)
      | ~ v1_relat_1(k6_partfun1(B_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_386])).

tff(c_408,plain,(
    ! [B_13,A_12] : k10_relat_1(k6_partfun1(B_13),A_12) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_34,c_404])).

tff(c_24,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_205,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k8_relset_1(A_43,B_44,C_45,D_46) = k10_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    ! [A_18,D_46] : k8_relset_1(A_18,A_18,k6_partfun1(A_18),D_46) = k10_relat_1(k6_partfun1(A_18),D_46) ),
    inference(resolution,[status(thm)],[c_24,c_205])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_261,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_28])).

tff(c_409,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_261])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_2,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.44  
% 2.21/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.45  %$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.21/1.45  
% 2.21/1.45  %Foreground sorts:
% 2.21/1.45  
% 2.21/1.45  
% 2.21/1.45  %Background operators:
% 2.21/1.45  
% 2.21/1.45  
% 2.21/1.45  %Foreground operators:
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.21/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.21/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.45  
% 2.21/1.46  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.21/1.46  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.46  tff(f_62, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.21/1.46  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.21/1.46  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.21/1.46  tff(f_52, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.21/1.46  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.21/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.21/1.46  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.21/1.46  tff(f_60, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.21/1.46  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.21/1.46  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.46  tff(c_100, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.46  tff(c_112, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.21/1.46  tff(c_26, plain, (![A_19]: (k6_relat_1(A_19)=k6_partfun1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.21/1.46  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.46  tff(c_34, plain, (![A_9]: (k1_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 2.21/1.46  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.46  tff(c_35, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.21/1.46  tff(c_18, plain, (![B_13, A_12]: (k5_relat_1(k6_relat_1(B_13), k6_relat_1(A_12))=k6_relat_1(k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.46  tff(c_31, plain, (![B_13, A_12]: (k5_relat_1(k6_partfun1(B_13), k6_partfun1(A_12))=k6_partfun1(k3_xboole_0(A_12, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_26, c_18])).
% 2.21/1.46  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.46  tff(c_33, plain, (![A_9]: (k2_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 2.21/1.46  tff(c_16, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.46  tff(c_123, plain, (![B_35, A_36]: (k5_relat_1(B_35, k6_partfun1(A_36))=B_35 | ~r1_tarski(k2_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 2.21/1.46  tff(c_126, plain, (![A_9, A_36]: (k5_relat_1(k6_partfun1(A_9), k6_partfun1(A_36))=k6_partfun1(A_9) | ~r1_tarski(A_9, A_36) | ~v1_relat_1(k6_partfun1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_123])).
% 2.21/1.46  tff(c_143, plain, (![A_39, A_40]: (k6_partfun1(k3_xboole_0(A_39, A_40))=k6_partfun1(A_40) | ~r1_tarski(A_40, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_31, c_126])).
% 2.21/1.46  tff(c_161, plain, (![A_39, A_40]: (k3_xboole_0(A_39, A_40)=k1_relat_1(k6_partfun1(A_40)) | ~r1_tarski(A_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_143, c_34])).
% 2.21/1.46  tff(c_186, plain, (![A_41, A_42]: (k3_xboole_0(A_41, A_42)=A_42 | ~r1_tarski(A_42, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_161])).
% 2.21/1.46  tff(c_194, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_112, c_186])).
% 2.21/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.46  tff(c_129, plain, (![A_37, B_38]: (k10_relat_1(A_37, k1_relat_1(B_38))=k1_relat_1(k5_relat_1(A_37, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.46  tff(c_138, plain, (![A_37, A_9]: (k1_relat_1(k5_relat_1(A_37, k6_partfun1(A_9)))=k10_relat_1(A_37, A_9) | ~v1_relat_1(k6_partfun1(A_9)) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_34, c_129])).
% 2.21/1.46  tff(c_386, plain, (![A_55, A_56]: (k1_relat_1(k5_relat_1(A_55, k6_partfun1(A_56)))=k10_relat_1(A_55, A_56) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_138])).
% 2.21/1.46  tff(c_404, plain, (![A_12, B_13]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_12, B_13)))=k10_relat_1(k6_partfun1(B_13), A_12) | ~v1_relat_1(k6_partfun1(B_13)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_386])).
% 2.21/1.46  tff(c_408, plain, (![B_13, A_12]: (k10_relat_1(k6_partfun1(B_13), A_12)=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_34, c_404])).
% 2.21/1.46  tff(c_24, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.46  tff(c_205, plain, (![A_43, B_44, C_45, D_46]: (k8_relset_1(A_43, B_44, C_45, D_46)=k10_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.46  tff(c_212, plain, (![A_18, D_46]: (k8_relset_1(A_18, A_18, k6_partfun1(A_18), D_46)=k10_relat_1(k6_partfun1(A_18), D_46))), inference(resolution, [status(thm)], [c_24, c_205])).
% 2.21/1.46  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.46  tff(c_261, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_28])).
% 2.21/1.46  tff(c_409, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_261])).
% 2.21/1.46  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_2, c_409])).
% 2.21/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.46  
% 2.21/1.46  Inference rules
% 2.21/1.46  ----------------------
% 2.21/1.46  #Ref     : 0
% 2.21/1.46  #Sup     : 93
% 2.21/1.46  #Fact    : 0
% 2.21/1.46  #Define  : 0
% 2.21/1.46  #Split   : 1
% 2.21/1.46  #Chain   : 0
% 2.21/1.46  #Close   : 0
% 2.21/1.46  
% 2.21/1.46  Ordering : KBO
% 2.21/1.46  
% 2.21/1.46  Simplification rules
% 2.21/1.46  ----------------------
% 2.21/1.46  #Subsume      : 6
% 2.21/1.46  #Demod        : 41
% 2.21/1.46  #Tautology    : 49
% 2.21/1.46  #SimpNegUnit  : 0
% 2.21/1.46  #BackRed      : 3
% 2.21/1.46  
% 2.21/1.46  #Partial instantiations: 0
% 2.21/1.46  #Strategies tried      : 1
% 2.21/1.46  
% 2.21/1.46  Timing (in seconds)
% 2.21/1.46  ----------------------
% 2.47/1.46  Preprocessing        : 0.36
% 2.47/1.46  Parsing              : 0.21
% 2.47/1.46  CNF conversion       : 0.02
% 2.47/1.46  Main loop            : 0.22
% 2.47/1.46  Inferencing          : 0.08
% 2.47/1.46  Reduction            : 0.08
% 2.47/1.46  Demodulation         : 0.06
% 2.47/1.46  BG Simplification    : 0.01
% 2.47/1.46  Subsumption          : 0.04
% 2.47/1.46  Abstraction          : 0.02
% 2.47/1.46  MUC search           : 0.00
% 2.47/1.46  Cooper               : 0.00
% 2.47/1.46  Total                : 0.62
% 2.47/1.46  Index Insertion      : 0.00
% 2.47/1.46  Index Deletion       : 0.00
% 2.47/1.47  Index Matching       : 0.00
% 2.47/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
