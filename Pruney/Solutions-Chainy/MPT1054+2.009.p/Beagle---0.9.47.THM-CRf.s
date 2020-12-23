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
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  86 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_56,axiom,(
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

tff(c_18,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [A_41,A_5] :
      ( r1_tarski(A_41,A_5)
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ m1_subset_1(A_41,k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_126,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(A_43,A_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_44)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_122])).

tff(c_134,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_38,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_26,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ! [A_17] : k1_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26])).

tff(c_30,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_partfun1(B_19),k6_partfun1(A_18)) = k6_partfun1(k3_xboole_0(A_18,B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_30])).

tff(c_157,plain,(
    ! [A_48,B_49] :
      ( k10_relat_1(A_48,k1_relat_1(B_49)) = k1_relat_1(k5_relat_1(A_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [A_48,A_17] :
      ( k1_relat_1(k5_relat_1(A_48,k6_partfun1(A_17))) = k10_relat_1(A_48,A_17)
      | ~ v1_relat_1(k6_partfun1(A_17))
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_157])).

tff(c_180,plain,(
    ! [A_51,A_52] :
      ( k1_relat_1(k5_relat_1(A_51,k6_partfun1(A_52))) = k10_relat_1(A_51,A_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_166])).

tff(c_192,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_18,B_19))) = k10_relat_1(k6_partfun1(B_19),A_18)
      | ~ v1_relat_1(k6_partfun1(B_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_180])).

tff(c_196,plain,(
    ! [B_19,A_18] : k10_relat_1(k6_partfun1(B_19),A_18) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_45,c_192])).

tff(c_36,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_274,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k8_relset_1(A_65,B_66,C_67,D_68) = k10_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_276,plain,(
    ! [A_24,D_68] : k8_relset_1(A_24,A_24,k6_partfun1(A_24),D_68) = k10_relat_1(k6_partfun1(A_24),D_68) ),
    inference(resolution,[status(thm)],[c_36,c_274])).

tff(c_278,plain,(
    ! [A_24,D_68] : k8_relset_1(A_24,A_24,k6_partfun1(A_24),D_68) = k3_xboole_0(D_68,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_276])).

tff(c_40,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_279,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_40])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:56:51 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.21  
% 2.14/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.21  %$ v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.14/1.21  
% 2.14/1.21  %Foreground sorts:
% 2.14/1.21  
% 2.14/1.21  
% 2.14/1.21  %Background operators:
% 2.14/1.21  
% 2.14/1.21  
% 2.14/1.21  %Foreground operators:
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.14/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.14/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.14/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.21  
% 2.14/1.23  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.14/1.23  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.14/1.23  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.23  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.23  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.14/1.23  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.14/1.23  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.14/1.23  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.14/1.23  tff(f_62, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.14/1.23  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.14/1.23  tff(f_70, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.14/1.23  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.14/1.23  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.23  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.23  tff(c_118, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.23  tff(c_6, plain, (![C_9, A_5]: (r1_tarski(C_9, A_5) | ~r2_hidden(C_9, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.23  tff(c_122, plain, (![A_41, A_5]: (r1_tarski(A_41, A_5) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~m1_subset_1(A_41, k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_118, c_6])).
% 2.14/1.23  tff(c_126, plain, (![A_43, A_44]: (r1_tarski(A_43, A_44) | ~m1_subset_1(A_43, k1_zfmisc_1(A_44)))), inference(negUnitSimplification, [status(thm)], [c_18, c_122])).
% 2.14/1.23  tff(c_134, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_126])).
% 2.14/1.23  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.23  tff(c_147, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.14/1.23  tff(c_38, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.23  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.23  tff(c_46, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 2.14/1.23  tff(c_26, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.23  tff(c_45, plain, (![A_17]: (k1_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26])).
% 2.14/1.23  tff(c_30, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.23  tff(c_43, plain, (![B_19, A_18]: (k5_relat_1(k6_partfun1(B_19), k6_partfun1(A_18))=k6_partfun1(k3_xboole_0(A_18, B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_30])).
% 2.14/1.23  tff(c_157, plain, (![A_48, B_49]: (k10_relat_1(A_48, k1_relat_1(B_49))=k1_relat_1(k5_relat_1(A_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.23  tff(c_166, plain, (![A_48, A_17]: (k1_relat_1(k5_relat_1(A_48, k6_partfun1(A_17)))=k10_relat_1(A_48, A_17) | ~v1_relat_1(k6_partfun1(A_17)) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_45, c_157])).
% 2.14/1.23  tff(c_180, plain, (![A_51, A_52]: (k1_relat_1(k5_relat_1(A_51, k6_partfun1(A_52)))=k10_relat_1(A_51, A_52) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_166])).
% 2.14/1.23  tff(c_192, plain, (![A_18, B_19]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_18, B_19)))=k10_relat_1(k6_partfun1(B_19), A_18) | ~v1_relat_1(k6_partfun1(B_19)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_180])).
% 2.14/1.23  tff(c_196, plain, (![B_19, A_18]: (k10_relat_1(k6_partfun1(B_19), A_18)=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_45, c_192])).
% 2.14/1.23  tff(c_36, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.23  tff(c_274, plain, (![A_65, B_66, C_67, D_68]: (k8_relset_1(A_65, B_66, C_67, D_68)=k10_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.23  tff(c_276, plain, (![A_24, D_68]: (k8_relset_1(A_24, A_24, k6_partfun1(A_24), D_68)=k10_relat_1(k6_partfun1(A_24), D_68))), inference(resolution, [status(thm)], [c_36, c_274])).
% 2.14/1.23  tff(c_278, plain, (![A_24, D_68]: (k8_relset_1(A_24, A_24, k6_partfun1(A_24), D_68)=k3_xboole_0(D_68, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_276])).
% 2.14/1.23  tff(c_40, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.23  tff(c_279, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_40])).
% 2.14/1.23  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_279])).
% 2.14/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  Inference rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Ref     : 0
% 2.14/1.23  #Sup     : 49
% 2.14/1.23  #Fact    : 0
% 2.14/1.23  #Define  : 0
% 2.14/1.23  #Split   : 0
% 2.14/1.23  #Chain   : 0
% 2.14/1.23  #Close   : 0
% 2.14/1.23  
% 2.14/1.23  Ordering : KBO
% 2.14/1.23  
% 2.14/1.23  Simplification rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Subsume      : 1
% 2.14/1.23  #Demod        : 26
% 2.14/1.23  #Tautology    : 32
% 2.14/1.23  #SimpNegUnit  : 1
% 2.14/1.23  #BackRed      : 1
% 2.14/1.23  
% 2.14/1.23  #Partial instantiations: 0
% 2.14/1.23  #Strategies tried      : 1
% 2.14/1.23  
% 2.14/1.23  Timing (in seconds)
% 2.14/1.23  ----------------------
% 2.14/1.23  Preprocessing        : 0.32
% 2.14/1.23  Parsing              : 0.17
% 2.14/1.23  CNF conversion       : 0.02
% 2.14/1.23  Main loop            : 0.18
% 2.14/1.23  Inferencing          : 0.07
% 2.14/1.23  Reduction            : 0.06
% 2.14/1.23  Demodulation         : 0.05
% 2.14/1.23  BG Simplification    : 0.01
% 2.14/1.23  Subsumption          : 0.02
% 2.14/1.23  Abstraction          : 0.01
% 2.25/1.23  MUC search           : 0.00
% 2.25/1.23  Cooper               : 0.00
% 2.25/1.23  Total                : 0.53
% 2.25/1.23  Index Insertion      : 0.00
% 2.25/1.23  Index Deletion       : 0.00
% 2.25/1.23  Index Matching       : 0.00
% 2.25/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
