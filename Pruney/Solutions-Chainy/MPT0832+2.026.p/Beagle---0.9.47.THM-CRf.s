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
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 148 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 229 expanded)
%              Number of equality atoms :    8 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k6_relset_1(A_42,B_43,C_44,D_45) = k8_relat_1(C_44,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    ! [C_50] : k6_relset_1('#skF_3','#skF_1',C_50,'#skF_4') = k8_relat_1(C_50,'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( m1_subset_1(k6_relset_1(A_15,B_16,C_17,D_18),k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [C_50] :
      ( m1_subset_1(k8_relat_1(C_50,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_16])).

tff(c_98,plain,(
    ! [C_51] : m1_subset_1(k8_relat_1(C_51,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [C_51] :
      ( v1_relat_1(k8_relat_1(C_51,'#skF_4'))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_115,plain,(
    ! [C_51] : v1_relat_1(k8_relat_1(C_51,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [C_52] : v4_relat_1(k8_relat_1(C_52,'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [C_52] :
      ( k7_relat_1(k8_relat_1(C_52,'#skF_4'),'#skF_3') = k8_relat_1(C_52,'#skF_4')
      | ~ v1_relat_1(k8_relat_1(C_52,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_211,plain,(
    ! [C_77] : k7_relat_1(k8_relat_1(C_77,'#skF_4'),'#skF_3') = k8_relat_1(C_77,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_120])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_217,plain,(
    ! [C_77] :
      ( r1_tarski(k1_relat_1(k8_relat_1(C_77,'#skF_4')),'#skF_3')
      | ~ v1_relat_1(k8_relat_1(C_77,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_10])).

tff(c_223,plain,(
    ! [C_77] : r1_tarski(k1_relat_1(k8_relat_1(C_77,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_217])).

tff(c_150,plain,(
    ! [C_63,A_64,B_65] :
      ( m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ r1_tarski(k2_relat_1(C_63),B_65)
      | ~ r1_tarski(k1_relat_1(C_63),A_64)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    ! [C_44] : k6_relset_1('#skF_3','#skF_1',C_44,'#skF_4') = k8_relat_1(C_44,'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_22,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_22])).

tff(c_155,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_150,c_83])).

tff(c_170,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_155])).

tff(c_206,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_206])).

tff(c_228,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_236,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_228])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.38  
% 2.36/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.38  
% 2.36/1.38  %Foreground sorts:
% 2.36/1.38  
% 2.36/1.38  
% 2.36/1.38  %Background operators:
% 2.36/1.38  
% 2.36/1.38  
% 2.36/1.38  %Foreground operators:
% 2.36/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.36/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.38  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.36/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.38  
% 2.36/1.40  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.36/1.40  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.36/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.36/1.40  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.36/1.40  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.36/1.40  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.36/1.40  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.36/1.40  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.36/1.40  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.36/1.40  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.36/1.40  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.40  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.40  tff(c_28, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.40  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_28])).
% 2.36/1.40  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_31])).
% 2.36/1.40  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.40  tff(c_61, plain, (![A_42, B_43, C_44, D_45]: (k6_relset_1(A_42, B_43, C_44, D_45)=k8_relat_1(C_44, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.40  tff(c_84, plain, (![C_50]: (k6_relset_1('#skF_3', '#skF_1', C_50, '#skF_4')=k8_relat_1(C_50, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.36/1.40  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k6_relset_1(A_15, B_16, C_17, D_18), k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.40  tff(c_90, plain, (![C_50]: (m1_subset_1(k8_relat_1(C_50, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_84, c_16])).
% 2.36/1.40  tff(c_98, plain, (![C_51]: (m1_subset_1(k8_relat_1(C_51, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 2.36/1.40  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.40  tff(c_109, plain, (![C_51]: (v1_relat_1(k8_relat_1(C_51, '#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.36/1.40  tff(c_115, plain, (![C_51]: (v1_relat_1(k8_relat_1(C_51, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 2.36/1.40  tff(c_14, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.40  tff(c_116, plain, (![C_52]: (v4_relat_1(k8_relat_1(C_52, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_14])).
% 2.36/1.40  tff(c_8, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.40  tff(c_120, plain, (![C_52]: (k7_relat_1(k8_relat_1(C_52, '#skF_4'), '#skF_3')=k8_relat_1(C_52, '#skF_4') | ~v1_relat_1(k8_relat_1(C_52, '#skF_4')))), inference(resolution, [status(thm)], [c_116, c_8])).
% 2.36/1.40  tff(c_211, plain, (![C_77]: (k7_relat_1(k8_relat_1(C_77, '#skF_4'), '#skF_3')=k8_relat_1(C_77, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_120])).
% 2.36/1.40  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.40  tff(c_217, plain, (![C_77]: (r1_tarski(k1_relat_1(k8_relat_1(C_77, '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1(C_77, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_211, c_10])).
% 2.36/1.40  tff(c_223, plain, (![C_77]: (r1_tarski(k1_relat_1(k8_relat_1(C_77, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_217])).
% 2.36/1.40  tff(c_150, plain, (![C_63, A_64, B_65]: (m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~r1_tarski(k2_relat_1(C_63), B_65) | ~r1_tarski(k1_relat_1(C_63), A_64) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.36/1.40  tff(c_64, plain, (![C_44]: (k6_relset_1('#skF_3', '#skF_1', C_44, '#skF_4')=k8_relat_1(C_44, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.36/1.40  tff(c_22, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.40  tff(c_83, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_22])).
% 2.36/1.40  tff(c_155, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_150, c_83])).
% 2.36/1.40  tff(c_170, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_155])).
% 2.36/1.40  tff(c_206, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_170])).
% 2.36/1.40  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_206])).
% 2.36/1.40  tff(c_228, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_170])).
% 2.36/1.40  tff(c_236, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_228])).
% 2.36/1.40  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_236])).
% 2.36/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.40  
% 2.36/1.40  Inference rules
% 2.36/1.40  ----------------------
% 2.36/1.40  #Ref     : 0
% 2.36/1.40  #Sup     : 43
% 2.36/1.40  #Fact    : 0
% 2.36/1.40  #Define  : 0
% 2.36/1.40  #Split   : 1
% 2.36/1.40  #Chain   : 0
% 2.36/1.40  #Close   : 0
% 2.36/1.40  
% 2.36/1.40  Ordering : KBO
% 2.36/1.40  
% 2.36/1.40  Simplification rules
% 2.36/1.40  ----------------------
% 2.36/1.40  #Subsume      : 0
% 2.36/1.40  #Demod        : 20
% 2.36/1.40  #Tautology    : 11
% 2.36/1.40  #SimpNegUnit  : 0
% 2.36/1.40  #BackRed      : 3
% 2.36/1.40  
% 2.36/1.40  #Partial instantiations: 0
% 2.36/1.40  #Strategies tried      : 1
% 2.36/1.40  
% 2.36/1.40  Timing (in seconds)
% 2.36/1.40  ----------------------
% 2.36/1.40  Preprocessing        : 0.38
% 2.36/1.40  Parsing              : 0.18
% 2.36/1.40  CNF conversion       : 0.03
% 2.36/1.40  Main loop            : 0.24
% 2.36/1.40  Inferencing          : 0.10
% 2.36/1.40  Reduction            : 0.07
% 2.36/1.40  Demodulation         : 0.05
% 2.36/1.40  BG Simplification    : 0.02
% 2.36/1.40  Subsumption          : 0.03
% 2.36/1.40  Abstraction          : 0.02
% 2.36/1.40  MUC search           : 0.00
% 2.36/1.40  Cooper               : 0.00
% 2.36/1.40  Total                : 0.66
% 2.36/1.40  Index Insertion      : 0.00
% 2.36/1.40  Index Deletion       : 0.00
% 2.36/1.40  Index Matching       : 0.00
% 2.36/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
