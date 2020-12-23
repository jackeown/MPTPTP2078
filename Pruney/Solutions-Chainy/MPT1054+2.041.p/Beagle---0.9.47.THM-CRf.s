%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  87 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_24,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_12,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_22,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_118,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k8_relset_1(A_34,B_35,C_36,D_37) = k10_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_124,plain,(
    ! [A_17,D_37] : k8_relset_1(A_17,A_17,k6_partfun1(A_17),D_37) = k10_relat_1(k6_partfun1(A_17),D_37) ),
    inference(resolution,[status(thm)],[c_29,c_118])).

tff(c_157,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( m1_subset_1(k8_relset_1(A_41,B_42,C_43,D_44),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [A_17,D_37] :
      ( m1_subset_1(k10_relat_1(k6_partfun1(A_17),D_37),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_157])).

tff(c_175,plain,(
    ! [A_45,D_46] : m1_subset_1(k10_relat_1(k6_partfun1(A_45),D_46),k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_169])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( k9_relat_1(k6_relat_1(A_7),B_8) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_7,B_8] :
      ( k9_relat_1(k6_partfun1(A_7),B_8) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_186,plain,(
    ! [A_45,D_46] : k9_relat_1(k6_partfun1(A_45),k10_relat_1(k6_partfun1(A_45),D_46)) = k10_relat_1(k6_partfun1(A_45),D_46) ),
    inference(resolution,[status(thm)],[c_175,c_30])).

tff(c_8,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_3] : k2_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_237,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,k10_relat_1(B_59,A_60)) = A_60
      | ~ r1_tarski(A_60,k2_relat_1(B_59))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    ! [A_3,A_60] :
      ( k9_relat_1(k6_partfun1(A_3),k10_relat_1(k6_partfun1(A_3),A_60)) = A_60
      | ~ r1_tarski(A_60,A_3)
      | ~ v1_funct_1(k6_partfun1(A_3))
      | ~ v1_relat_1(k6_partfun1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_237])).

tff(c_246,plain,(
    ! [A_61,A_62] :
      ( k10_relat_1(k6_partfun1(A_61),A_62) = A_62
      | ~ r1_tarski(A_62,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_31,c_186,c_242])).

tff(c_26,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_26])).

tff(c_261,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_147])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:23:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.87/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.87/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.23  
% 2.10/1.24  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.10/1.24  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.10/1.24  tff(f_61, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.10/1.24  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.10/1.24  tff(f_59, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.10/1.24  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.10/1.24  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.10/1.24  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.10/1.24  tff(f_33, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.10/1.24  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.10/1.24  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.24  tff(c_64, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.24  tff(c_68, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.10/1.24  tff(c_24, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.24  tff(c_10, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.24  tff(c_32, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 2.10/1.24  tff(c_12, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.24  tff(c_31, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 2.10/1.24  tff(c_22, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.24  tff(c_29, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 2.10/1.24  tff(c_118, plain, (![A_34, B_35, C_36, D_37]: (k8_relset_1(A_34, B_35, C_36, D_37)=k10_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.24  tff(c_124, plain, (![A_17, D_37]: (k8_relset_1(A_17, A_17, k6_partfun1(A_17), D_37)=k10_relat_1(k6_partfun1(A_17), D_37))), inference(resolution, [status(thm)], [c_29, c_118])).
% 2.10/1.24  tff(c_157, plain, (![A_41, B_42, C_43, D_44]: (m1_subset_1(k8_relset_1(A_41, B_42, C_43, D_44), k1_zfmisc_1(A_41)) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.24  tff(c_169, plain, (![A_17, D_37]: (m1_subset_1(k10_relat_1(k6_partfun1(A_17), D_37), k1_zfmisc_1(A_17)) | ~m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(superposition, [status(thm), theory('equality')], [c_124, c_157])).
% 2.10/1.24  tff(c_175, plain, (![A_45, D_46]: (m1_subset_1(k10_relat_1(k6_partfun1(A_45), D_46), k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_169])).
% 2.10/1.24  tff(c_16, plain, (![A_7, B_8]: (k9_relat_1(k6_relat_1(A_7), B_8)=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.24  tff(c_30, plain, (![A_7, B_8]: (k9_relat_1(k6_partfun1(A_7), B_8)=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 2.10/1.24  tff(c_186, plain, (![A_45, D_46]: (k9_relat_1(k6_partfun1(A_45), k10_relat_1(k6_partfun1(A_45), D_46))=k10_relat_1(k6_partfun1(A_45), D_46))), inference(resolution, [status(thm)], [c_175, c_30])).
% 2.10/1.24  tff(c_8, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.24  tff(c_33, plain, (![A_3]: (k2_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 2.10/1.24  tff(c_237, plain, (![B_59, A_60]: (k9_relat_1(B_59, k10_relat_1(B_59, A_60))=A_60 | ~r1_tarski(A_60, k2_relat_1(B_59)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.24  tff(c_242, plain, (![A_3, A_60]: (k9_relat_1(k6_partfun1(A_3), k10_relat_1(k6_partfun1(A_3), A_60))=A_60 | ~r1_tarski(A_60, A_3) | ~v1_funct_1(k6_partfun1(A_3)) | ~v1_relat_1(k6_partfun1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_237])).
% 2.10/1.24  tff(c_246, plain, (![A_61, A_62]: (k10_relat_1(k6_partfun1(A_61), A_62)=A_62 | ~r1_tarski(A_62, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_31, c_186, c_242])).
% 2.10/1.24  tff(c_26, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.24  tff(c_147, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_26])).
% 2.10/1.24  tff(c_261, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_147])).
% 2.10/1.24  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_261])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 51
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 0
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 1
% 2.10/1.24  #Demod        : 21
% 2.10/1.24  #Tautology    : 27
% 2.10/1.24  #SimpNegUnit  : 0
% 2.10/1.24  #BackRed      : 1
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.16
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.18
% 2.10/1.24  Inferencing          : 0.08
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.02
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.51
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
