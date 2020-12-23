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
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   62 (  89 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 109 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_73,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_34,plain,(
    ! [A_19] : k6_relat_1(A_19) = k6_partfun1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_18,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_6] : v1_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_22,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( k9_relat_1(k6_relat_1(A_12),B_13) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [A_35,B_36] :
      ( k9_relat_1(k6_partfun1(A_35),B_36) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_120,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_126,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k10_relat_1(B_37,k9_relat_1(B_37,A_38)),A_38)
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,
    ( r1_tarski(k10_relat_1(k6_partfun1('#skF_1'),'#skF_2'),'#skF_2')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_126])).

tff(c_134,plain,(
    r1_tarski(k10_relat_1(k6_partfun1('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_43,c_41,c_131])).

tff(c_80,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_12,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_198,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k10_relat_1(B_46,k9_relat_1(B_46,A_45)))
      | ~ r1_tarski(A_45,k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,
    ( r1_tarski('#skF_2',k10_relat_1(k6_partfun1('#skF_1'),'#skF_2'))
    | ~ r1_tarski('#skF_2',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_198])).

tff(c_216,plain,(
    r1_tarski('#skF_2',k10_relat_1(k6_partfun1('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_88,c_46,c_209])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,
    ( k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski(k10_relat_1(k6_partfun1('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_221,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_218])).

tff(c_32,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_39,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_276,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_283,plain,(
    ! [A_18,D_55] : k8_relset_1(A_18,A_18,k6_partfun1(A_18),D_55) = k10_relat_1(k6_partfun1(A_18),D_55) ),
    inference(resolution,[status(thm)],[c_39,c_276])).

tff(c_36,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_284,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_36])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:02:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.31  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.31  
% 2.00/1.31  %Foreground sorts:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Background operators:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Foreground operators:
% 2.00/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.31  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.00/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.31  
% 2.30/1.32  tff(f_73, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.30/1.32  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.30/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.30/1.32  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.30/1.32  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.30/1.32  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 2.30/1.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.30/1.32  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.30/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.30/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.32  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.30/1.32  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.30/1.32  tff(c_34, plain, (![A_19]: (k6_relat_1(A_19)=k6_partfun1(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.32  tff(c_20, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.32  tff(c_42, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20])).
% 2.30/1.32  tff(c_18, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.32  tff(c_43, plain, (![A_6]: (v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 2.30/1.32  tff(c_22, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.32  tff(c_41, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22])).
% 2.30/1.32  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.32  tff(c_28, plain, (![A_12, B_13]: (k9_relat_1(k6_relat_1(A_12), B_13)=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.32  tff(c_108, plain, (![A_35, B_36]: (k9_relat_1(k6_partfun1(A_35), B_36)=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 2.30/1.32  tff(c_120, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_108])).
% 2.30/1.32  tff(c_126, plain, (![B_37, A_38]: (r1_tarski(k10_relat_1(B_37, k9_relat_1(B_37, A_38)), A_38) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.32  tff(c_131, plain, (r1_tarski(k10_relat_1(k6_partfun1('#skF_1'), '#skF_2'), '#skF_2') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_126])).
% 2.30/1.32  tff(c_134, plain, (r1_tarski(k10_relat_1(k6_partfun1('#skF_1'), '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_43, c_41, c_131])).
% 2.30/1.32  tff(c_80, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.32  tff(c_88, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_80])).
% 2.30/1.32  tff(c_12, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.32  tff(c_46, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 2.30/1.32  tff(c_198, plain, (![A_45, B_46]: (r1_tarski(A_45, k10_relat_1(B_46, k9_relat_1(B_46, A_45))) | ~r1_tarski(A_45, k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.32  tff(c_209, plain, (r1_tarski('#skF_2', k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_198])).
% 2.30/1.32  tff(c_216, plain, (r1_tarski('#skF_2', k10_relat_1(k6_partfun1('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_88, c_46, c_209])).
% 2.30/1.32  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.32  tff(c_218, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski(k10_relat_1(k6_partfun1('#skF_1'), '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_216, c_2])).
% 2.30/1.32  tff(c_221, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_218])).
% 2.30/1.32  tff(c_32, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.32  tff(c_39, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 2.30/1.32  tff(c_276, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.30/1.32  tff(c_283, plain, (![A_18, D_55]: (k8_relset_1(A_18, A_18, k6_partfun1(A_18), D_55)=k10_relat_1(k6_partfun1(A_18), D_55))), inference(resolution, [status(thm)], [c_39, c_276])).
% 2.30/1.32  tff(c_36, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.32  tff(c_284, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_36])).
% 2.30/1.32  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_284])).
% 2.30/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.32  
% 2.30/1.32  Inference rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Ref     : 0
% 2.30/1.32  #Sup     : 49
% 2.30/1.32  #Fact    : 0
% 2.30/1.32  #Define  : 0
% 2.30/1.32  #Split   : 1
% 2.30/1.32  #Chain   : 0
% 2.30/1.32  #Close   : 0
% 2.30/1.32  
% 2.30/1.32  Ordering : KBO
% 2.30/1.32  
% 2.30/1.32  Simplification rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Subsume      : 0
% 2.30/1.32  #Demod        : 55
% 2.30/1.32  #Tautology    : 33
% 2.30/1.32  #SimpNegUnit  : 0
% 2.30/1.32  #BackRed      : 5
% 2.30/1.32  
% 2.30/1.32  #Partial instantiations: 0
% 2.30/1.32  #Strategies tried      : 1
% 2.30/1.32  
% 2.30/1.32  Timing (in seconds)
% 2.30/1.32  ----------------------
% 2.30/1.33  Preprocessing        : 0.33
% 2.30/1.33  Parsing              : 0.17
% 2.30/1.33  CNF conversion       : 0.02
% 2.30/1.33  Main loop            : 0.19
% 2.30/1.33  Inferencing          : 0.07
% 2.30/1.33  Reduction            : 0.07
% 2.30/1.33  Demodulation         : 0.05
% 2.30/1.33  BG Simplification    : 0.01
% 2.30/1.33  Subsumption          : 0.03
% 2.30/1.33  Abstraction          : 0.01
% 2.30/1.33  MUC search           : 0.00
% 2.30/1.33  Cooper               : 0.00
% 2.30/1.33  Total                : 0.55
% 2.30/1.33  Index Insertion      : 0.00
% 2.30/1.33  Index Deletion       : 0.00
% 2.30/1.33  Index Matching       : 0.00
% 2.30/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
