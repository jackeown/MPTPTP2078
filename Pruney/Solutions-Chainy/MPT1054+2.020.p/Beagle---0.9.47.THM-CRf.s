%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   63 (  90 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 109 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_48,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_34,A_1] :
      ( r1_tarski(A_34,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_34,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_94,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(A_36,A_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_90])).

tff(c_102,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_36,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_20,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_partfun1(A_38),B_39) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24])).

tff(c_106,plain,(
    ! [A_38,A_12] :
      ( k5_relat_1(k6_partfun1(A_38),k6_partfun1(A_12)) = k6_partfun1(A_12)
      | ~ r1_tarski(A_12,A_38)
      | ~ v1_relat_1(k6_partfun1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_103])).

tff(c_108,plain,(
    ! [A_38,A_12] :
      ( k5_relat_1(k6_partfun1(A_38),k6_partfun1(A_12)) = k6_partfun1(A_12)
      | ~ r1_tarski(A_12,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106])).

tff(c_119,plain,(
    ! [A_43,B_44] :
      ( k10_relat_1(A_43,k1_relat_1(B_44)) = k1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [A_43,A_12] :
      ( k1_relat_1(k5_relat_1(A_43,k6_partfun1(A_12))) = k10_relat_1(A_43,A_12)
      | ~ v1_relat_1(k6_partfun1(A_12))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_119])).

tff(c_139,plain,(
    ! [A_47,A_48] :
      ( k1_relat_1(k5_relat_1(A_47,k6_partfun1(A_48))) = k10_relat_1(A_47,A_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128])).

tff(c_154,plain,(
    ! [A_38,A_12] :
      ( k10_relat_1(k6_partfun1(A_38),A_12) = k1_relat_1(k6_partfun1(A_12))
      | ~ v1_relat_1(k6_partfun1(A_38))
      | ~ r1_tarski(A_12,A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_139])).

tff(c_158,plain,(
    ! [A_38,A_12] :
      ( k10_relat_1(k6_partfun1(A_38),A_12) = A_12
      | ~ r1_tarski(A_12,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_47,c_154])).

tff(c_34,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_196,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k8_relset_1(A_57,B_58,C_59,D_60) = k10_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,(
    ! [A_20,D_60] : k8_relset_1(A_20,A_20,k6_partfun1(A_20),D_60) = k10_relat_1(k6_partfun1(A_20),D_60) ),
    inference(resolution,[status(thm)],[c_41,c_196])).

tff(c_38,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_200,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_38])).

tff(c_212,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_200])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.25  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.25  
% 2.14/1.26  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.14/1.26  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.14/1.26  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.26  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.26  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.14/1.26  tff(f_64, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.14/1.26  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.14/1.26  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.14/1.26  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.14/1.26  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.14/1.26  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.14/1.26  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.26  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.26  tff(c_86, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | v1_xboole_0(B_35) | ~m1_subset_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.26  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.26  tff(c_90, plain, (![A_34, A_1]: (r1_tarski(A_34, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_34, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_86, c_2])).
% 2.14/1.26  tff(c_94, plain, (![A_36, A_37]: (r1_tarski(A_36, A_37) | ~m1_subset_1(A_36, k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_14, c_90])).
% 2.14/1.26  tff(c_102, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_94])).
% 2.14/1.26  tff(c_36, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.26  tff(c_26, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.26  tff(c_44, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 2.14/1.26  tff(c_20, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.26  tff(c_47, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20])).
% 2.14/1.26  tff(c_24, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.26  tff(c_103, plain, (![A_38, B_39]: (k5_relat_1(k6_partfun1(A_38), B_39)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24])).
% 2.14/1.26  tff(c_106, plain, (![A_38, A_12]: (k5_relat_1(k6_partfun1(A_38), k6_partfun1(A_12))=k6_partfun1(A_12) | ~r1_tarski(A_12, A_38) | ~v1_relat_1(k6_partfun1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_103])).
% 2.14/1.26  tff(c_108, plain, (![A_38, A_12]: (k5_relat_1(k6_partfun1(A_38), k6_partfun1(A_12))=k6_partfun1(A_12) | ~r1_tarski(A_12, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_106])).
% 2.14/1.26  tff(c_119, plain, (![A_43, B_44]: (k10_relat_1(A_43, k1_relat_1(B_44))=k1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.26  tff(c_128, plain, (![A_43, A_12]: (k1_relat_1(k5_relat_1(A_43, k6_partfun1(A_12)))=k10_relat_1(A_43, A_12) | ~v1_relat_1(k6_partfun1(A_12)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_47, c_119])).
% 2.14/1.26  tff(c_139, plain, (![A_47, A_48]: (k1_relat_1(k5_relat_1(A_47, k6_partfun1(A_48)))=k10_relat_1(A_47, A_48) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_128])).
% 2.14/1.26  tff(c_154, plain, (![A_38, A_12]: (k10_relat_1(k6_partfun1(A_38), A_12)=k1_relat_1(k6_partfun1(A_12)) | ~v1_relat_1(k6_partfun1(A_38)) | ~r1_tarski(A_12, A_38))), inference(superposition, [status(thm), theory('equality')], [c_108, c_139])).
% 2.14/1.26  tff(c_158, plain, (![A_38, A_12]: (k10_relat_1(k6_partfun1(A_38), A_12)=A_12 | ~r1_tarski(A_12, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_47, c_154])).
% 2.14/1.26  tff(c_34, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.26  tff(c_41, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.14/1.26  tff(c_196, plain, (![A_57, B_58, C_59, D_60]: (k8_relset_1(A_57, B_58, C_59, D_60)=k10_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.26  tff(c_199, plain, (![A_20, D_60]: (k8_relset_1(A_20, A_20, k6_partfun1(A_20), D_60)=k10_relat_1(k6_partfun1(A_20), D_60))), inference(resolution, [status(thm)], [c_41, c_196])).
% 2.14/1.26  tff(c_38, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.26  tff(c_200, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_38])).
% 2.14/1.26  tff(c_212, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_158, c_200])).
% 2.14/1.26  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_212])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 33
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.26  #Split   : 0
% 2.14/1.26  #Chain   : 0
% 2.14/1.26  #Close   : 0
% 2.14/1.26  
% 2.14/1.26  Ordering : KBO
% 2.14/1.26  
% 2.14/1.26  Simplification rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Subsume      : 0
% 2.14/1.26  #Demod        : 15
% 2.14/1.26  #Tautology    : 17
% 2.14/1.26  #SimpNegUnit  : 1
% 2.14/1.26  #BackRed      : 1
% 2.14/1.26  
% 2.14/1.26  #Partial instantiations: 0
% 2.14/1.26  #Strategies tried      : 1
% 2.14/1.26  
% 2.14/1.26  Timing (in seconds)
% 2.14/1.26  ----------------------
% 2.14/1.26  Preprocessing        : 0.31
% 2.14/1.26  Parsing              : 0.16
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.16
% 2.14/1.26  Inferencing          : 0.07
% 2.14/1.26  Reduction            : 0.05
% 2.14/1.26  Demodulation         : 0.04
% 2.14/1.26  BG Simplification    : 0.01
% 2.14/1.26  Subsumption          : 0.02
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.50
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
