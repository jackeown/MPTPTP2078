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

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   63 (  84 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  88 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_73,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_36,A_3] :
      ( r1_tarski(A_36,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_36,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_89,plain,(
    ! [A_38,A_39] :
      ( r1_tarski(A_38,A_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_39)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_85])).

tff(c_97,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_34,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_28,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_partfun1(B_17),k6_partfun1(A_16)) = k6_partfun1(k3_xboole_0(A_16,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_34,c_28])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( k10_relat_1(A_44,k1_relat_1(B_45)) = k1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    ! [A_44,A_15] :
      ( k1_relat_1(k5_relat_1(A_44,k6_partfun1(A_15))) = k10_relat_1(A_44,A_15)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_129])).

tff(c_152,plain,(
    ! [A_48,A_49] :
      ( k1_relat_1(k5_relat_1(A_48,k6_partfun1(A_49))) = k10_relat_1(A_48,A_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_138])).

tff(c_164,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_16,B_17))) = k10_relat_1(k6_partfun1(B_17),A_16)
      | ~ v1_relat_1(k6_partfun1(B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_152])).

tff(c_168,plain,(
    ! [B_17,A_16] : k10_relat_1(k6_partfun1(B_17),A_16) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_42,c_164])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_236,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k8_relset_1(A_60,B_61,C_62,D_63) = k10_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_238,plain,(
    ! [A_22,D_63] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_63) = k10_relat_1(k6_partfun1(A_22),D_63) ),
    inference(resolution,[status(thm)],[c_39,c_236])).

tff(c_240,plain,(
    ! [A_22,D_63] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_63) = k3_xboole_0(D_63,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_238])).

tff(c_36,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_241,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_36])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:41:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.03/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.03/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.23  
% 2.12/1.24  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.12/1.24  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.12/1.24  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.12/1.24  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.12/1.24  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.12/1.24  tff(f_68, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.12/1.24  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.12/1.24  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.12/1.24  tff(f_60, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.12/1.24  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.12/1.24  tff(f_66, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.12/1.24  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.12/1.24  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.24  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.24  tff(c_81, plain, (![A_36, B_37]: (r2_hidden(A_36, B_37) | v1_xboole_0(B_37) | ~m1_subset_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.24  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.24  tff(c_85, plain, (![A_36, A_3]: (r1_tarski(A_36, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_36, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_81, c_4])).
% 2.12/1.24  tff(c_89, plain, (![A_38, A_39]: (r1_tarski(A_38, A_39) | ~m1_subset_1(A_38, k1_zfmisc_1(A_39)))), inference(negUnitSimplification, [status(thm)], [c_16, c_85])).
% 2.12/1.24  tff(c_97, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_89])).
% 2.12/1.24  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.24  tff(c_101, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.12/1.24  tff(c_34, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.24  tff(c_20, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.24  tff(c_43, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20])).
% 2.12/1.24  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.24  tff(c_42, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 2.12/1.24  tff(c_28, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.24  tff(c_40, plain, (![B_17, A_16]: (k5_relat_1(k6_partfun1(B_17), k6_partfun1(A_16))=k6_partfun1(k3_xboole_0(A_16, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_34, c_28])).
% 2.12/1.24  tff(c_129, plain, (![A_44, B_45]: (k10_relat_1(A_44, k1_relat_1(B_45))=k1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.24  tff(c_138, plain, (![A_44, A_15]: (k1_relat_1(k5_relat_1(A_44, k6_partfun1(A_15)))=k10_relat_1(A_44, A_15) | ~v1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_42, c_129])).
% 2.12/1.24  tff(c_152, plain, (![A_48, A_49]: (k1_relat_1(k5_relat_1(A_48, k6_partfun1(A_49)))=k10_relat_1(A_48, A_49) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_138])).
% 2.12/1.24  tff(c_164, plain, (![A_16, B_17]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_16, B_17)))=k10_relat_1(k6_partfun1(B_17), A_16) | ~v1_relat_1(k6_partfun1(B_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_152])).
% 2.12/1.24  tff(c_168, plain, (![B_17, A_16]: (k10_relat_1(k6_partfun1(B_17), A_16)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_42, c_164])).
% 2.12/1.24  tff(c_32, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.24  tff(c_39, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 2.12/1.24  tff(c_236, plain, (![A_60, B_61, C_62, D_63]: (k8_relset_1(A_60, B_61, C_62, D_63)=k10_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.24  tff(c_238, plain, (![A_22, D_63]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_63)=k10_relat_1(k6_partfun1(A_22), D_63))), inference(resolution, [status(thm)], [c_39, c_236])).
% 2.12/1.24  tff(c_240, plain, (![A_22, D_63]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_63)=k3_xboole_0(D_63, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_238])).
% 2.12/1.24  tff(c_36, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.24  tff(c_241, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_36])).
% 2.12/1.24  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_241])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 41
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 0
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 1
% 2.12/1.24  #Demod        : 26
% 2.12/1.24  #Tautology    : 24
% 2.12/1.24  #SimpNegUnit  : 1
% 2.12/1.24  #BackRed      : 1
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.31
% 2.12/1.24  Parsing              : 0.16
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.17
% 2.12/1.24  Inferencing          : 0.07
% 2.12/1.24  Reduction            : 0.05
% 2.12/1.25  Demodulation         : 0.04
% 2.12/1.25  BG Simplification    : 0.01
% 2.12/1.25  Subsumption          : 0.02
% 2.12/1.25  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.50
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
