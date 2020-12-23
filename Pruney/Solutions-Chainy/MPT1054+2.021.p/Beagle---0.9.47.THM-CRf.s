%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   64 (  85 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  90 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_75,negated_conjecture,(
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

tff(f_70,axiom,(
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

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_89,plain,(
    ! [A_37,A_3] :
      ( r1_tarski(A_37,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_93,plain,(
    ! [A_39,A_40] :
      ( r1_tarski(A_39,A_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_89])).

tff(c_101,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_36,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_30,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_partfun1(B_17),k6_partfun1(A_16)) = k6_partfun1(k3_xboole_0(A_16,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_36,c_30])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,(
    ! [A_45,A_14] :
      ( k1_relat_1(k5_relat_1(A_45,k6_partfun1(A_14))) = k10_relat_1(A_45,A_14)
      | ~ v1_relat_1(k6_partfun1(A_14))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_133])).

tff(c_147,plain,(
    ! [A_47,A_48] :
      ( k1_relat_1(k5_relat_1(A_47,k6_partfun1(A_48))) = k10_relat_1(A_47,A_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_142])).

tff(c_159,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_16,B_17))) = k10_relat_1(k6_partfun1(B_17),A_16)
      | ~ v1_relat_1(k6_partfun1(B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_147])).

tff(c_163,plain,(
    ! [B_17,A_16] : k10_relat_1(k6_partfun1(B_17),A_16) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_159])).

tff(c_34,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_240,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k8_relset_1(A_61,B_62,C_63,D_64) = k10_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_242,plain,(
    ! [A_22,D_64] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_64) = k10_relat_1(k6_partfun1(A_22),D_64) ),
    inference(resolution,[status(thm)],[c_41,c_240])).

tff(c_244,plain,(
    ! [A_22,D_64] : k8_relset_1(A_22,A_22,k6_partfun1(A_22),D_64) = k3_xboole_0(D_64,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_242])).

tff(c_38,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_246,plain,(
    k3_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_38])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.09/1.23  
% 2.09/1.23  %Foreground sorts:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Background operators:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Foreground operators:
% 2.09/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.23  
% 2.09/1.25  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.09/1.25  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.09/1.25  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.09/1.25  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.09/1.25  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.09/1.25  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.09/1.25  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.09/1.25  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.09/1.25  tff(f_62, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.09/1.25  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.09/1.25  tff(f_68, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.09/1.25  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.09/1.25  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.09/1.25  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.25  tff(c_85, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.25  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.09/1.25  tff(c_89, plain, (![A_37, A_3]: (r1_tarski(A_37, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_85, c_4])).
% 2.09/1.25  tff(c_93, plain, (![A_39, A_40]: (r1_tarski(A_39, A_40) | ~m1_subset_1(A_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_16, c_89])).
% 2.09/1.25  tff(c_101, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_93])).
% 2.09/1.25  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.25  tff(c_105, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_101, c_2])).
% 2.09/1.25  tff(c_36, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.25  tff(c_26, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.25  tff(c_44, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 2.09/1.25  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.25  tff(c_46, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22])).
% 2.09/1.25  tff(c_30, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.25  tff(c_42, plain, (![B_17, A_16]: (k5_relat_1(k6_partfun1(B_17), k6_partfun1(A_16))=k6_partfun1(k3_xboole_0(A_16, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_36, c_30])).
% 2.09/1.25  tff(c_133, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.25  tff(c_142, plain, (![A_45, A_14]: (k1_relat_1(k5_relat_1(A_45, k6_partfun1(A_14)))=k10_relat_1(A_45, A_14) | ~v1_relat_1(k6_partfun1(A_14)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_46, c_133])).
% 2.09/1.25  tff(c_147, plain, (![A_47, A_48]: (k1_relat_1(k5_relat_1(A_47, k6_partfun1(A_48)))=k10_relat_1(A_47, A_48) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_142])).
% 2.09/1.25  tff(c_159, plain, (![A_16, B_17]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_16, B_17)))=k10_relat_1(k6_partfun1(B_17), A_16) | ~v1_relat_1(k6_partfun1(B_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_147])).
% 2.09/1.25  tff(c_163, plain, (![B_17, A_16]: (k10_relat_1(k6_partfun1(B_17), A_16)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_159])).
% 2.09/1.25  tff(c_34, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.09/1.25  tff(c_41, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.09/1.25  tff(c_240, plain, (![A_61, B_62, C_63, D_64]: (k8_relset_1(A_61, B_62, C_63, D_64)=k10_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.25  tff(c_242, plain, (![A_22, D_64]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_64)=k10_relat_1(k6_partfun1(A_22), D_64))), inference(resolution, [status(thm)], [c_41, c_240])).
% 2.09/1.25  tff(c_244, plain, (![A_22, D_64]: (k8_relset_1(A_22, A_22, k6_partfun1(A_22), D_64)=k3_xboole_0(D_64, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_242])).
% 2.09/1.25  tff(c_38, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.09/1.25  tff(c_246, plain, (k3_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_38])).
% 2.09/1.25  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_246])).
% 2.09/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  Inference rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Ref     : 0
% 2.09/1.25  #Sup     : 41
% 2.09/1.25  #Fact    : 0
% 2.09/1.25  #Define  : 0
% 2.09/1.25  #Split   : 0
% 2.09/1.25  #Chain   : 0
% 2.09/1.25  #Close   : 0
% 2.09/1.25  
% 2.09/1.25  Ordering : KBO
% 2.09/1.25  
% 2.09/1.25  Simplification rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Subsume      : 1
% 2.09/1.25  #Demod        : 27
% 2.09/1.25  #Tautology    : 24
% 2.09/1.25  #SimpNegUnit  : 1
% 2.09/1.25  #BackRed      : 1
% 2.09/1.25  
% 2.09/1.25  #Partial instantiations: 0
% 2.09/1.25  #Strategies tried      : 1
% 2.09/1.25  
% 2.09/1.25  Timing (in seconds)
% 2.09/1.25  ----------------------
% 2.09/1.25  Preprocessing        : 0.31
% 2.09/1.25  Parsing              : 0.16
% 2.09/1.25  CNF conversion       : 0.02
% 2.09/1.25  Main loop            : 0.19
% 2.09/1.25  Inferencing          : 0.07
% 2.09/1.25  Reduction            : 0.06
% 2.09/1.25  Demodulation         : 0.04
% 2.09/1.25  BG Simplification    : 0.01
% 2.09/1.25  Subsumption          : 0.02
% 2.09/1.25  Abstraction          : 0.01
% 2.09/1.25  MUC search           : 0.00
% 2.09/1.25  Cooper               : 0.00
% 2.09/1.25  Total                : 0.52
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
