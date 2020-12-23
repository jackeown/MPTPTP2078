%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 185 expanded)
%              Number of leaves         :   39 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 240 expanded)
%              Number of equality atoms :   41 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_89,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_42,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30])).

tff(c_28,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    ! [A_19] : v1_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_32,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_36,plain,(
    ! [A_23] : k2_funct_1(k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [A_23] : k2_funct_1(k6_partfun1(A_23)) = k6_partfun1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_36])).

tff(c_443,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(k2_funct_1(B_80),A_81) = k10_relat_1(B_80,A_81)
      | ~ v2_funct_1(B_80)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_452,plain,(
    ! [A_23,A_81] :
      ( k9_relat_1(k6_partfun1(A_23),A_81) = k10_relat_1(k6_partfun1(A_23),A_81)
      | ~ v2_funct_1(k6_partfun1(A_23))
      | ~ v1_funct_1(k6_partfun1(A_23))
      | ~ v1_relat_1(k6_partfun1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_443])).

tff(c_460,plain,(
    ! [A_82,A_83] : k9_relat_1(k6_partfun1(A_82),A_83) = k10_relat_1(k6_partfun1(A_82),A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_51,c_49,c_452])).

tff(c_16,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_22,plain,(
    ! [A_18] : v4_relat_1(k6_relat_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_18] : v4_relat_1(k6_partfun1(A_18),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_115,plain,(
    ! [B_44,A_45] :
      ( k7_relat_1(B_44,A_45) = B_44
      | ~ v4_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,(
    ! [A_18] :
      ( k7_relat_1(k6_partfun1(A_18),A_18) = k6_partfun1(A_18)
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_121,plain,(
    ! [A_18] : k7_relat_1(k6_partfun1(A_18),A_18) = k6_partfun1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_132,plain,(
    ! [B_48,A_49] :
      ( k2_relat_1(k7_relat_1(B_48,A_49)) = k9_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_18] :
      ( k9_relat_1(k6_partfun1(A_18),A_18) = k2_relat_1(k6_partfun1(A_18))
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_132])).

tff(c_145,plain,(
    ! [A_18] : k9_relat_1(k6_partfun1(A_18),A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_57,c_141])).

tff(c_467,plain,(
    ! [A_83] : k10_relat_1(k6_partfun1(A_83),A_83) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_145])).

tff(c_14,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_221,plain,(
    ! [A_63,B_64] :
      ( k5_relat_1(k6_partfun1(A_63),B_64) = B_64
      | ~ r1_tarski(k1_relat_1(B_64),A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_224,plain,(
    ! [A_63,A_15] :
      ( k5_relat_1(k6_partfun1(A_63),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_63)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_221])).

tff(c_226,plain,(
    ! [A_63,A_15] :
      ( k5_relat_1(k6_partfun1(A_63),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_224])).

tff(c_613,plain,(
    ! [B_98,C_99,A_100] :
      ( k10_relat_1(k5_relat_1(B_98,C_99),A_100) = k10_relat_1(B_98,k10_relat_1(C_99,A_100))
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_622,plain,(
    ! [A_63,A_15,A_100] :
      ( k10_relat_1(k6_partfun1(A_63),k10_relat_1(k6_partfun1(A_15),A_100)) = k10_relat_1(k6_partfun1(A_15),A_100)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(k6_partfun1(A_63))
      | ~ r1_tarski(A_15,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_613])).

tff(c_669,plain,(
    ! [A_113,A_114,A_115] :
      ( k10_relat_1(k6_partfun1(A_113),k10_relat_1(k6_partfun1(A_114),A_115)) = k10_relat_1(k6_partfun1(A_114),A_115)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_622])).

tff(c_714,plain,(
    ! [A_83,A_113] :
      ( k10_relat_1(k6_partfun1(A_83),A_83) = k10_relat_1(k6_partfun1(A_113),A_83)
      | ~ r1_tarski(A_83,A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_669])).

tff(c_731,plain,(
    ! [A_120,A_121] :
      ( k10_relat_1(k6_partfun1(A_120),A_121) = A_121
      | ~ r1_tarski(A_121,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_714])).

tff(c_40,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_47,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_639,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k8_relset_1(A_103,B_104,C_105,D_106) = k10_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_645,plain,(
    ! [A_28,D_106] : k8_relset_1(A_28,A_28,k6_partfun1(A_28),D_106) = k10_relat_1(k6_partfun1(A_28),D_106) ),
    inference(resolution,[status(thm)],[c_47,c_639])).

tff(c_44,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_647,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_44])).

tff(c_744,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_647])).

tff(c_789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:11:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.78/1.37  
% 2.78/1.37  %Foreground sorts:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Background operators:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Foreground operators:
% 2.78/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.37  
% 2.78/1.38  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.78/1.38  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.38  tff(f_97, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.78/1.38  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.78/1.38  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.78/1.38  tff(f_89, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 2.78/1.38  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.78/1.38  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.38  tff(f_71, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.78/1.38  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.78/1.38  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.38  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.78/1.38  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.78/1.38  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.78/1.38  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.78/1.38  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.78/1.38  tff(c_100, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.38  tff(c_104, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_100])).
% 2.78/1.38  tff(c_42, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.78/1.38  tff(c_30, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.38  tff(c_50, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30])).
% 2.78/1.38  tff(c_28, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.38  tff(c_51, plain, (![A_19]: (v1_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28])).
% 2.78/1.38  tff(c_32, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.38  tff(c_49, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 2.78/1.38  tff(c_36, plain, (![A_23]: (k2_funct_1(k6_relat_1(A_23))=k6_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.78/1.38  tff(c_48, plain, (![A_23]: (k2_funct_1(k6_partfun1(A_23))=k6_partfun1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_36])).
% 2.78/1.38  tff(c_443, plain, (![B_80, A_81]: (k9_relat_1(k2_funct_1(B_80), A_81)=k10_relat_1(B_80, A_81) | ~v2_funct_1(B_80) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.38  tff(c_452, plain, (![A_23, A_81]: (k9_relat_1(k6_partfun1(A_23), A_81)=k10_relat_1(k6_partfun1(A_23), A_81) | ~v2_funct_1(k6_partfun1(A_23)) | ~v1_funct_1(k6_partfun1(A_23)) | ~v1_relat_1(k6_partfun1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_443])).
% 2.78/1.38  tff(c_460, plain, (![A_82, A_83]: (k9_relat_1(k6_partfun1(A_82), A_83)=k10_relat_1(k6_partfun1(A_82), A_83))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_51, c_49, c_452])).
% 2.78/1.38  tff(c_16, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.38  tff(c_57, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 2.78/1.38  tff(c_22, plain, (![A_18]: (v4_relat_1(k6_relat_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.38  tff(c_54, plain, (![A_18]: (v4_relat_1(k6_partfun1(A_18), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 2.78/1.38  tff(c_115, plain, (![B_44, A_45]: (k7_relat_1(B_44, A_45)=B_44 | ~v4_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.78/1.38  tff(c_118, plain, (![A_18]: (k7_relat_1(k6_partfun1(A_18), A_18)=k6_partfun1(A_18) | ~v1_relat_1(k6_partfun1(A_18)))), inference(resolution, [status(thm)], [c_54, c_115])).
% 2.78/1.38  tff(c_121, plain, (![A_18]: (k7_relat_1(k6_partfun1(A_18), A_18)=k6_partfun1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_118])).
% 2.78/1.38  tff(c_132, plain, (![B_48, A_49]: (k2_relat_1(k7_relat_1(B_48, A_49))=k9_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.38  tff(c_141, plain, (![A_18]: (k9_relat_1(k6_partfun1(A_18), A_18)=k2_relat_1(k6_partfun1(A_18)) | ~v1_relat_1(k6_partfun1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_132])).
% 2.78/1.38  tff(c_145, plain, (![A_18]: (k9_relat_1(k6_partfun1(A_18), A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_57, c_141])).
% 2.78/1.38  tff(c_467, plain, (![A_83]: (k10_relat_1(k6_partfun1(A_83), A_83)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_460, c_145])).
% 2.78/1.38  tff(c_14, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.38  tff(c_58, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 2.78/1.38  tff(c_18, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.78/1.38  tff(c_221, plain, (![A_63, B_64]: (k5_relat_1(k6_partfun1(A_63), B_64)=B_64 | ~r1_tarski(k1_relat_1(B_64), A_63) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 2.78/1.38  tff(c_224, plain, (![A_63, A_15]: (k5_relat_1(k6_partfun1(A_63), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_63) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_221])).
% 2.78/1.38  tff(c_226, plain, (![A_63, A_15]: (k5_relat_1(k6_partfun1(A_63), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_224])).
% 2.78/1.38  tff(c_613, plain, (![B_98, C_99, A_100]: (k10_relat_1(k5_relat_1(B_98, C_99), A_100)=k10_relat_1(B_98, k10_relat_1(C_99, A_100)) | ~v1_relat_1(C_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.38  tff(c_622, plain, (![A_63, A_15, A_100]: (k10_relat_1(k6_partfun1(A_63), k10_relat_1(k6_partfun1(A_15), A_100))=k10_relat_1(k6_partfun1(A_15), A_100) | ~v1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(k6_partfun1(A_63)) | ~r1_tarski(A_15, A_63))), inference(superposition, [status(thm), theory('equality')], [c_226, c_613])).
% 2.78/1.38  tff(c_669, plain, (![A_113, A_114, A_115]: (k10_relat_1(k6_partfun1(A_113), k10_relat_1(k6_partfun1(A_114), A_115))=k10_relat_1(k6_partfun1(A_114), A_115) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_622])).
% 2.78/1.38  tff(c_714, plain, (![A_83, A_113]: (k10_relat_1(k6_partfun1(A_83), A_83)=k10_relat_1(k6_partfun1(A_113), A_83) | ~r1_tarski(A_83, A_113))), inference(superposition, [status(thm), theory('equality')], [c_467, c_669])).
% 2.78/1.38  tff(c_731, plain, (![A_120, A_121]: (k10_relat_1(k6_partfun1(A_120), A_121)=A_121 | ~r1_tarski(A_121, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_714])).
% 2.78/1.38  tff(c_40, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.78/1.38  tff(c_47, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 2.78/1.38  tff(c_639, plain, (![A_103, B_104, C_105, D_106]: (k8_relset_1(A_103, B_104, C_105, D_106)=k10_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.38  tff(c_645, plain, (![A_28, D_106]: (k8_relset_1(A_28, A_28, k6_partfun1(A_28), D_106)=k10_relat_1(k6_partfun1(A_28), D_106))), inference(resolution, [status(thm)], [c_47, c_639])).
% 2.78/1.38  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.78/1.38  tff(c_647, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_44])).
% 2.78/1.38  tff(c_744, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_731, c_647])).
% 2.78/1.38  tff(c_789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_744])).
% 2.78/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  Inference rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Ref     : 0
% 2.78/1.38  #Sup     : 161
% 2.78/1.38  #Fact    : 0
% 2.78/1.38  #Define  : 0
% 2.78/1.38  #Split   : 1
% 2.78/1.38  #Chain   : 0
% 2.78/1.38  #Close   : 0
% 2.78/1.38  
% 2.78/1.38  Ordering : KBO
% 2.78/1.38  
% 2.78/1.38  Simplification rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Subsume      : 2
% 2.78/1.38  #Demod        : 52
% 2.78/1.38  #Tautology    : 105
% 2.78/1.38  #SimpNegUnit  : 0
% 2.78/1.38  #BackRed      : 4
% 2.78/1.38  
% 2.78/1.38  #Partial instantiations: 0
% 2.78/1.38  #Strategies tried      : 1
% 2.78/1.38  
% 2.78/1.38  Timing (in seconds)
% 2.78/1.38  ----------------------
% 2.78/1.39  Preprocessing        : 0.32
% 2.78/1.39  Parsing              : 0.17
% 2.78/1.39  CNF conversion       : 0.02
% 2.78/1.39  Main loop            : 0.31
% 2.78/1.39  Inferencing          : 0.13
% 2.78/1.39  Reduction            : 0.09
% 2.78/1.39  Demodulation         : 0.07
% 2.78/1.39  BG Simplification    : 0.02
% 2.78/1.39  Subsumption          : 0.05
% 2.78/1.39  Abstraction          : 0.02
% 2.78/1.39  MUC search           : 0.00
% 2.78/1.39  Cooper               : 0.00
% 2.78/1.39  Total                : 0.66
% 2.78/1.39  Index Insertion      : 0.00
% 2.78/1.39  Index Deletion       : 0.00
% 2.78/1.39  Index Matching       : 0.00
% 2.78/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
