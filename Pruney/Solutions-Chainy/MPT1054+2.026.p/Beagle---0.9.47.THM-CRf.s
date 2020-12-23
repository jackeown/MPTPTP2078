%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:15 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 183 expanded)
%              Number of leaves         :   40 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 238 expanded)
%              Number of equality atoms :   41 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_99,axiom,(
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
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

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

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_102,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_44,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_51,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30])).

tff(c_28,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ! [A_19] : v1_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_32,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32])).

tff(c_36,plain,(
    ! [A_23] : k2_funct_1(k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [A_23] : k2_funct_1(k6_partfun1(A_23)) = k6_partfun1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_36])).

tff(c_396,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k2_funct_1(B_79),A_80) = k9_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_405,plain,(
    ! [A_23,A_80] :
      ( k9_relat_1(k6_partfun1(A_23),A_80) = k10_relat_1(k6_partfun1(A_23),A_80)
      | ~ v2_funct_1(k6_partfun1(A_23))
      | ~ v1_funct_1(k6_partfun1(A_23))
      | ~ v1_relat_1(k6_partfun1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_396])).

tff(c_413,plain,(
    ! [A_81,A_82] : k9_relat_1(k6_partfun1(A_81),A_82) = k10_relat_1(k6_partfun1(A_81),A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52,c_50,c_405])).

tff(c_16,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_22,plain,(
    ! [A_18] : v4_relat_1(k6_relat_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_55,plain,(
    ! [A_18] : v4_relat_1(k6_partfun1(A_18),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_127,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [A_18] :
      ( k7_relat_1(k6_partfun1(A_18),A_18) = k6_partfun1(A_18)
      | ~ v1_relat_1(k6_partfun1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_55,c_127])).

tff(c_140,plain,(
    ! [A_53] : k7_relat_1(k6_partfun1(A_53),A_53) = k6_partfun1(A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_130])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_53] :
      ( k9_relat_1(k6_partfun1(A_53),A_53) = k2_relat_1(k6_partfun1(A_53))
      | ~ v1_relat_1(k6_partfun1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_6])).

tff(c_152,plain,(
    ! [A_53] : k9_relat_1(k6_partfun1(A_53),A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_58,c_146])).

tff(c_420,plain,(
    ! [A_82] : k10_relat_1(k6_partfun1(A_82),A_82) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_152])).

tff(c_14,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_216,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_partfun1(A_61),B_62) = B_62
      | ~ r1_tarski(k1_relat_1(B_62),A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_219,plain,(
    ! [A_61,A_15] :
      ( k5_relat_1(k6_partfun1(A_61),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_61)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_216])).

tff(c_221,plain,(
    ! [A_61,A_15] :
      ( k5_relat_1(k6_partfun1(A_61),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_219])).

tff(c_607,plain,(
    ! [B_96,C_97,A_98] :
      ( k10_relat_1(k5_relat_1(B_96,C_97),A_98) = k10_relat_1(B_96,k10_relat_1(C_97,A_98))
      | ~ v1_relat_1(C_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_616,plain,(
    ! [A_61,A_15,A_98] :
      ( k10_relat_1(k6_partfun1(A_61),k10_relat_1(k6_partfun1(A_15),A_98)) = k10_relat_1(k6_partfun1(A_15),A_98)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(k6_partfun1(A_61))
      | ~ r1_tarski(A_15,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_607])).

tff(c_720,plain,(
    ! [A_116,A_117,A_118] :
      ( k10_relat_1(k6_partfun1(A_116),k10_relat_1(k6_partfun1(A_117),A_118)) = k10_relat_1(k6_partfun1(A_117),A_118)
      | ~ r1_tarski(A_117,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_51,c_616])).

tff(c_765,plain,(
    ! [A_82,A_116] :
      ( k10_relat_1(k6_partfun1(A_82),A_82) = k10_relat_1(k6_partfun1(A_116),A_82)
      | ~ r1_tarski(A_82,A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_720])).

tff(c_775,plain,(
    ! [A_119,A_120] :
      ( k10_relat_1(k6_partfun1(A_119),A_120) = A_120
      | ~ r1_tarski(A_120,A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_765])).

tff(c_42,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_640,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k8_relset_1(A_104,B_105,C_106,D_107) = k10_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_647,plain,(
    ! [A_28,D_107] : k8_relset_1(A_28,A_28,k6_partfun1(A_28),D_107) = k10_relat_1(k6_partfun1(A_28),D_107) ),
    inference(resolution,[status(thm)],[c_42,c_640])).

tff(c_46,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_698,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_46])).

tff(c_788,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_698])).

tff(c_833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n008.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 14:41:30 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.37  
% 2.86/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.37  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.86/1.37  
% 2.86/1.37  %Foreground sorts:
% 2.86/1.37  
% 2.86/1.37  
% 2.86/1.37  %Background operators:
% 2.86/1.37  
% 2.86/1.37  
% 2.86/1.37  %Foreground operators:
% 2.86/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.86/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.86/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.86/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.86/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.86/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.86/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.86/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.37  
% 2.86/1.39  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.86/1.39  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.39  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.86/1.39  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.86/1.39  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.86/1.39  tff(f_89, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 2.86/1.39  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.86/1.39  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.86/1.39  tff(f_71, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.86/1.39  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.86/1.39  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.86/1.39  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.86/1.39  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.86/1.39  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.86/1.39  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.86/1.39  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.86/1.39  tff(c_102, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.39  tff(c_106, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_102])).
% 2.86/1.39  tff(c_44, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.86/1.39  tff(c_30, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.86/1.39  tff(c_51, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_30])).
% 2.86/1.39  tff(c_28, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.86/1.39  tff(c_52, plain, (![A_19]: (v1_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 2.86/1.39  tff(c_32, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.86/1.39  tff(c_50, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32])).
% 2.86/1.39  tff(c_36, plain, (![A_23]: (k2_funct_1(k6_relat_1(A_23))=k6_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.39  tff(c_49, plain, (![A_23]: (k2_funct_1(k6_partfun1(A_23))=k6_partfun1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_36])).
% 2.86/1.39  tff(c_396, plain, (![B_79, A_80]: (k10_relat_1(k2_funct_1(B_79), A_80)=k9_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.86/1.39  tff(c_405, plain, (![A_23, A_80]: (k9_relat_1(k6_partfun1(A_23), A_80)=k10_relat_1(k6_partfun1(A_23), A_80) | ~v2_funct_1(k6_partfun1(A_23)) | ~v1_funct_1(k6_partfun1(A_23)) | ~v1_relat_1(k6_partfun1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_396])).
% 2.86/1.39  tff(c_413, plain, (![A_81, A_82]: (k9_relat_1(k6_partfun1(A_81), A_82)=k10_relat_1(k6_partfun1(A_81), A_82))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_52, c_50, c_405])).
% 2.86/1.39  tff(c_16, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.39  tff(c_58, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 2.86/1.39  tff(c_22, plain, (![A_18]: (v4_relat_1(k6_relat_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.39  tff(c_55, plain, (![A_18]: (v4_relat_1(k6_partfun1(A_18), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22])).
% 2.86/1.39  tff(c_127, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.39  tff(c_130, plain, (![A_18]: (k7_relat_1(k6_partfun1(A_18), A_18)=k6_partfun1(A_18) | ~v1_relat_1(k6_partfun1(A_18)))), inference(resolution, [status(thm)], [c_55, c_127])).
% 2.86/1.39  tff(c_140, plain, (![A_53]: (k7_relat_1(k6_partfun1(A_53), A_53)=k6_partfun1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_130])).
% 2.86/1.39  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.39  tff(c_146, plain, (![A_53]: (k9_relat_1(k6_partfun1(A_53), A_53)=k2_relat_1(k6_partfun1(A_53)) | ~v1_relat_1(k6_partfun1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_6])).
% 2.86/1.39  tff(c_152, plain, (![A_53]: (k9_relat_1(k6_partfun1(A_53), A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_58, c_146])).
% 2.86/1.39  tff(c_420, plain, (![A_82]: (k10_relat_1(k6_partfun1(A_82), A_82)=A_82)), inference(superposition, [status(thm), theory('equality')], [c_413, c_152])).
% 2.86/1.39  tff(c_14, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.39  tff(c_59, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 2.86/1.39  tff(c_18, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.86/1.39  tff(c_216, plain, (![A_61, B_62]: (k5_relat_1(k6_partfun1(A_61), B_62)=B_62 | ~r1_tarski(k1_relat_1(B_62), A_61) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 2.86/1.39  tff(c_219, plain, (![A_61, A_15]: (k5_relat_1(k6_partfun1(A_61), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_61) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_216])).
% 2.86/1.39  tff(c_221, plain, (![A_61, A_15]: (k5_relat_1(k6_partfun1(A_61), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_219])).
% 2.86/1.39  tff(c_607, plain, (![B_96, C_97, A_98]: (k10_relat_1(k5_relat_1(B_96, C_97), A_98)=k10_relat_1(B_96, k10_relat_1(C_97, A_98)) | ~v1_relat_1(C_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.39  tff(c_616, plain, (![A_61, A_15, A_98]: (k10_relat_1(k6_partfun1(A_61), k10_relat_1(k6_partfun1(A_15), A_98))=k10_relat_1(k6_partfun1(A_15), A_98) | ~v1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(k6_partfun1(A_61)) | ~r1_tarski(A_15, A_61))), inference(superposition, [status(thm), theory('equality')], [c_221, c_607])).
% 2.86/1.39  tff(c_720, plain, (![A_116, A_117, A_118]: (k10_relat_1(k6_partfun1(A_116), k10_relat_1(k6_partfun1(A_117), A_118))=k10_relat_1(k6_partfun1(A_117), A_118) | ~r1_tarski(A_117, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_51, c_616])).
% 2.86/1.39  tff(c_765, plain, (![A_82, A_116]: (k10_relat_1(k6_partfun1(A_82), A_82)=k10_relat_1(k6_partfun1(A_116), A_82) | ~r1_tarski(A_82, A_116))), inference(superposition, [status(thm), theory('equality')], [c_420, c_720])).
% 2.86/1.39  tff(c_775, plain, (![A_119, A_120]: (k10_relat_1(k6_partfun1(A_119), A_120)=A_120 | ~r1_tarski(A_120, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_765])).
% 2.86/1.39  tff(c_42, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.39  tff(c_640, plain, (![A_104, B_105, C_106, D_107]: (k8_relset_1(A_104, B_105, C_106, D_107)=k10_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.86/1.39  tff(c_647, plain, (![A_28, D_107]: (k8_relset_1(A_28, A_28, k6_partfun1(A_28), D_107)=k10_relat_1(k6_partfun1(A_28), D_107))), inference(resolution, [status(thm)], [c_42, c_640])).
% 2.86/1.39  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.86/1.39  tff(c_698, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_46])).
% 2.86/1.39  tff(c_788, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_775, c_698])).
% 2.86/1.39  tff(c_833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_788])).
% 2.86/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  Inference rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Ref     : 0
% 2.86/1.39  #Sup     : 170
% 2.86/1.39  #Fact    : 0
% 2.86/1.39  #Define  : 0
% 2.86/1.39  #Split   : 1
% 2.86/1.39  #Chain   : 0
% 2.86/1.39  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 2
% 2.86/1.39  #Demod        : 54
% 2.86/1.39  #Tautology    : 115
% 2.86/1.39  #SimpNegUnit  : 0
% 2.86/1.39  #BackRed      : 4
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.33
% 2.86/1.39  Parsing              : 0.19
% 2.86/1.39  CNF conversion       : 0.02
% 2.86/1.39  Main loop            : 0.31
% 2.86/1.39  Inferencing          : 0.12
% 2.86/1.39  Reduction            : 0.09
% 2.86/1.39  Demodulation         : 0.07
% 2.86/1.39  BG Simplification    : 0.02
% 2.86/1.39  Subsumption          : 0.05
% 2.86/1.39  Abstraction          : 0.02
% 2.86/1.39  MUC search           : 0.00
% 2.86/1.39  Cooper               : 0.00
% 2.86/1.39  Total                : 0.68
% 2.86/1.39  Index Insertion      : 0.00
% 2.86/1.39  Index Deletion       : 0.00
% 2.86/1.39  Index Matching       : 0.00
% 2.86/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
