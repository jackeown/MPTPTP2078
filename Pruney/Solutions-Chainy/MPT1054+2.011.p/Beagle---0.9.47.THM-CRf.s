%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:13 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 180 expanded)
%              Number of leaves         :   42 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 225 expanded)
%              Number of equality atoms :   43 ( 115 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_87,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_44,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,(
    ! [A_19] : v1_relat_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_30])).

tff(c_28,plain,(
    ! [A_18] : v1_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_18] : v1_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_32,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ! [A_19] : v2_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32])).

tff(c_16,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    ! [A_16] : k1_relat_1(k6_partfun1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_36,plain,(
    ! [B_23,A_22] : k5_relat_1(k6_relat_1(B_23),k6_relat_1(A_22)) = k6_relat_1(k3_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_51,plain,(
    ! [B_23,A_22] : k5_relat_1(k6_partfun1(B_23),k6_partfun1(A_22)) = k6_partfun1(k3_xboole_0(A_22,B_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_44,c_36])).

tff(c_240,plain,(
    ! [A_63,B_64] :
      ( k10_relat_1(A_63,k1_relat_1(B_64)) = k1_relat_1(k5_relat_1(A_63,B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    ! [A_63,A_16] :
      ( k1_relat_1(k5_relat_1(A_63,k6_partfun1(A_16))) = k10_relat_1(A_63,A_16)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_240])).

tff(c_272,plain,(
    ! [A_67,A_68] :
      ( k1_relat_1(k5_relat_1(A_67,k6_partfun1(A_68))) = k10_relat_1(A_67,A_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_249])).

tff(c_284,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_22,B_23))) = k10_relat_1(k6_partfun1(B_23),A_22)
      | ~ v1_relat_1(k6_partfun1(B_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_272])).

tff(c_288,plain,(
    ! [B_23,A_22] : k10_relat_1(k6_partfun1(B_23),A_22) = k3_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_60,c_284])).

tff(c_38,plain,(
    ! [A_24] : k2_funct_1(k6_relat_1(A_24)) = k6_relat_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_24] : k2_funct_1(k6_partfun1(A_24)) = k6_partfun1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_38])).

tff(c_310,plain,(
    ! [B_71,A_72] :
      ( k9_relat_1(k2_funct_1(B_71),A_72) = k10_relat_1(B_71,A_72)
      | ~ v2_funct_1(B_71)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_319,plain,(
    ! [A_24,A_72] :
      ( k9_relat_1(k6_partfun1(A_24),A_72) = k10_relat_1(k6_partfun1(A_24),A_72)
      | ~ v2_funct_1(k6_partfun1(A_24))
      | ~ v1_funct_1(k6_partfun1(A_24))
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_310])).

tff(c_323,plain,(
    ! [A_24,A_72] : k9_relat_1(k6_partfun1(A_24),A_72) = k3_xboole_0(A_72,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54,c_52,c_288,c_319])).

tff(c_18,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [A_16] : k2_relat_1(k6_partfun1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_22,plain,(
    ! [A_17] : v4_relat_1(k6_relat_1(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_17] : v4_relat_1(k6_partfun1(A_17),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_199,plain,(
    ! [C_56,B_57,A_58] :
      ( v4_relat_1(C_56,B_57)
      | ~ v4_relat_1(C_56,A_58)
      | ~ v1_relat_1(C_56)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [A_17,B_57] :
      ( v4_relat_1(k6_partfun1(A_17),B_57)
      | ~ v1_relat_1(k6_partfun1(A_17))
      | ~ r1_tarski(A_17,B_57) ) ),
    inference(resolution,[status(thm)],[c_57,c_199])).

tff(c_205,plain,(
    ! [A_59,B_60] :
      ( v4_relat_1(k6_partfun1(A_59),B_60)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_201])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_210,plain,(
    ! [A_59,B_60] :
      ( k7_relat_1(k6_partfun1(A_59),B_60) = k6_partfun1(A_59)
      | ~ v1_relat_1(k6_partfun1(A_59))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_205,c_12])).

tff(c_217,plain,(
    ! [A_61,B_62] :
      ( k7_relat_1(k6_partfun1(A_61),B_62) = k6_partfun1(A_61)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_210])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [A_61,B_62] :
      ( k9_relat_1(k6_partfun1(A_61),B_62) = k2_relat_1(k6_partfun1(A_61))
      | ~ v1_relat_1(k6_partfun1(A_61))
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_8])).

tff(c_237,plain,(
    ! [A_61,B_62] :
      ( k9_relat_1(k6_partfun1(A_61),B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_59,c_227])).

tff(c_351,plain,(
    ! [B_76,A_77] :
      ( k3_xboole_0(B_76,A_77) = A_77
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_237])).

tff(c_359,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_149,c_351])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_364,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k8_relset_1(A_78,B_79,C_80,D_81) = k10_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_369,plain,(
    ! [A_29,D_81] : k8_relset_1(A_29,A_29,k6_partfun1(A_29),D_81) = k10_relat_1(k6_partfun1(A_29),D_81) ),
    inference(resolution,[status(thm)],[c_49,c_364])).

tff(c_372,plain,(
    ! [A_29,D_81] : k8_relset_1(A_29,A_29,k6_partfun1(A_29),D_81) = k3_xboole_0(D_81,A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_369])).

tff(c_46,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_406,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_46])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_2,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  
% 2.22/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.22/1.26  
% 2.22/1.26  %Foreground sorts:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Background operators:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Foreground operators:
% 2.22/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.22/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.26  
% 2.22/1.27  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.22/1.27  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.27  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.22/1.27  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.22/1.27  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.22/1.27  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.22/1.27  tff(f_85, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.22/1.27  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.22/1.27  tff(f_87, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 2.22/1.27  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.22/1.27  tff(f_67, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.22/1.27  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.22/1.27  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.22/1.27  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.22/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/1.27  tff(f_93, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.22/1.27  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.22/1.27  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.22/1.27  tff(c_137, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.27  tff(c_149, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_137])).
% 2.22/1.27  tff(c_44, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.22/1.27  tff(c_30, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.27  tff(c_53, plain, (![A_19]: (v1_relat_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_30])).
% 2.22/1.27  tff(c_28, plain, (![A_18]: (v1_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.27  tff(c_54, plain, (![A_18]: (v1_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 2.22/1.27  tff(c_32, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.27  tff(c_52, plain, (![A_19]: (v2_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32])).
% 2.22/1.27  tff(c_16, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.27  tff(c_60, plain, (![A_16]: (k1_relat_1(k6_partfun1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 2.22/1.27  tff(c_36, plain, (![B_23, A_22]: (k5_relat_1(k6_relat_1(B_23), k6_relat_1(A_22))=k6_relat_1(k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.22/1.27  tff(c_51, plain, (![B_23, A_22]: (k5_relat_1(k6_partfun1(B_23), k6_partfun1(A_22))=k6_partfun1(k3_xboole_0(A_22, B_23)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_44, c_36])).
% 2.22/1.27  tff(c_240, plain, (![A_63, B_64]: (k10_relat_1(A_63, k1_relat_1(B_64))=k1_relat_1(k5_relat_1(A_63, B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.27  tff(c_249, plain, (![A_63, A_16]: (k1_relat_1(k5_relat_1(A_63, k6_partfun1(A_16)))=k10_relat_1(A_63, A_16) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_60, c_240])).
% 2.22/1.27  tff(c_272, plain, (![A_67, A_68]: (k1_relat_1(k5_relat_1(A_67, k6_partfun1(A_68)))=k10_relat_1(A_67, A_68) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_249])).
% 2.22/1.27  tff(c_284, plain, (![A_22, B_23]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_22, B_23)))=k10_relat_1(k6_partfun1(B_23), A_22) | ~v1_relat_1(k6_partfun1(B_23)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_272])).
% 2.22/1.27  tff(c_288, plain, (![B_23, A_22]: (k10_relat_1(k6_partfun1(B_23), A_22)=k3_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_60, c_284])).
% 2.22/1.27  tff(c_38, plain, (![A_24]: (k2_funct_1(k6_relat_1(A_24))=k6_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.22/1.27  tff(c_50, plain, (![A_24]: (k2_funct_1(k6_partfun1(A_24))=k6_partfun1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_38])).
% 2.22/1.27  tff(c_310, plain, (![B_71, A_72]: (k9_relat_1(k2_funct_1(B_71), A_72)=k10_relat_1(B_71, A_72) | ~v2_funct_1(B_71) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.22/1.27  tff(c_319, plain, (![A_24, A_72]: (k9_relat_1(k6_partfun1(A_24), A_72)=k10_relat_1(k6_partfun1(A_24), A_72) | ~v2_funct_1(k6_partfun1(A_24)) | ~v1_funct_1(k6_partfun1(A_24)) | ~v1_relat_1(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_310])).
% 2.22/1.27  tff(c_323, plain, (![A_24, A_72]: (k9_relat_1(k6_partfun1(A_24), A_72)=k3_xboole_0(A_72, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_54, c_52, c_288, c_319])).
% 2.22/1.27  tff(c_18, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.27  tff(c_59, plain, (![A_16]: (k2_relat_1(k6_partfun1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 2.22/1.27  tff(c_22, plain, (![A_17]: (v4_relat_1(k6_relat_1(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.27  tff(c_57, plain, (![A_17]: (v4_relat_1(k6_partfun1(A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22])).
% 2.22/1.27  tff(c_199, plain, (![C_56, B_57, A_58]: (v4_relat_1(C_56, B_57) | ~v4_relat_1(C_56, A_58) | ~v1_relat_1(C_56) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.27  tff(c_201, plain, (![A_17, B_57]: (v4_relat_1(k6_partfun1(A_17), B_57) | ~v1_relat_1(k6_partfun1(A_17)) | ~r1_tarski(A_17, B_57))), inference(resolution, [status(thm)], [c_57, c_199])).
% 2.22/1.27  tff(c_205, plain, (![A_59, B_60]: (v4_relat_1(k6_partfun1(A_59), B_60) | ~r1_tarski(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_201])).
% 2.22/1.27  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.27  tff(c_210, plain, (![A_59, B_60]: (k7_relat_1(k6_partfun1(A_59), B_60)=k6_partfun1(A_59) | ~v1_relat_1(k6_partfun1(A_59)) | ~r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_205, c_12])).
% 2.22/1.27  tff(c_217, plain, (![A_61, B_62]: (k7_relat_1(k6_partfun1(A_61), B_62)=k6_partfun1(A_61) | ~r1_tarski(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_210])).
% 2.22/1.27  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.27  tff(c_227, plain, (![A_61, B_62]: (k9_relat_1(k6_partfun1(A_61), B_62)=k2_relat_1(k6_partfun1(A_61)) | ~v1_relat_1(k6_partfun1(A_61)) | ~r1_tarski(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_217, c_8])).
% 2.22/1.27  tff(c_237, plain, (![A_61, B_62]: (k9_relat_1(k6_partfun1(A_61), B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_59, c_227])).
% 2.22/1.27  tff(c_351, plain, (![B_76, A_77]: (k3_xboole_0(B_76, A_77)=A_77 | ~r1_tarski(A_77, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_237])).
% 2.22/1.27  tff(c_359, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_149, c_351])).
% 2.22/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.27  tff(c_42, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.22/1.27  tff(c_49, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 2.22/1.27  tff(c_364, plain, (![A_78, B_79, C_80, D_81]: (k8_relset_1(A_78, B_79, C_80, D_81)=k10_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.27  tff(c_369, plain, (![A_29, D_81]: (k8_relset_1(A_29, A_29, k6_partfun1(A_29), D_81)=k10_relat_1(k6_partfun1(A_29), D_81))), inference(resolution, [status(thm)], [c_49, c_364])).
% 2.22/1.27  tff(c_372, plain, (![A_29, D_81]: (k8_relset_1(A_29, A_29, k6_partfun1(A_29), D_81)=k3_xboole_0(D_81, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_369])).
% 2.22/1.27  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.22/1.27  tff(c_406, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_372, c_46])).
% 2.22/1.27  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_2, c_406])).
% 2.22/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  Inference rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Ref     : 0
% 2.22/1.27  #Sup     : 75
% 2.22/1.27  #Fact    : 0
% 2.22/1.27  #Define  : 0
% 2.22/1.27  #Split   : 0
% 2.22/1.27  #Chain   : 0
% 2.22/1.27  #Close   : 0
% 2.22/1.27  
% 2.22/1.27  Ordering : KBO
% 2.22/1.27  
% 2.22/1.27  Simplification rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Subsume      : 0
% 2.22/1.27  #Demod        : 43
% 2.22/1.27  #Tautology    : 57
% 2.22/1.27  #SimpNegUnit  : 0
% 2.22/1.27  #BackRed      : 2
% 2.22/1.27  
% 2.22/1.27  #Partial instantiations: 0
% 2.22/1.27  #Strategies tried      : 1
% 2.22/1.27  
% 2.22/1.27  Timing (in seconds)
% 2.22/1.27  ----------------------
% 2.22/1.28  Preprocessing        : 0.32
% 2.22/1.28  Parsing              : 0.17
% 2.22/1.28  CNF conversion       : 0.02
% 2.22/1.28  Main loop            : 0.20
% 2.22/1.28  Inferencing          : 0.08
% 2.22/1.28  Reduction            : 0.07
% 2.22/1.28  Demodulation         : 0.05
% 2.22/1.28  BG Simplification    : 0.02
% 2.22/1.28  Subsumption          : 0.02
% 2.22/1.28  Abstraction          : 0.01
% 2.22/1.28  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.28  Total                : 0.56
% 2.22/1.28  Index Insertion      : 0.00
% 2.22/1.28  Index Deletion       : 0.00
% 2.22/1.28  Index Matching       : 0.00
% 2.22/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
