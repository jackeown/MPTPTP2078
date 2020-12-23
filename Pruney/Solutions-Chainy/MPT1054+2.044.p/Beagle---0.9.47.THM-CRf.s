%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:17 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 127 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_76,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_111,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_111])).

tff(c_40,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49,plain,(
    ! [A_18] : v1_relat_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24])).

tff(c_22,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ! [A_17] : v1_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_22])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [B_24,A_23] : k5_relat_1(k6_relat_1(B_24),k6_relat_1(A_23)) = k6_relat_1(k3_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    ! [B_24,A_23] : k5_relat_1(k6_partfun1(B_24),k6_partfun1(A_23)) = k6_partfun1(k3_xboole_0(A_23,B_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_40,c_32])).

tff(c_177,plain,(
    ! [B_59,C_60,A_61] :
      ( k10_relat_1(k5_relat_1(B_59,C_60),A_61) = k10_relat_1(B_59,k10_relat_1(C_60,A_61))
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    ! [B_24,A_23,A_61] :
      ( k10_relat_1(k6_partfun1(B_24),k10_relat_1(k6_partfun1(A_23),A_61)) = k10_relat_1(k6_partfun1(k3_xboole_0(A_23,B_24)),A_61)
      | ~ v1_relat_1(k6_partfun1(A_23))
      | ~ v1_relat_1(k6_partfun1(B_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_177])).

tff(c_190,plain,(
    ! [B_24,A_23,A_61] : k10_relat_1(k6_partfun1(B_24),k10_relat_1(k6_partfun1(A_23),A_61)) = k10_relat_1(k6_partfun1(k3_xboole_0(A_23,B_24)),A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_49,c_186])).

tff(c_26,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26])).

tff(c_34,plain,(
    ! [A_25] : k2_funct_1(k6_relat_1(A_25)) = k6_relat_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    ! [A_25] : k2_funct_1(k6_partfun1(A_25)) = k6_partfun1(A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_34])).

tff(c_154,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(k2_funct_1(B_55),A_56) = k10_relat_1(B_55,A_56)
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_163,plain,(
    ! [A_25,A_56] :
      ( k9_relat_1(k6_partfun1(A_25),A_56) = k10_relat_1(k6_partfun1(A_25),A_56)
      | ~ v2_funct_1(k6_partfun1(A_25))
      | ~ v1_funct_1(k6_partfun1(A_25))
      | ~ v1_relat_1(k6_partfun1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_154])).

tff(c_167,plain,(
    ! [A_25,A_56] : k9_relat_1(k6_partfun1(A_25),A_56) = k10_relat_1(k6_partfun1(A_25),A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_50,c_48,c_163])).

tff(c_18,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ! [A_16] : k2_relat_1(k6_partfun1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_208,plain,(
    ! [B_65,A_66] :
      ( k9_relat_1(B_65,k10_relat_1(B_65,A_66)) = A_66
      | ~ r1_tarski(A_66,k2_relat_1(B_65))
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_210,plain,(
    ! [A_16,A_66] :
      ( k9_relat_1(k6_partfun1(A_16),k10_relat_1(k6_partfun1(A_16),A_66)) = A_66
      | ~ r1_tarski(A_66,A_16)
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k6_partfun1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_208])).

tff(c_212,plain,(
    ! [A_16,A_66] :
      ( k10_relat_1(k6_partfun1(A_16),A_66) = A_66
      | ~ r1_tarski(A_66,A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_50,c_2,c_190,c_167,c_210])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(k6_relat_1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_45,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_232,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    ! [A_30,D_72] : k8_relset_1(A_30,A_30,k6_partfun1(A_30),D_72) = k10_relat_1(k6_partfun1(A_30),D_72) ),
    inference(resolution,[status(thm)],[c_45,c_232])).

tff(c_42,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_240,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_42])).

tff(c_252,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_240])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.19/1.26  
% 2.19/1.26  %Foreground sorts:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Background operators:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Foreground operators:
% 2.19/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.19/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.19/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.19/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.19/1.26  
% 2.19/1.27  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 2.19/1.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.27  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.19/1.27  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.19/1.27  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.19/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.19/1.27  tff(f_74, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.19/1.27  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.19/1.27  tff(f_76, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.19/1.27  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.19/1.27  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.19/1.27  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.19/1.27  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.19/1.27  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.19/1.27  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.27  tff(c_111, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.27  tff(c_115, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_111])).
% 2.19/1.27  tff(c_40, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/1.27  tff(c_24, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.27  tff(c_49, plain, (![A_18]: (v1_relat_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24])).
% 2.19/1.27  tff(c_22, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.27  tff(c_50, plain, (![A_17]: (v1_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_22])).
% 2.19/1.27  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.27  tff(c_32, plain, (![B_24, A_23]: (k5_relat_1(k6_relat_1(B_24), k6_relat_1(A_23))=k6_relat_1(k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.27  tff(c_47, plain, (![B_24, A_23]: (k5_relat_1(k6_partfun1(B_24), k6_partfun1(A_23))=k6_partfun1(k3_xboole_0(A_23, B_24)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_40, c_32])).
% 2.19/1.27  tff(c_177, plain, (![B_59, C_60, A_61]: (k10_relat_1(k5_relat_1(B_59, C_60), A_61)=k10_relat_1(B_59, k10_relat_1(C_60, A_61)) | ~v1_relat_1(C_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.27  tff(c_186, plain, (![B_24, A_23, A_61]: (k10_relat_1(k6_partfun1(B_24), k10_relat_1(k6_partfun1(A_23), A_61))=k10_relat_1(k6_partfun1(k3_xboole_0(A_23, B_24)), A_61) | ~v1_relat_1(k6_partfun1(A_23)) | ~v1_relat_1(k6_partfun1(B_24)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_177])).
% 2.19/1.27  tff(c_190, plain, (![B_24, A_23, A_61]: (k10_relat_1(k6_partfun1(B_24), k10_relat_1(k6_partfun1(A_23), A_61))=k10_relat_1(k6_partfun1(k3_xboole_0(A_23, B_24)), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_49, c_186])).
% 2.19/1.27  tff(c_26, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.27  tff(c_48, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26])).
% 2.19/1.27  tff(c_34, plain, (![A_25]: (k2_funct_1(k6_relat_1(A_25))=k6_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.27  tff(c_46, plain, (![A_25]: (k2_funct_1(k6_partfun1(A_25))=k6_partfun1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_34])).
% 2.19/1.27  tff(c_154, plain, (![B_55, A_56]: (k9_relat_1(k2_funct_1(B_55), A_56)=k10_relat_1(B_55, A_56) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.27  tff(c_163, plain, (![A_25, A_56]: (k9_relat_1(k6_partfun1(A_25), A_56)=k10_relat_1(k6_partfun1(A_25), A_56) | ~v2_funct_1(k6_partfun1(A_25)) | ~v1_funct_1(k6_partfun1(A_25)) | ~v1_relat_1(k6_partfun1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_154])).
% 2.19/1.27  tff(c_167, plain, (![A_25, A_56]: (k9_relat_1(k6_partfun1(A_25), A_56)=k10_relat_1(k6_partfun1(A_25), A_56))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_50, c_48, c_163])).
% 2.19/1.27  tff(c_18, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.27  tff(c_52, plain, (![A_16]: (k2_relat_1(k6_partfun1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 2.19/1.27  tff(c_208, plain, (![B_65, A_66]: (k9_relat_1(B_65, k10_relat_1(B_65, A_66))=A_66 | ~r1_tarski(A_66, k2_relat_1(B_65)) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.27  tff(c_210, plain, (![A_16, A_66]: (k9_relat_1(k6_partfun1(A_16), k10_relat_1(k6_partfun1(A_16), A_66))=A_66 | ~r1_tarski(A_66, A_16) | ~v1_funct_1(k6_partfun1(A_16)) | ~v1_relat_1(k6_partfun1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_208])).
% 2.19/1.27  tff(c_212, plain, (![A_16, A_66]: (k10_relat_1(k6_partfun1(A_16), A_66)=A_66 | ~r1_tarski(A_66, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_50, c_2, c_190, c_167, c_210])).
% 2.19/1.27  tff(c_38, plain, (![A_30]: (m1_subset_1(k6_relat_1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.27  tff(c_45, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 2.19/1.27  tff(c_232, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_239, plain, (![A_30, D_72]: (k8_relset_1(A_30, A_30, k6_partfun1(A_30), D_72)=k10_relat_1(k6_partfun1(A_30), D_72))), inference(resolution, [status(thm)], [c_45, c_232])).
% 2.19/1.27  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.27  tff(c_240, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_42])).
% 2.19/1.27  tff(c_252, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_212, c_240])).
% 2.19/1.27  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_252])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 44
% 2.19/1.27  #Fact    : 0
% 2.19/1.27  #Define  : 0
% 2.19/1.27  #Split   : 0
% 2.19/1.27  #Chain   : 0
% 2.19/1.27  #Close   : 0
% 2.19/1.27  
% 2.19/1.27  Ordering : KBO
% 2.19/1.27  
% 2.19/1.27  Simplification rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Subsume      : 0
% 2.19/1.27  #Demod        : 29
% 2.19/1.27  #Tautology    : 32
% 2.19/1.27  #SimpNegUnit  : 0
% 2.19/1.27  #BackRed      : 1
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.27  Preprocessing        : 0.33
% 2.19/1.27  Parsing              : 0.18
% 2.19/1.27  CNF conversion       : 0.02
% 2.19/1.27  Main loop            : 0.18
% 2.19/1.27  Inferencing          : 0.08
% 2.19/1.27  Reduction            : 0.06
% 2.19/1.27  Demodulation         : 0.05
% 2.19/1.27  BG Simplification    : 0.02
% 2.19/1.27  Subsumption          : 0.02
% 2.19/1.27  Abstraction          : 0.01
% 2.19/1.27  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.55
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
