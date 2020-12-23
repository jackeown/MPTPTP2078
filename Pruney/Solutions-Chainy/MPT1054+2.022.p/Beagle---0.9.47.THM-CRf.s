%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   43 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 100 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_76,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_120,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_310,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,C_77)
      | ~ r1_tarski(B_78,C_77)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_385,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_1')
      | ~ r1_tarski(A_82,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_132,c_310])).

tff(c_407,plain,(
    ! [B_6] : r1_tarski(k4_xboole_0('#skF_2',B_6),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_385])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,(
    ! [B_64,A_65] :
      ( ~ r1_xboole_0(B_64,A_65)
      | ~ r1_tarski(B_64,A_65)
      | v1_xboole_0(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1109,plain,(
    ! [A_129,B_130] :
      ( ~ r1_tarski(k4_xboole_0(A_129,B_130),B_130)
      | v1_xboole_0(k4_xboole_0(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_1150,plain,(
    v1_xboole_0(k4_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_407,c_1109])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1162,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1150,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1191,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_10])).

tff(c_1208,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1191])).

tff(c_42,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_23] : v1_relat_1(k6_partfun1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_26])).

tff(c_30,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49,plain,(
    ! [A_27] : k1_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30])).

tff(c_34,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_relat_1(B_29),k6_relat_1(A_28)) = k6_relat_1(k3_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_47,plain,(
    ! [B_29,A_28] : k5_relat_1(k6_partfun1(B_29),k6_partfun1(A_28)) = k6_partfun1(k3_xboole_0(A_28,B_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_42,c_34])).

tff(c_844,plain,(
    ! [A_109,B_110] :
      ( k10_relat_1(A_109,k1_relat_1(B_110)) = k1_relat_1(k5_relat_1(A_109,B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_853,plain,(
    ! [A_109,A_27] :
      ( k1_relat_1(k5_relat_1(A_109,k6_partfun1(A_27))) = k10_relat_1(A_109,A_27)
      | ~ v1_relat_1(k6_partfun1(A_27))
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_844])).

tff(c_2320,plain,(
    ! [A_161,A_162] :
      ( k1_relat_1(k5_relat_1(A_161,k6_partfun1(A_162))) = k10_relat_1(A_161,A_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_853])).

tff(c_2332,plain,(
    ! [A_28,B_29] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_28,B_29))) = k10_relat_1(k6_partfun1(B_29),A_28)
      | ~ v1_relat_1(k6_partfun1(B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_2320])).

tff(c_2336,plain,(
    ! [B_29,A_28] : k10_relat_1(k6_partfun1(B_29),A_28) = k3_xboole_0(A_28,B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49,c_2332])).

tff(c_40,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_988,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k8_relset_1(A_120,B_121,C_122,D_123) = k10_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_995,plain,(
    ! [A_34,D_123] : k8_relset_1(A_34,A_34,k6_partfun1(A_34),D_123) = k10_relat_1(k6_partfun1(A_34),D_123) ),
    inference(resolution,[status(thm)],[c_40,c_988])).

tff(c_44,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1928,plain,(
    k10_relat_1(k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_44])).

tff(c_2337,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2336,c_1928])).

tff(c_2341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_2337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.62  
% 3.14/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.62  %$ v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.14/1.62  
% 3.14/1.62  %Foreground sorts:
% 3.14/1.62  
% 3.14/1.62  
% 3.14/1.62  %Background operators:
% 3.14/1.62  
% 3.14/1.62  
% 3.14/1.62  %Foreground operators:
% 3.14/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.14/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.14/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.14/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.62  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.14/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.14/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.14/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.62  
% 3.55/1.64  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.55/1.64  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.55/1.64  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 3.55/1.64  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.55/1.64  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.55/1.64  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.55/1.64  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.55/1.64  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.55/1.64  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.55/1.64  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.55/1.64  tff(f_63, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.55/1.64  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.55/1.64  tff(f_76, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.55/1.64  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.55/1.64  tff(f_84, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.55/1.64  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.55/1.64  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.64  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.64  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.55/1.64  tff(c_120, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.64  tff(c_132, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_120])).
% 3.55/1.64  tff(c_310, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, C_77) | ~r1_tarski(B_78, C_77) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.64  tff(c_385, plain, (![A_82]: (r1_tarski(A_82, '#skF_1') | ~r1_tarski(A_82, '#skF_2'))), inference(resolution, [status(thm)], [c_132, c_310])).
% 3.55/1.64  tff(c_407, plain, (![B_6]: (r1_tarski(k4_xboole_0('#skF_2', B_6), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_385])).
% 3.55/1.64  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.64  tff(c_195, plain, (![B_64, A_65]: (~r1_xboole_0(B_64, A_65) | ~r1_tarski(B_64, A_65) | v1_xboole_0(B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.64  tff(c_1109, plain, (![A_129, B_130]: (~r1_tarski(k4_xboole_0(A_129, B_130), B_130) | v1_xboole_0(k4_xboole_0(A_129, B_130)))), inference(resolution, [status(thm)], [c_14, c_195])).
% 3.55/1.64  tff(c_1150, plain, (v1_xboole_0(k4_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_407, c_1109])).
% 3.55/1.64  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.64  tff(c_1162, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1150, c_2])).
% 3.55/1.64  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.55/1.64  tff(c_1191, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1162, c_10])).
% 3.55/1.64  tff(c_1208, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1191])).
% 3.55/1.64  tff(c_42, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.55/1.64  tff(c_26, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.55/1.64  tff(c_50, plain, (![A_23]: (v1_relat_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_26])).
% 3.55/1.64  tff(c_30, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.55/1.64  tff(c_49, plain, (![A_27]: (k1_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30])).
% 3.55/1.64  tff(c_34, plain, (![B_29, A_28]: (k5_relat_1(k6_relat_1(B_29), k6_relat_1(A_28))=k6_relat_1(k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.55/1.64  tff(c_47, plain, (![B_29, A_28]: (k5_relat_1(k6_partfun1(B_29), k6_partfun1(A_28))=k6_partfun1(k3_xboole_0(A_28, B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_42, c_34])).
% 3.55/1.64  tff(c_844, plain, (![A_109, B_110]: (k10_relat_1(A_109, k1_relat_1(B_110))=k1_relat_1(k5_relat_1(A_109, B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.55/1.64  tff(c_853, plain, (![A_109, A_27]: (k1_relat_1(k5_relat_1(A_109, k6_partfun1(A_27)))=k10_relat_1(A_109, A_27) | ~v1_relat_1(k6_partfun1(A_27)) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_49, c_844])).
% 3.55/1.64  tff(c_2320, plain, (![A_161, A_162]: (k1_relat_1(k5_relat_1(A_161, k6_partfun1(A_162)))=k10_relat_1(A_161, A_162) | ~v1_relat_1(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_853])).
% 3.55/1.64  tff(c_2332, plain, (![A_28, B_29]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_28, B_29)))=k10_relat_1(k6_partfun1(B_29), A_28) | ~v1_relat_1(k6_partfun1(B_29)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_2320])).
% 3.55/1.64  tff(c_2336, plain, (![B_29, A_28]: (k10_relat_1(k6_partfun1(B_29), A_28)=k3_xboole_0(A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_49, c_2332])).
% 3.55/1.64  tff(c_40, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.55/1.64  tff(c_988, plain, (![A_120, B_121, C_122, D_123]: (k8_relset_1(A_120, B_121, C_122, D_123)=k10_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.64  tff(c_995, plain, (![A_34, D_123]: (k8_relset_1(A_34, A_34, k6_partfun1(A_34), D_123)=k10_relat_1(k6_partfun1(A_34), D_123))), inference(resolution, [status(thm)], [c_40, c_988])).
% 3.55/1.64  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.55/1.64  tff(c_1928, plain, (k10_relat_1(k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_995, c_44])).
% 3.55/1.64  tff(c_2337, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2336, c_1928])).
% 3.55/1.64  tff(c_2341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1208, c_2337])).
% 3.55/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.64  
% 3.55/1.64  Inference rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Ref     : 0
% 3.55/1.64  #Sup     : 528
% 3.55/1.64  #Fact    : 0
% 3.55/1.64  #Define  : 0
% 3.55/1.64  #Split   : 0
% 3.55/1.64  #Chain   : 0
% 3.55/1.64  #Close   : 0
% 3.55/1.64  
% 3.55/1.64  Ordering : KBO
% 3.55/1.64  
% 3.55/1.64  Simplification rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Subsume      : 36
% 3.55/1.64  #Demod        : 491
% 3.55/1.64  #Tautology    : 391
% 3.55/1.64  #SimpNegUnit  : 0
% 3.55/1.64  #BackRed      : 13
% 3.55/1.64  
% 3.55/1.64  #Partial instantiations: 0
% 3.55/1.64  #Strategies tried      : 1
% 3.55/1.64  
% 3.55/1.64  Timing (in seconds)
% 3.55/1.64  ----------------------
% 3.55/1.64  Preprocessing        : 0.32
% 3.55/1.64  Parsing              : 0.18
% 3.55/1.64  CNF conversion       : 0.02
% 3.55/1.64  Main loop            : 0.50
% 3.55/1.64  Inferencing          : 0.17
% 3.55/1.64  Reduction            : 0.19
% 3.55/1.64  Demodulation         : 0.15
% 3.55/1.64  BG Simplification    : 0.02
% 3.55/1.64  Subsumption          : 0.08
% 3.55/1.64  Abstraction          : 0.03
% 3.55/1.64  MUC search           : 0.00
% 3.55/1.64  Cooper               : 0.00
% 3.55/1.64  Total                : 0.85
% 3.55/1.64  Index Insertion      : 0.00
% 3.55/1.64  Index Deletion       : 0.00
% 3.55/1.64  Index Matching       : 0.00
% 3.55/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
