%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:16 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 101 expanded)
%              Number of leaves         :   43 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 102 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_63,axiom,(
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

tff(f_65,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_82,axiom,(
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

tff(c_119,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_127,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_246,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_445,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,'#skF_1')
      | ~ r1_tarski(A_86,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_127,c_246])).

tff(c_467,plain,(
    ! [B_6] : r1_tarski(k4_xboole_0('#skF_2',B_6),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_445])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    ! [B_62,A_63] :
      ( ~ r1_xboole_0(B_62,A_63)
      | ~ r1_tarski(B_62,A_63)
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1076,plain,(
    ! [A_129,B_130] :
      ( ~ r1_tarski(k4_xboole_0(A_129,B_130),B_130)
      | v1_xboole_0(k4_xboole_0(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_1117,plain,(
    v1_xboole_0(k4_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_467,c_1076])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1143,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1117,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1172,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_10])).

tff(c_1189,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1172])).

tff(c_42,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    ! [A_27] : v1_relat_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_32,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_31] : k1_relat_1(k6_partfun1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_36,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_relat_1(B_33),k6_relat_1(A_32)) = k6_relat_1(k3_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_partfun1(B_33),k6_partfun1(A_32)) = k6_partfun1(k3_xboole_0(A_32,B_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_42,c_36])).

tff(c_1126,plain,(
    ! [A_131,B_132] :
      ( k10_relat_1(A_131,k1_relat_1(B_132)) = k1_relat_1(k5_relat_1(A_131,B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1135,plain,(
    ! [A_131,A_31] :
      ( k1_relat_1(k5_relat_1(A_131,k6_partfun1(A_31))) = k10_relat_1(A_131,A_31)
      | ~ v1_relat_1(k6_partfun1(A_31))
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1126])).

tff(c_1864,plain,(
    ! [A_156,A_157] :
      ( k1_relat_1(k5_relat_1(A_156,k6_partfun1(A_157))) = k10_relat_1(A_156,A_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1135])).

tff(c_1876,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k6_partfun1(k3_xboole_0(A_32,B_33))) = k10_relat_1(k6_partfun1(B_33),A_32)
      | ~ v1_relat_1(k6_partfun1(B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1864])).

tff(c_1880,plain,(
    ! [B_33,A_32] : k10_relat_1(k6_partfun1(B_33),A_32) = k3_xboole_0(A_32,B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_1876])).

tff(c_40,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_1469,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1475,plain,(
    ! [A_38,D_145] : k8_relset_1(A_38,A_38,k6_partfun1(A_38),D_145) = k10_relat_1(k6_partfun1(A_38),D_145) ),
    inference(resolution,[status(thm)],[c_47,c_1469])).

tff(c_4080,plain,(
    ! [A_38,D_145] : k8_relset_1(A_38,A_38,k6_partfun1(A_38),D_145) = k3_xboole_0(D_145,A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1880,c_1475])).

tff(c_44,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4081,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4080,c_44])).

tff(c_4084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_4081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.54  
% 5.41/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.54  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.41/2.54  
% 5.41/2.54  %Foreground sorts:
% 5.41/2.54  
% 5.41/2.54  
% 5.41/2.54  %Background operators:
% 5.41/2.54  
% 5.41/2.54  
% 5.41/2.54  %Foreground operators:
% 5.41/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.41/2.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.41/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/2.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.41/2.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.41/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.41/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.41/2.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.41/2.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.41/2.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.41/2.54  tff('#skF_2', type, '#skF_2': $i).
% 5.41/2.54  tff('#skF_1', type, '#skF_1': $i).
% 5.41/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.41/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.41/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.41/2.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.41/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.41/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.41/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.41/2.54  
% 5.74/2.56  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.74/2.56  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.74/2.56  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 5.74/2.56  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.74/2.56  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.74/2.56  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.74/2.56  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.74/2.56  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.74/2.56  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.74/2.56  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.74/2.56  tff(f_65, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.74/2.56  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.74/2.56  tff(f_78, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.74/2.56  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.74/2.56  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.74/2.56  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.74/2.56  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.56  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.56  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.56  tff(c_119, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.74/2.56  tff(c_127, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_119])).
% 5.74/2.56  tff(c_246, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.74/2.56  tff(c_445, plain, (![A_86]: (r1_tarski(A_86, '#skF_1') | ~r1_tarski(A_86, '#skF_2'))), inference(resolution, [status(thm)], [c_127, c_246])).
% 5.74/2.56  tff(c_467, plain, (![B_6]: (r1_tarski(k4_xboole_0('#skF_2', B_6), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_445])).
% 5.74/2.56  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.74/2.56  tff(c_134, plain, (![B_62, A_63]: (~r1_xboole_0(B_62, A_63) | ~r1_tarski(B_62, A_63) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.74/2.56  tff(c_1076, plain, (![A_129, B_130]: (~r1_tarski(k4_xboole_0(A_129, B_130), B_130) | v1_xboole_0(k4_xboole_0(A_129, B_130)))), inference(resolution, [status(thm)], [c_14, c_134])).
% 5.74/2.56  tff(c_1117, plain, (v1_xboole_0(k4_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_467, c_1076])).
% 5.74/2.56  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.74/2.56  tff(c_1143, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1117, c_2])).
% 5.74/2.56  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.56  tff(c_1172, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_10])).
% 5.74/2.56  tff(c_1189, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1172])).
% 5.74/2.56  tff(c_42, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.74/2.56  tff(c_28, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.74/2.56  tff(c_51, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28])).
% 5.74/2.56  tff(c_32, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.74/2.56  tff(c_50, plain, (![A_31]: (k1_relat_1(k6_partfun1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 5.74/2.56  tff(c_36, plain, (![B_33, A_32]: (k5_relat_1(k6_relat_1(B_33), k6_relat_1(A_32))=k6_relat_1(k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.74/2.56  tff(c_48, plain, (![B_33, A_32]: (k5_relat_1(k6_partfun1(B_33), k6_partfun1(A_32))=k6_partfun1(k3_xboole_0(A_32, B_33)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_42, c_36])).
% 5.74/2.56  tff(c_1126, plain, (![A_131, B_132]: (k10_relat_1(A_131, k1_relat_1(B_132))=k1_relat_1(k5_relat_1(A_131, B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.74/2.56  tff(c_1135, plain, (![A_131, A_31]: (k1_relat_1(k5_relat_1(A_131, k6_partfun1(A_31)))=k10_relat_1(A_131, A_31) | ~v1_relat_1(k6_partfun1(A_31)) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1126])).
% 5.74/2.56  tff(c_1864, plain, (![A_156, A_157]: (k1_relat_1(k5_relat_1(A_156, k6_partfun1(A_157)))=k10_relat_1(A_156, A_157) | ~v1_relat_1(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_1135])).
% 5.74/2.56  tff(c_1876, plain, (![A_32, B_33]: (k1_relat_1(k6_partfun1(k3_xboole_0(A_32, B_33)))=k10_relat_1(k6_partfun1(B_33), A_32) | ~v1_relat_1(k6_partfun1(B_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1864])).
% 5.74/2.56  tff(c_1880, plain, (![B_33, A_32]: (k10_relat_1(k6_partfun1(B_33), A_32)=k3_xboole_0(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_1876])).
% 5.74/2.56  tff(c_40, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.74/2.56  tff(c_47, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 5.74/2.56  tff(c_1469, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.74/2.56  tff(c_1475, plain, (![A_38, D_145]: (k8_relset_1(A_38, A_38, k6_partfun1(A_38), D_145)=k10_relat_1(k6_partfun1(A_38), D_145))), inference(resolution, [status(thm)], [c_47, c_1469])).
% 5.74/2.56  tff(c_4080, plain, (![A_38, D_145]: (k8_relset_1(A_38, A_38, k6_partfun1(A_38), D_145)=k3_xboole_0(D_145, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_1880, c_1475])).
% 5.74/2.56  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.74/2.56  tff(c_4081, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4080, c_44])).
% 5.74/2.56  tff(c_4084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1189, c_4081])).
% 5.74/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.56  
% 5.74/2.56  Inference rules
% 5.74/2.56  ----------------------
% 5.74/2.56  #Ref     : 0
% 5.74/2.56  #Sup     : 942
% 5.74/2.56  #Fact    : 0
% 5.74/2.56  #Define  : 0
% 5.74/2.56  #Split   : 0
% 5.74/2.56  #Chain   : 0
% 5.74/2.56  #Close   : 0
% 5.74/2.56  
% 5.74/2.56  Ordering : KBO
% 5.74/2.56  
% 5.74/2.56  Simplification rules
% 5.74/2.56  ----------------------
% 5.74/2.56  #Subsume      : 42
% 5.74/2.57  #Demod        : 1113
% 5.74/2.57  #Tautology    : 737
% 5.74/2.57  #SimpNegUnit  : 0
% 5.74/2.57  #BackRed      : 16
% 5.74/2.57  
% 5.74/2.57  #Partial instantiations: 0
% 5.74/2.57  #Strategies tried      : 1
% 5.74/2.57  
% 5.74/2.57  Timing (in seconds)
% 5.74/2.57  ----------------------
% 5.74/2.57  Preprocessing        : 0.51
% 5.74/2.57  Parsing              : 0.27
% 5.74/2.57  CNF conversion       : 0.03
% 5.74/2.57  Main loop            : 1.12
% 5.74/2.57  Inferencing          : 0.38
% 5.74/2.57  Reduction            : 0.46
% 5.74/2.57  Demodulation         : 0.37
% 5.74/2.57  BG Simplification    : 0.04
% 5.74/2.57  Subsumption          : 0.17
% 5.74/2.57  Abstraction          : 0.06
% 5.74/2.57  MUC search           : 0.00
% 5.74/2.57  Cooper               : 0.00
% 5.74/2.57  Total                : 1.68
% 5.74/2.57  Index Insertion      : 0.00
% 5.74/2.57  Index Deletion       : 0.00
% 5.74/2.57  Index Matching       : 0.00
% 5.74/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
