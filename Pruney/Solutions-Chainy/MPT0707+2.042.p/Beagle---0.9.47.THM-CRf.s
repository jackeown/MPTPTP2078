%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 138 expanded)
%              Number of leaves         :   37 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 195 expanded)
%              Number of equality atoms :   37 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_81,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_83,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_30,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [B_42,A_43] :
      ( k5_relat_1(B_42,k6_relat_1(A_43)) = k8_relat_1(A_43,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [B_23,A_22] : k5_relat_1(k6_relat_1(B_23),k6_relat_1(A_22)) = k6_relat_1(k3_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,(
    ! [A_43,B_23] :
      ( k8_relat_1(A_43,k6_relat_1(B_23)) = k6_relat_1(k3_xboole_0(A_43,B_23))
      | ~ v1_relat_1(k6_relat_1(B_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_38])).

tff(c_132,plain,(
    ! [A_43,B_23] : k8_relat_1(A_43,k6_relat_1(B_23)) = k6_relat_1(k3_xboole_0(A_43,B_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_146,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_8,A_46] :
      ( k8_relat_1(A_8,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_8),A_46)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_10])).

tff(c_178,plain,(
    ! [A_48,A_49] : k7_relat_1(k6_relat_1(A_48),A_49) = k6_relat_1(k3_xboole_0(A_48,A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_132,c_153])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [A_48,A_49] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_48,A_49))) = k9_relat_1(k6_relat_1(A_48),A_49)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_12])).

tff(c_190,plain,(
    ! [A_48,A_49] : k9_relat_1(k6_relat_1(A_48),A_49) = k3_xboole_0(A_48,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16,c_184])).

tff(c_42,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_192,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_42])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_89,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_28,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_52,B_53,C_54] : k3_xboole_0(k3_xboole_0(A_52,B_53),C_54) = k3_xboole_0(A_52,k3_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    ! [A_1,C_54] : k3_xboole_0(A_1,k3_xboole_0(A_1,C_54)) = k3_xboole_0(A_1,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_32,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_24] : k2_funct_1(k6_relat_1(A_24)) = k6_relat_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_338,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(k2_funct_1(B_59),A_60) = k10_relat_1(B_59,A_60)
      | ~ v2_funct_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_347,plain,(
    ! [A_24,A_60] :
      ( k9_relat_1(k6_relat_1(A_24),A_60) = k10_relat_1(k6_relat_1(A_24),A_60)
      | ~ v2_funct_1(k6_relat_1(A_24))
      | ~ v1_funct_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_338])).

tff(c_351,plain,(
    ! [A_24,A_60] : k10_relat_1(k6_relat_1(A_24),A_60) = k3_xboole_0(A_24,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_32,c_190,c_347])).

tff(c_362,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(B_63,k10_relat_1(B_63,A_64)) = A_64
      | ~ r1_tarski(A_64,k2_relat_1(B_63))
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_366,plain,(
    ! [A_12,A_64] :
      ( k9_relat_1(k6_relat_1(A_12),k10_relat_1(k6_relat_1(A_12),A_64)) = A_64
      | ~ r1_tarski(A_64,A_12)
      | ~ v1_funct_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_362])).

tff(c_369,plain,(
    ! [A_65,A_66] :
      ( k3_xboole_0(A_65,A_66) = A_66
      | ~ r1_tarski(A_66,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_223,c_351,c_190,c_366])).

tff(c_372,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_369])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:21:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.26  
% 2.25/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.25/1.27  
% 2.25/1.27  %Foreground sorts:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Background operators:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Foreground operators:
% 2.25/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.25/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.25/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.25/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.27  
% 2.25/1.28  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.25/1.28  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.25/1.28  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.25/1.28  tff(f_81, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.25/1.28  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.25/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.25/1.28  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.25/1.28  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.28  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.25/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.25/1.28  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.25/1.28  tff(f_83, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.25/1.28  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 2.25/1.28  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.25/1.28  tff(c_30, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.25/1.28  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.28  tff(c_116, plain, (![B_42, A_43]: (k5_relat_1(B_42, k6_relat_1(A_43))=k8_relat_1(A_43, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.28  tff(c_38, plain, (![B_23, A_22]: (k5_relat_1(k6_relat_1(B_23), k6_relat_1(A_22))=k6_relat_1(k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.28  tff(c_123, plain, (![A_43, B_23]: (k8_relat_1(A_43, k6_relat_1(B_23))=k6_relat_1(k3_xboole_0(A_43, B_23)) | ~v1_relat_1(k6_relat_1(B_23)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_38])).
% 2.25/1.28  tff(c_132, plain, (![A_43, B_23]: (k8_relat_1(A_43, k6_relat_1(B_23))=k6_relat_1(k3_xboole_0(A_43, B_23)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_123])).
% 2.25/1.28  tff(c_146, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.28  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.28  tff(c_153, plain, (![A_8, A_46]: (k8_relat_1(A_8, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_8), A_46) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_10])).
% 2.25/1.28  tff(c_178, plain, (![A_48, A_49]: (k7_relat_1(k6_relat_1(A_48), A_49)=k6_relat_1(k3_xboole_0(A_48, A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_132, c_153])).
% 2.25/1.28  tff(c_12, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.28  tff(c_184, plain, (![A_48, A_49]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_48, A_49)))=k9_relat_1(k6_relat_1(A_48), A_49) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_12])).
% 2.25/1.28  tff(c_190, plain, (![A_48, A_49]: (k9_relat_1(k6_relat_1(A_48), A_49)=k3_xboole_0(A_48, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16, c_184])).
% 2.25/1.28  tff(c_42, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.25/1.28  tff(c_192, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_42])).
% 2.25/1.28  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.25/1.28  tff(c_89, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.28  tff(c_97, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_89])).
% 2.25/1.28  tff(c_28, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.28  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.28  tff(c_204, plain, (![A_52, B_53, C_54]: (k3_xboole_0(k3_xboole_0(A_52, B_53), C_54)=k3_xboole_0(A_52, k3_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.28  tff(c_223, plain, (![A_1, C_54]: (k3_xboole_0(A_1, k3_xboole_0(A_1, C_54))=k3_xboole_0(A_1, C_54))), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 2.25/1.28  tff(c_32, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.25/1.28  tff(c_40, plain, (![A_24]: (k2_funct_1(k6_relat_1(A_24))=k6_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.25/1.28  tff(c_338, plain, (![B_59, A_60]: (k9_relat_1(k2_funct_1(B_59), A_60)=k10_relat_1(B_59, A_60) | ~v2_funct_1(B_59) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.25/1.28  tff(c_347, plain, (![A_24, A_60]: (k9_relat_1(k6_relat_1(A_24), A_60)=k10_relat_1(k6_relat_1(A_24), A_60) | ~v2_funct_1(k6_relat_1(A_24)) | ~v1_funct_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_338])).
% 2.25/1.28  tff(c_351, plain, (![A_24, A_60]: (k10_relat_1(k6_relat_1(A_24), A_60)=k3_xboole_0(A_24, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_32, c_190, c_347])).
% 2.25/1.28  tff(c_362, plain, (![B_63, A_64]: (k9_relat_1(B_63, k10_relat_1(B_63, A_64))=A_64 | ~r1_tarski(A_64, k2_relat_1(B_63)) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.28  tff(c_366, plain, (![A_12, A_64]: (k9_relat_1(k6_relat_1(A_12), k10_relat_1(k6_relat_1(A_12), A_64))=A_64 | ~r1_tarski(A_64, A_12) | ~v1_funct_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_362])).
% 2.25/1.28  tff(c_369, plain, (![A_65, A_66]: (k3_xboole_0(A_65, A_66)=A_66 | ~r1_tarski(A_66, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_223, c_351, c_190, c_366])).
% 2.25/1.28  tff(c_372, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_97, c_369])).
% 2.25/1.28  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_372])).
% 2.25/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  Inference rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Ref     : 0
% 2.25/1.28  #Sup     : 70
% 2.25/1.28  #Fact    : 0
% 2.25/1.28  #Define  : 0
% 2.25/1.28  #Split   : 0
% 2.25/1.28  #Chain   : 0
% 2.25/1.28  #Close   : 0
% 2.25/1.28  
% 2.25/1.28  Ordering : KBO
% 2.25/1.28  
% 2.25/1.28  Simplification rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Subsume      : 0
% 2.25/1.28  #Demod        : 68
% 2.25/1.28  #Tautology    : 54
% 2.25/1.28  #SimpNegUnit  : 1
% 2.25/1.28  #BackRed      : 1
% 2.25/1.28  
% 2.25/1.28  #Partial instantiations: 0
% 2.25/1.28  #Strategies tried      : 1
% 2.25/1.28  
% 2.25/1.28  Timing (in seconds)
% 2.25/1.28  ----------------------
% 2.25/1.29  Preprocessing        : 0.31
% 2.25/1.29  Parsing              : 0.18
% 2.25/1.29  CNF conversion       : 0.02
% 2.25/1.29  Main loop            : 0.24
% 2.25/1.29  Inferencing          : 0.10
% 2.25/1.29  Reduction            : 0.09
% 2.25/1.29  Demodulation         : 0.07
% 2.25/1.29  BG Simplification    : 0.02
% 2.25/1.29  Subsumption          : 0.03
% 2.25/1.29  Abstraction          : 0.01
% 2.25/1.29  MUC search           : 0.00
% 2.25/1.29  Cooper               : 0.00
% 2.25/1.29  Total                : 0.59
% 2.25/1.29  Index Insertion      : 0.00
% 2.25/1.29  Index Deletion       : 0.00
% 2.25/1.29  Index Matching       : 0.00
% 2.25/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
