%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 104 expanded)
%              Number of equality atoms :   34 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_29)) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_283,plain,(
    ! [A_66,B_67] :
      ( k10_relat_1(A_66,k1_relat_1(B_67)) = k1_relat_1(k5_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_292,plain,(
    ! [A_66,A_25] :
      ( k1_relat_1(k5_relat_1(A_66,k6_relat_1(A_25))) = k10_relat_1(A_66,A_25)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_283])).

tff(c_297,plain,(
    ! [A_68,A_69] :
      ( k1_relat_1(k5_relat_1(A_68,k6_relat_1(A_69))) = k10_relat_1(A_68,A_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_292])).

tff(c_309,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_29,B_30))) = k10_relat_1(k6_relat_1(B_30),A_29)
      | ~ v1_relat_1(k6_relat_1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_297])).

tff(c_320,plain,(
    ! [B_30,A_29] : k10_relat_1(k6_relat_1(B_30),A_29) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_309])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_345,plain,(
    ! [B_72,C_73,A_74] :
      ( k10_relat_1(k5_relat_1(B_72,C_73),A_74) = k10_relat_1(B_72,k10_relat_1(C_73,A_74))
      | ~ v1_relat_1(C_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_365,plain,(
    ! [A_26,B_27,A_74] :
      ( k10_relat_1(k6_relat_1(A_26),k10_relat_1(B_27,A_74)) = k10_relat_1(k7_relat_1(B_27,A_26),A_74)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_345])).

tff(c_2181,plain,(
    ! [B_112,A_113,A_114] :
      ( k3_xboole_0(k10_relat_1(B_112,A_113),A_114) = k10_relat_1(k7_relat_1(B_112,A_114),A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_320,c_365])).

tff(c_22,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [B_50,A_51] : k5_relat_1(k6_relat_1(B_50),k6_relat_1(A_51)) = k6_relat_1(k3_xboole_0(A_51,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_143,plain,(
    ! [A_51,B_50] :
      ( k7_relat_1(k6_relat_1(A_51),B_50) = k6_relat_1(k3_xboole_0(A_51,B_50))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_24])).

tff(c_160,plain,(
    ! [A_51,B_50] : k7_relat_1(k6_relat_1(A_51),B_50) = k6_relat_1(k3_xboole_0(A_51,B_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( k5_relat_1(B_17,k6_relat_1(A_16)) = k8_relat_1(A_16,B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_16,A_46] :
      ( k8_relat_1(A_16,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_16),A_46)
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14])).

tff(c_123,plain,(
    ! [A_16,A_46] : k8_relat_1(A_16,k6_relat_1(A_46)) = k7_relat_1(k6_relat_1(A_16),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_113])).

tff(c_168,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(k2_relat_1(B_52),A_53) = k2_relat_1(k8_relat_1(A_53,B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [A_53,A_25] :
      ( k2_relat_1(k8_relat_1(A_53,k6_relat_1(A_25))) = k3_xboole_0(A_25,A_53)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_181,plain,(
    ! [A_53,A_25] : k2_relat_1(k7_relat_1(k6_relat_1(A_53),A_25)) = k3_xboole_0(A_25,A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_123,c_177])).

tff(c_212,plain,(
    ! [A_53,A_25] : k3_xboole_0(A_53,A_25) = k3_xboole_0(A_25,A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_160,c_181])).

tff(c_3624,plain,(
    ! [A_138,B_139,A_140] :
      ( k3_xboole_0(A_138,k10_relat_1(B_139,A_140)) = k10_relat_1(k7_relat_1(B_139,A_138),A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2181,c_212])).

tff(c_32,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3715,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3624,c_32])).

tff(c_3779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:50:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.25  
% 6.42/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.25  %$ v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.42/2.25  
% 6.42/2.25  %Foreground sorts:
% 6.42/2.25  
% 6.42/2.25  
% 6.42/2.25  %Background operators:
% 6.42/2.25  
% 6.42/2.25  
% 6.42/2.25  %Foreground operators:
% 6.42/2.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.42/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.42/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.42/2.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.42/2.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.42/2.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.42/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.42/2.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.42/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.42/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.42/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.42/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.42/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.42/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.42/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.42/2.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.42/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.42/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.42/2.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.42/2.25  
% 6.42/2.27  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.42/2.27  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.42/2.27  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.42/2.27  tff(f_71, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.42/2.27  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.42/2.27  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.42/2.27  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 6.42/2.27  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 6.42/2.27  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 6.42/2.27  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.42/2.27  tff(c_26, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.42/2.27  tff(c_20, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.42/2.27  tff(c_30, plain, (![B_30, A_29]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_29))=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.42/2.27  tff(c_283, plain, (![A_66, B_67]: (k10_relat_1(A_66, k1_relat_1(B_67))=k1_relat_1(k5_relat_1(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.42/2.27  tff(c_292, plain, (![A_66, A_25]: (k1_relat_1(k5_relat_1(A_66, k6_relat_1(A_25)))=k10_relat_1(A_66, A_25) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_20, c_283])).
% 6.42/2.27  tff(c_297, plain, (![A_68, A_69]: (k1_relat_1(k5_relat_1(A_68, k6_relat_1(A_69)))=k10_relat_1(A_68, A_69) | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_292])).
% 6.42/2.27  tff(c_309, plain, (![A_29, B_30]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_29, B_30)))=k10_relat_1(k6_relat_1(B_30), A_29) | ~v1_relat_1(k6_relat_1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_297])).
% 6.42/2.27  tff(c_320, plain, (![B_30, A_29]: (k10_relat_1(k6_relat_1(B_30), A_29)=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_309])).
% 6.42/2.27  tff(c_24, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.42/2.27  tff(c_345, plain, (![B_72, C_73, A_74]: (k10_relat_1(k5_relat_1(B_72, C_73), A_74)=k10_relat_1(B_72, k10_relat_1(C_73, A_74)) | ~v1_relat_1(C_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.42/2.27  tff(c_365, plain, (![A_26, B_27, A_74]: (k10_relat_1(k6_relat_1(A_26), k10_relat_1(B_27, A_74))=k10_relat_1(k7_relat_1(B_27, A_26), A_74) | ~v1_relat_1(B_27) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_24, c_345])).
% 6.42/2.27  tff(c_2181, plain, (![B_112, A_113, A_114]: (k3_xboole_0(k10_relat_1(B_112, A_113), A_114)=k10_relat_1(k7_relat_1(B_112, A_114), A_113) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_320, c_365])).
% 6.42/2.27  tff(c_22, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.42/2.27  tff(c_137, plain, (![B_50, A_51]: (k5_relat_1(k6_relat_1(B_50), k6_relat_1(A_51))=k6_relat_1(k3_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.42/2.27  tff(c_143, plain, (![A_51, B_50]: (k7_relat_1(k6_relat_1(A_51), B_50)=k6_relat_1(k3_xboole_0(A_51, B_50)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_24])).
% 6.42/2.27  tff(c_160, plain, (![A_51, B_50]: (k7_relat_1(k6_relat_1(A_51), B_50)=k6_relat_1(k3_xboole_0(A_51, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_143])).
% 6.42/2.27  tff(c_106, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.42/2.27  tff(c_14, plain, (![B_17, A_16]: (k5_relat_1(B_17, k6_relat_1(A_16))=k8_relat_1(A_16, B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.42/2.27  tff(c_113, plain, (![A_16, A_46]: (k8_relat_1(A_16, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_16), A_46) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_14])).
% 6.42/2.27  tff(c_123, plain, (![A_16, A_46]: (k8_relat_1(A_16, k6_relat_1(A_46))=k7_relat_1(k6_relat_1(A_16), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_113])).
% 6.42/2.27  tff(c_168, plain, (![B_52, A_53]: (k3_xboole_0(k2_relat_1(B_52), A_53)=k2_relat_1(k8_relat_1(A_53, B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.27  tff(c_177, plain, (![A_53, A_25]: (k2_relat_1(k8_relat_1(A_53, k6_relat_1(A_25)))=k3_xboole_0(A_25, A_53) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_168])).
% 6.42/2.27  tff(c_181, plain, (![A_53, A_25]: (k2_relat_1(k7_relat_1(k6_relat_1(A_53), A_25))=k3_xboole_0(A_25, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_123, c_177])).
% 6.42/2.27  tff(c_212, plain, (![A_53, A_25]: (k3_xboole_0(A_53, A_25)=k3_xboole_0(A_25, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_160, c_181])).
% 6.42/2.27  tff(c_3624, plain, (![A_138, B_139, A_140]: (k3_xboole_0(A_138, k10_relat_1(B_139, A_140))=k10_relat_1(k7_relat_1(B_139, A_138), A_140) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_2181, c_212])).
% 6.42/2.27  tff(c_32, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.42/2.27  tff(c_3715, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3624, c_32])).
% 6.42/2.27  tff(c_3779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3715])).
% 6.42/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.27  
% 6.42/2.27  Inference rules
% 6.42/2.27  ----------------------
% 6.42/2.27  #Ref     : 0
% 6.42/2.27  #Sup     : 974
% 6.42/2.27  #Fact    : 0
% 6.42/2.27  #Define  : 0
% 6.42/2.27  #Split   : 0
% 6.42/2.27  #Chain   : 0
% 6.42/2.27  #Close   : 0
% 6.42/2.27  
% 6.42/2.27  Ordering : KBO
% 6.42/2.27  
% 6.42/2.27  Simplification rules
% 6.42/2.27  ----------------------
% 6.42/2.27  #Subsume      : 152
% 6.42/2.27  #Demod        : 573
% 6.42/2.27  #Tautology    : 196
% 6.42/2.27  #SimpNegUnit  : 0
% 6.42/2.27  #BackRed      : 1
% 6.42/2.27  
% 6.42/2.27  #Partial instantiations: 0
% 6.42/2.27  #Strategies tried      : 1
% 6.42/2.27  
% 6.42/2.27  Timing (in seconds)
% 6.42/2.27  ----------------------
% 6.42/2.27  Preprocessing        : 0.31
% 6.42/2.27  Parsing              : 0.16
% 6.42/2.27  CNF conversion       : 0.02
% 6.42/2.27  Main loop            : 1.21
% 6.42/2.27  Inferencing          : 0.30
% 6.42/2.27  Reduction            : 0.68
% 6.42/2.27  Demodulation         : 0.61
% 6.42/2.27  BG Simplification    : 0.05
% 6.42/2.27  Subsumption          : 0.13
% 6.42/2.27  Abstraction          : 0.07
% 6.42/2.27  MUC search           : 0.00
% 6.42/2.27  Cooper               : 0.00
% 6.42/2.27  Total                : 1.54
% 6.42/2.27  Index Insertion      : 0.00
% 6.42/2.27  Index Deletion       : 0.00
% 6.42/2.27  Index Matching       : 0.00
% 6.42/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
