%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 182 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 269 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_10,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = k8_relat_1(A_6,B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_6,A_30] :
      ( k8_relat_1(A_6,k6_relat_1(A_30)) = k7_relat_1(k6_relat_1(A_6),A_30)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_106,plain,(
    ! [A_6,A_30] : k8_relat_1(A_6,k6_relat_1(A_30)) = k7_relat_1(k6_relat_1(A_6),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_93])).

tff(c_22,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_34,B_35] :
      ( k8_relat_1(A_34,B_35) = B_35
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [B_38] :
      ( k8_relat_1(k2_relat_1(B_38),B_38) = B_38
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_155,plain,(
    ! [A_30] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_30))),A_30) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_106])).

tff(c_168,plain,(
    ! [A_30] : k7_relat_1(k6_relat_1(A_30),A_30) = k6_relat_1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22,c_155])).

tff(c_327,plain,(
    ! [A_49,B_50,C_51] :
      ( k8_relat_1(k3_xboole_0(A_49,B_50),C_51) = k8_relat_1(A_49,k8_relat_1(B_50,C_51))
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_350,plain,(
    ! [A_49,B_50,A_30] :
      ( k8_relat_1(A_49,k8_relat_1(B_50,k6_relat_1(A_30))) = k7_relat_1(k6_relat_1(k3_xboole_0(A_49,B_50)),A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_327])).

tff(c_773,plain,(
    ! [A_70,B_71,A_72] : k8_relat_1(A_70,k7_relat_1(k6_relat_1(B_71),A_72)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_70,B_71)),A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_106,c_350])).

tff(c_818,plain,(
    ! [A_70,A_30] : k7_relat_1(k6_relat_1(k3_xboole_0(A_70,A_30)),A_30) = k8_relat_1(A_70,k6_relat_1(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_773])).

tff(c_836,plain,(
    ! [A_70,A_30] : k7_relat_1(k6_relat_1(k3_xboole_0(A_70,A_30)),A_30) = k7_relat_1(k6_relat_1(A_70),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_818])).

tff(c_20,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(k1_relat_1(B_36),A_37) = k1_relat_1(k7_relat_1(B_36,A_37))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,(
    ! [A_15,A_37] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_37)) = k3_xboole_0(A_15,A_37)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_147,plain,(
    ! [A_15,A_37] : k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_37)) = k3_xboole_0(A_15,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_143])).

tff(c_837,plain,(
    ! [A_73,A_74] : k7_relat_1(k6_relat_1(k3_xboole_0(A_73,A_74)),A_74) = k7_relat_1(k6_relat_1(A_73),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_818])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,k3_xboole_0(k1_relat_1(B_40),A_41)) = k7_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,k1_relat_1(k7_relat_1(B_17,A_16))) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_184])).

tff(c_849,plain,(
    ! [A_73,A_74] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_73,A_74)),k1_relat_1(k7_relat_1(k6_relat_1(A_73),A_74))) = k7_relat_1(k6_relat_1(k3_xboole_0(A_73,A_74)),A_74)
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_73,A_74)))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_73,A_74))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_193])).

tff(c_879,plain,(
    ! [A_73,A_74] : k7_relat_1(k6_relat_1(A_73),A_74) = k6_relat_1(k3_xboole_0(A_73,A_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_836,c_168,c_147,c_849])).

tff(c_28,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_108,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  
% 2.62/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.62/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.34  
% 2.62/1.36  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.62/1.36  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.62/1.36  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.62/1.36  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.62/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.36  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.62/1.36  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 2.62/1.36  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.62/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.62/1.36  tff(f_68, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.62/1.36  tff(c_10, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.36  tff(c_86, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.36  tff(c_12, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=k8_relat_1(A_6, B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.36  tff(c_93, plain, (![A_6, A_30]: (k8_relat_1(A_6, k6_relat_1(A_30))=k7_relat_1(k6_relat_1(A_6), A_30) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_12])).
% 2.62/1.36  tff(c_106, plain, (![A_6, A_30]: (k8_relat_1(A_6, k6_relat_1(A_30))=k7_relat_1(k6_relat_1(A_6), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_93])).
% 2.62/1.36  tff(c_22, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.36  tff(c_123, plain, (![A_34, B_35]: (k8_relat_1(A_34, B_35)=B_35 | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.36  tff(c_148, plain, (![B_38]: (k8_relat_1(k2_relat_1(B_38), B_38)=B_38 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.62/1.36  tff(c_155, plain, (![A_30]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_30))), A_30)=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_106])).
% 2.62/1.36  tff(c_168, plain, (![A_30]: (k7_relat_1(k6_relat_1(A_30), A_30)=k6_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22, c_155])).
% 2.62/1.36  tff(c_327, plain, (![A_49, B_50, C_51]: (k8_relat_1(k3_xboole_0(A_49, B_50), C_51)=k8_relat_1(A_49, k8_relat_1(B_50, C_51)) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.36  tff(c_350, plain, (![A_49, B_50, A_30]: (k8_relat_1(A_49, k8_relat_1(B_50, k6_relat_1(A_30)))=k7_relat_1(k6_relat_1(k3_xboole_0(A_49, B_50)), A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_327])).
% 2.62/1.36  tff(c_773, plain, (![A_70, B_71, A_72]: (k8_relat_1(A_70, k7_relat_1(k6_relat_1(B_71), A_72))=k7_relat_1(k6_relat_1(k3_xboole_0(A_70, B_71)), A_72))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_106, c_350])).
% 2.62/1.36  tff(c_818, plain, (![A_70, A_30]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_70, A_30)), A_30)=k8_relat_1(A_70, k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_773])).
% 2.62/1.36  tff(c_836, plain, (![A_70, A_30]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_70, A_30)), A_30)=k7_relat_1(k6_relat_1(A_70), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_818])).
% 2.62/1.36  tff(c_20, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.36  tff(c_134, plain, (![B_36, A_37]: (k3_xboole_0(k1_relat_1(B_36), A_37)=k1_relat_1(k7_relat_1(B_36, A_37)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.36  tff(c_143, plain, (![A_15, A_37]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_37))=k3_xboole_0(A_15, A_37) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_134])).
% 2.62/1.36  tff(c_147, plain, (![A_15, A_37]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_37))=k3_xboole_0(A_15, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_143])).
% 2.62/1.36  tff(c_837, plain, (![A_73, A_74]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_73, A_74)), A_74)=k7_relat_1(k6_relat_1(A_73), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_818])).
% 2.62/1.36  tff(c_24, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.36  tff(c_184, plain, (![B_40, A_41]: (k7_relat_1(B_40, k3_xboole_0(k1_relat_1(B_40), A_41))=k7_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.36  tff(c_193, plain, (![B_17, A_16]: (k7_relat_1(B_17, k1_relat_1(k7_relat_1(B_17, A_16)))=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_24, c_184])).
% 2.62/1.36  tff(c_849, plain, (![A_73, A_74]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_73, A_74)), k1_relat_1(k7_relat_1(k6_relat_1(A_73), A_74)))=k7_relat_1(k6_relat_1(k3_xboole_0(A_73, A_74)), A_74) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_73, A_74))) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_73, A_74))))), inference(superposition, [status(thm), theory('equality')], [c_837, c_193])).
% 2.62/1.36  tff(c_879, plain, (![A_73, A_74]: (k7_relat_1(k6_relat_1(A_73), A_74)=k6_relat_1(k3_xboole_0(A_73, A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_836, c_168, c_147, c_849])).
% 2.62/1.36  tff(c_28, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.36  tff(c_96, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_28])).
% 2.62/1.36  tff(c_108, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 2.62/1.36  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_879, c_108])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 193
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 1
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 5
% 2.62/1.36  #Demod        : 205
% 2.62/1.36  #Tautology    : 113
% 2.62/1.36  #SimpNegUnit  : 0
% 2.62/1.36  #BackRed      : 9
% 2.62/1.36  
% 2.62/1.36  #Partial instantiations: 0
% 2.62/1.36  #Strategies tried      : 1
% 2.62/1.36  
% 2.62/1.36  Timing (in seconds)
% 2.62/1.36  ----------------------
% 2.62/1.36  Preprocessing        : 0.29
% 2.62/1.36  Parsing              : 0.15
% 2.62/1.36  CNF conversion       : 0.02
% 2.62/1.36  Main loop            : 0.31
% 2.62/1.36  Inferencing          : 0.12
% 2.62/1.36  Reduction            : 0.11
% 2.62/1.36  Demodulation         : 0.08
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.04
% 2.62/1.36  Abstraction          : 0.02
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.62
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
