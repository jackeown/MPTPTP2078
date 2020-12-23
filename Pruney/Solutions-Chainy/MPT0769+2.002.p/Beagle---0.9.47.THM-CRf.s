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
% DateTime   : Thu Dec  3 10:06:37 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 107 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( k7_relat_1(k8_relat_1(A_26,B_27),A_26) = k2_wellord1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154,plain,(
    ! [A_49,B_50,C_51] :
      ( k8_relat_1(A_49,k5_relat_1(B_50,C_51)) = k5_relat_1(B_50,k8_relat_1(A_49,C_51))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [A_23,A_49,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),k8_relat_1(A_49,B_24)) = k8_relat_1(A_49,k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_154])).

tff(c_175,plain,(
    ! [A_23,A_49,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),k8_relat_1(A_49,B_24)) = k8_relat_1(A_49,k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_169])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [B_46,C_47,A_48] :
      ( k7_relat_1(k5_relat_1(B_46,C_47),A_48) = k5_relat_1(k7_relat_1(B_46,A_48),C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_144,plain,(
    ! [B_11,A_48,A_10] :
      ( k5_relat_1(k7_relat_1(B_11,A_48),k6_relat_1(A_10)) = k7_relat_1(k8_relat_1(A_10,B_11),A_48)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_135])).

tff(c_151,plain,(
    ! [B_11,A_48,A_10] :
      ( k5_relat_1(k7_relat_1(B_11,A_48),k6_relat_1(A_10)) = k7_relat_1(k8_relat_1(A_10,B_11),A_48)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_144])).

tff(c_272,plain,(
    ! [A_61,B_62,C_63] :
      ( k5_relat_1(k5_relat_1(A_61,B_62),C_63) = k5_relat_1(A_61,k5_relat_1(B_62,C_63))
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_321,plain,(
    ! [A_23,B_24,C_63] :
      ( k5_relat_1(k6_relat_1(A_23),k5_relat_1(B_24,C_63)) = k5_relat_1(k7_relat_1(B_24,A_23),C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_272])).

tff(c_428,plain,(
    ! [A_70,B_71,C_72] :
      ( k5_relat_1(k6_relat_1(A_70),k5_relat_1(B_71,C_72)) = k5_relat_1(k7_relat_1(B_71,A_70),C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_473,plain,(
    ! [B_11,A_70,A_10] :
      ( k5_relat_1(k7_relat_1(B_11,A_70),k6_relat_1(A_10)) = k5_relat_1(k6_relat_1(A_70),k8_relat_1(A_10,B_11))
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_428])).

tff(c_503,plain,(
    ! [B_73,A_74,A_75] :
      ( k5_relat_1(k7_relat_1(B_73,A_74),k6_relat_1(A_75)) = k5_relat_1(k6_relat_1(A_74),k8_relat_1(A_75,B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_473])).

tff(c_1018,plain,(
    ! [A_97,A_98,B_99] :
      ( k5_relat_1(k6_relat_1(A_97),k8_relat_1(A_98,B_99)) = k7_relat_1(k8_relat_1(A_98,B_99),A_97)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_503])).

tff(c_1311,plain,(
    ! [A_112,B_113,A_114] :
      ( k8_relat_1(A_112,k7_relat_1(B_113,A_114)) = k7_relat_1(k8_relat_1(A_112,B_113),A_114)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1018])).

tff(c_26,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_2','#skF_1')) != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1338,plain,
    ( k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_26])).

tff(c_1358,plain,(
    k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_28,c_1338])).

tff(c_1365,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1358])).

tff(c_1369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  %$ v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > #skF_2 > #skF_1
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.13/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.13/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.13/1.50  
% 3.13/1.51  tff(f_82, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 3.13/1.51  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 3.13/1.51  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.13/1.51  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.13/1.51  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 3.13/1.51  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.13/1.51  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 3.13/1.51  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.13/1.51  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.51  tff(c_24, plain, (![A_26, B_27]: (k7_relat_1(k8_relat_1(A_26, B_27), A_26)=k2_wellord1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.51  tff(c_20, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.51  tff(c_18, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.51  tff(c_154, plain, (![A_49, B_50, C_51]: (k8_relat_1(A_49, k5_relat_1(B_50, C_51))=k5_relat_1(B_50, k8_relat_1(A_49, C_51)) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.51  tff(c_169, plain, (![A_23, A_49, B_24]: (k5_relat_1(k6_relat_1(A_23), k8_relat_1(A_49, B_24))=k8_relat_1(A_49, k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_18, c_154])).
% 3.13/1.51  tff(c_175, plain, (![A_23, A_49, B_24]: (k5_relat_1(k6_relat_1(A_23), k8_relat_1(A_49, B_24))=k8_relat_1(A_49, k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_169])).
% 3.13/1.51  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.51  tff(c_135, plain, (![B_46, C_47, A_48]: (k7_relat_1(k5_relat_1(B_46, C_47), A_48)=k5_relat_1(k7_relat_1(B_46, A_48), C_47) | ~v1_relat_1(C_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.51  tff(c_144, plain, (![B_11, A_48, A_10]: (k5_relat_1(k7_relat_1(B_11, A_48), k6_relat_1(A_10))=k7_relat_1(k8_relat_1(A_10, B_11), A_48) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_135])).
% 3.13/1.51  tff(c_151, plain, (![B_11, A_48, A_10]: (k5_relat_1(k7_relat_1(B_11, A_48), k6_relat_1(A_10))=k7_relat_1(k8_relat_1(A_10, B_11), A_48) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_144])).
% 3.13/1.51  tff(c_272, plain, (![A_61, B_62, C_63]: (k5_relat_1(k5_relat_1(A_61, B_62), C_63)=k5_relat_1(A_61, k5_relat_1(B_62, C_63)) | ~v1_relat_1(C_63) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.51  tff(c_321, plain, (![A_23, B_24, C_63]: (k5_relat_1(k6_relat_1(A_23), k5_relat_1(B_24, C_63))=k5_relat_1(k7_relat_1(B_24, A_23), C_63) | ~v1_relat_1(C_63) | ~v1_relat_1(B_24) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_18, c_272])).
% 3.13/1.51  tff(c_428, plain, (![A_70, B_71, C_72]: (k5_relat_1(k6_relat_1(A_70), k5_relat_1(B_71, C_72))=k5_relat_1(k7_relat_1(B_71, A_70), C_72) | ~v1_relat_1(C_72) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_321])).
% 3.13/1.51  tff(c_473, plain, (![B_11, A_70, A_10]: (k5_relat_1(k7_relat_1(B_11, A_70), k6_relat_1(A_10))=k5_relat_1(k6_relat_1(A_70), k8_relat_1(A_10, B_11)) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_428])).
% 3.13/1.51  tff(c_503, plain, (![B_73, A_74, A_75]: (k5_relat_1(k7_relat_1(B_73, A_74), k6_relat_1(A_75))=k5_relat_1(k6_relat_1(A_74), k8_relat_1(A_75, B_73)) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_473])).
% 3.13/1.51  tff(c_1018, plain, (![A_97, A_98, B_99]: (k5_relat_1(k6_relat_1(A_97), k8_relat_1(A_98, B_99))=k7_relat_1(k8_relat_1(A_98, B_99), A_97) | ~v1_relat_1(B_99) | ~v1_relat_1(B_99))), inference(superposition, [status(thm), theory('equality')], [c_151, c_503])).
% 3.13/1.51  tff(c_1311, plain, (![A_112, B_113, A_114]: (k8_relat_1(A_112, k7_relat_1(B_113, A_114))=k7_relat_1(k8_relat_1(A_112, B_113), A_114) | ~v1_relat_1(B_113) | ~v1_relat_1(B_113) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_175, c_1018])).
% 3.13/1.51  tff(c_26, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_2', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.51  tff(c_1338, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1311, c_26])).
% 3.13/1.51  tff(c_1358, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_28, c_1338])).
% 3.13/1.51  tff(c_1365, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1358])).
% 3.13/1.51  tff(c_1369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1365])).
% 3.13/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  Inference rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Ref     : 0
% 3.13/1.51  #Sup     : 300
% 3.13/1.51  #Fact    : 0
% 3.13/1.51  #Define  : 0
% 3.13/1.51  #Split   : 0
% 3.13/1.51  #Chain   : 0
% 3.13/1.51  #Close   : 0
% 3.13/1.51  
% 3.13/1.51  Ordering : KBO
% 3.13/1.51  
% 3.13/1.51  Simplification rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Subsume      : 24
% 3.13/1.51  #Demod        : 229
% 3.13/1.51  #Tautology    : 102
% 3.13/1.51  #SimpNegUnit  : 1
% 3.13/1.51  #BackRed      : 1
% 3.13/1.51  
% 3.13/1.51  #Partial instantiations: 0
% 3.13/1.51  #Strategies tried      : 1
% 3.13/1.51  
% 3.13/1.51  Timing (in seconds)
% 3.13/1.51  ----------------------
% 3.13/1.52  Preprocessing        : 0.31
% 3.13/1.52  Parsing              : 0.17
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.43
% 3.13/1.52  Inferencing          : 0.17
% 3.13/1.52  Reduction            : 0.14
% 3.13/1.52  Demodulation         : 0.10
% 3.13/1.52  BG Simplification    : 0.03
% 3.13/1.52  Subsumption          : 0.06
% 3.13/1.52  Abstraction          : 0.04
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.76
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
