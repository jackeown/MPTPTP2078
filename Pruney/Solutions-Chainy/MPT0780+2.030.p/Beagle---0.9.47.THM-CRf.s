%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 191 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k2_wellord1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k7_relat_1(k8_relat_1(A_18,B_19),A_18) = k2_wellord1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,(
    ! [B_47,A_48] :
      ( k7_relat_1(B_47,A_48) = B_47
      | ~ r1_tarski(k1_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_596,plain,(
    ! [B_90,A_91] :
      ( k7_relat_1(k7_relat_1(B_90,A_91),A_91) = k7_relat_1(B_90,A_91)
      | ~ v1_relat_1(k7_relat_1(B_90,A_91))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_12,c_108])).

tff(c_602,plain,(
    ! [A_92,B_93] :
      ( k7_relat_1(k7_relat_1(A_92,B_93),B_93) = k7_relat_1(A_92,B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_4,c_596])).

tff(c_1963,plain,(
    ! [A_155,B_156] :
      ( k7_relat_1(k8_relat_1(A_155,B_156),A_155) = k7_relat_1(k2_wellord1(B_156,A_155),A_155)
      | ~ v1_relat_1(k8_relat_1(A_155,B_156))
      | ~ v1_relat_1(B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_602])).

tff(c_1977,plain,(
    ! [A_157,B_158] :
      ( k7_relat_1(k8_relat_1(A_157,B_158),A_157) = k7_relat_1(k2_wellord1(B_158,A_157),A_157)
      | ~ v1_relat_1(B_158) ) ),
    inference(resolution,[status(thm)],[c_6,c_1963])).

tff(c_2077,plain,(
    ! [B_159,A_160] :
      ( k7_relat_1(k2_wellord1(B_159,A_160),A_160) = k2_wellord1(B_159,A_160)
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_18])).

tff(c_2330,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(k1_relat_1(k2_wellord1(B_168,A_169)),A_169)
      | ~ v1_relat_1(k2_wellord1(B_168,A_169))
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2077,c_12])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_2')
      | ~ r1_tarski(A_35,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_116,plain,(
    ! [B_47] :
      ( k7_relat_1(B_47,'#skF_2') = B_47
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(k1_relat_1(B_47),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_108])).

tff(c_2428,plain,(
    ! [B_172] :
      ( k7_relat_1(k2_wellord1(B_172,'#skF_1'),'#skF_2') = k2_wellord1(B_172,'#skF_1')
      | ~ v1_relat_1(k2_wellord1(B_172,'#skF_1'))
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_2330,c_116])).

tff(c_2474,plain,(
    ! [A_173] :
      ( k7_relat_1(k2_wellord1(A_173,'#skF_1'),'#skF_2') = k2_wellord1(A_173,'#skF_1')
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_16,c_2428])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k8_relat_1(A_20,k7_relat_1(B_21,A_20)) = k2_wellord1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7590,plain,(
    ! [A_291] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_291,'#skF_1')) = k2_wellord1(k2_wellord1(A_291,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(k2_wellord1(A_291,'#skF_1'))
      | ~ v1_relat_1(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_20])).

tff(c_7654,plain,(
    ! [A_292] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_292,'#skF_1')) = k2_wellord1(k2_wellord1(A_292,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(A_292) ) ),
    inference(resolution,[status(thm)],[c_16,c_7590])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_45,B_46] :
      ( k8_relat_1(A_45,B_46) = B_46
      | ~ r1_tarski(k2_relat_1(B_46),A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_527,plain,(
    ! [A_86,B_87] :
      ( k8_relat_1(A_86,k8_relat_1(A_86,B_87)) = k8_relat_1(A_86,B_87)
      | ~ v1_relat_1(k8_relat_1(A_86,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_535,plain,(
    ! [A_88,B_89] :
      ( k8_relat_1(A_88,k8_relat_1(A_88,B_89)) = k8_relat_1(A_88,B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_527])).

tff(c_3508,plain,(
    ! [A_203,B_204] :
      ( k8_relat_1(A_203,k7_relat_1(B_204,A_203)) = k8_relat_1(A_203,k2_wellord1(B_204,A_203))
      | ~ v1_relat_1(k7_relat_1(B_204,A_203))
      | ~ v1_relat_1(B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_535])).

tff(c_3533,plain,(
    ! [B_205,A_206] :
      ( k8_relat_1(B_205,k7_relat_1(A_206,B_205)) = k8_relat_1(B_205,k2_wellord1(A_206,B_205))
      | ~ v1_relat_1(A_206) ) ),
    inference(resolution,[status(thm)],[c_4,c_3508])).

tff(c_3672,plain,(
    ! [B_207,A_208] :
      ( k8_relat_1(B_207,k2_wellord1(A_208,B_207)) = k2_wellord1(A_208,B_207)
      | ~ v1_relat_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3533,c_20])).

tff(c_4099,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k2_relat_1(k2_wellord1(A_217,B_218)),B_218)
      | ~ v1_relat_1(k2_wellord1(A_217,B_218))
      | ~ v1_relat_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3672,c_8])).

tff(c_106,plain,(
    ! [B_46] :
      ( k8_relat_1('#skF_2',B_46) = B_46
      | ~ v1_relat_1(B_46)
      | ~ r1_tarski(k2_relat_1(B_46),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_98])).

tff(c_4226,plain,(
    ! [A_221] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_221,'#skF_1')) = k2_wellord1(A_221,'#skF_1')
      | ~ v1_relat_1(k2_wellord1(A_221,'#skF_1'))
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_4099,c_106])).

tff(c_4280,plain,(
    ! [A_16] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_16,'#skF_1')) = k2_wellord1(A_16,'#skF_1')
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_4226])).

tff(c_7784,plain,(
    ! [A_293] :
      ( k2_wellord1(k2_wellord1(A_293,'#skF_1'),'#skF_2') = k2_wellord1(A_293,'#skF_1')
      | ~ v1_relat_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7654,c_4280])).

tff(c_118,plain,(
    ! [C_49,B_50,A_51] :
      ( k2_wellord1(k2_wellord1(C_49,B_50),A_51) = k2_wellord1(k2_wellord1(C_49,A_51),B_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_145,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_24])).

tff(c_184,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_7895,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7784,c_184])).

tff(c_7948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.70/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.62  
% 7.70/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.62  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.70/2.62  
% 7.70/2.62  %Foreground sorts:
% 7.70/2.62  
% 7.70/2.62  
% 7.70/2.62  %Background operators:
% 7.70/2.62  
% 7.70/2.62  
% 7.70/2.62  %Foreground operators:
% 7.70/2.62  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.70/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.70/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.70/2.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.70/2.62  tff('#skF_2', type, '#skF_2': $i).
% 7.70/2.62  tff('#skF_3', type, '#skF_3': $i).
% 7.70/2.62  tff('#skF_1', type, '#skF_1': $i).
% 7.70/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.70/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.62  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 7.70/2.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.70/2.62  
% 7.70/2.64  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 7.70/2.64  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 7.70/2.64  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 7.70/2.64  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 7.70/2.64  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.70/2.64  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 7.70/2.64  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.70/2.64  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.70/2.64  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 7.70/2.64  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 7.70/2.64  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 7.70/2.64  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 7.70/2.64  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.70/2.64  tff(c_16, plain, (![A_16, B_17]: (v1_relat_1(k2_wellord1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.70/2.64  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.70/2.64  tff(c_18, plain, (![A_18, B_19]: (k7_relat_1(k8_relat_1(A_18, B_19), A_18)=k2_wellord1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.70/2.64  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.70/2.64  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.70/2.64  tff(c_108, plain, (![B_47, A_48]: (k7_relat_1(B_47, A_48)=B_47 | ~r1_tarski(k1_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.70/2.64  tff(c_596, plain, (![B_90, A_91]: (k7_relat_1(k7_relat_1(B_90, A_91), A_91)=k7_relat_1(B_90, A_91) | ~v1_relat_1(k7_relat_1(B_90, A_91)) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_12, c_108])).
% 7.70/2.64  tff(c_602, plain, (![A_92, B_93]: (k7_relat_1(k7_relat_1(A_92, B_93), B_93)=k7_relat_1(A_92, B_93) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_4, c_596])).
% 7.70/2.64  tff(c_1963, plain, (![A_155, B_156]: (k7_relat_1(k8_relat_1(A_155, B_156), A_155)=k7_relat_1(k2_wellord1(B_156, A_155), A_155) | ~v1_relat_1(k8_relat_1(A_155, B_156)) | ~v1_relat_1(B_156))), inference(superposition, [status(thm), theory('equality')], [c_18, c_602])).
% 7.70/2.64  tff(c_1977, plain, (![A_157, B_158]: (k7_relat_1(k8_relat_1(A_157, B_158), A_157)=k7_relat_1(k2_wellord1(B_158, A_157), A_157) | ~v1_relat_1(B_158))), inference(resolution, [status(thm)], [c_6, c_1963])).
% 7.70/2.64  tff(c_2077, plain, (![B_159, A_160]: (k7_relat_1(k2_wellord1(B_159, A_160), A_160)=k2_wellord1(B_159, A_160) | ~v1_relat_1(B_159) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_1977, c_18])).
% 7.70/2.64  tff(c_2330, plain, (![B_168, A_169]: (r1_tarski(k1_relat_1(k2_wellord1(B_168, A_169)), A_169) | ~v1_relat_1(k2_wellord1(B_168, A_169)) | ~v1_relat_1(B_168) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_2077, c_12])).
% 7.70/2.64  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.70/2.64  tff(c_34, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.70/2.64  tff(c_43, plain, (![A_35]: (r1_tarski(A_35, '#skF_2') | ~r1_tarski(A_35, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_34])).
% 7.70/2.64  tff(c_116, plain, (![B_47]: (k7_relat_1(B_47, '#skF_2')=B_47 | ~v1_relat_1(B_47) | ~r1_tarski(k1_relat_1(B_47), '#skF_1'))), inference(resolution, [status(thm)], [c_43, c_108])).
% 7.70/2.64  tff(c_2428, plain, (![B_172]: (k7_relat_1(k2_wellord1(B_172, '#skF_1'), '#skF_2')=k2_wellord1(B_172, '#skF_1') | ~v1_relat_1(k2_wellord1(B_172, '#skF_1')) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_2330, c_116])).
% 7.70/2.64  tff(c_2474, plain, (![A_173]: (k7_relat_1(k2_wellord1(A_173, '#skF_1'), '#skF_2')=k2_wellord1(A_173, '#skF_1') | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_16, c_2428])).
% 7.70/2.64  tff(c_20, plain, (![A_20, B_21]: (k8_relat_1(A_20, k7_relat_1(B_21, A_20))=k2_wellord1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.70/2.64  tff(c_7590, plain, (![A_291]: (k8_relat_1('#skF_2', k2_wellord1(A_291, '#skF_1'))=k2_wellord1(k2_wellord1(A_291, '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1(A_291, '#skF_1')) | ~v1_relat_1(A_291))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_20])).
% 7.70/2.64  tff(c_7654, plain, (![A_292]: (k8_relat_1('#skF_2', k2_wellord1(A_292, '#skF_1'))=k2_wellord1(k2_wellord1(A_292, '#skF_1'), '#skF_2') | ~v1_relat_1(A_292))), inference(resolution, [status(thm)], [c_16, c_7590])).
% 7.70/2.64  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.70/2.64  tff(c_98, plain, (![A_45, B_46]: (k8_relat_1(A_45, B_46)=B_46 | ~r1_tarski(k2_relat_1(B_46), A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.70/2.64  tff(c_527, plain, (![A_86, B_87]: (k8_relat_1(A_86, k8_relat_1(A_86, B_87))=k8_relat_1(A_86, B_87) | ~v1_relat_1(k8_relat_1(A_86, B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_8, c_98])).
% 7.70/2.64  tff(c_535, plain, (![A_88, B_89]: (k8_relat_1(A_88, k8_relat_1(A_88, B_89))=k8_relat_1(A_88, B_89) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_6, c_527])).
% 7.70/2.64  tff(c_3508, plain, (![A_203, B_204]: (k8_relat_1(A_203, k7_relat_1(B_204, A_203))=k8_relat_1(A_203, k2_wellord1(B_204, A_203)) | ~v1_relat_1(k7_relat_1(B_204, A_203)) | ~v1_relat_1(B_204))), inference(superposition, [status(thm), theory('equality')], [c_20, c_535])).
% 7.70/2.64  tff(c_3533, plain, (![B_205, A_206]: (k8_relat_1(B_205, k7_relat_1(A_206, B_205))=k8_relat_1(B_205, k2_wellord1(A_206, B_205)) | ~v1_relat_1(A_206))), inference(resolution, [status(thm)], [c_4, c_3508])).
% 7.70/2.64  tff(c_3672, plain, (![B_207, A_208]: (k8_relat_1(B_207, k2_wellord1(A_208, B_207))=k2_wellord1(A_208, B_207) | ~v1_relat_1(A_208) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_3533, c_20])).
% 7.70/2.64  tff(c_4099, plain, (![A_217, B_218]: (r1_tarski(k2_relat_1(k2_wellord1(A_217, B_218)), B_218) | ~v1_relat_1(k2_wellord1(A_217, B_218)) | ~v1_relat_1(A_217) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_3672, c_8])).
% 7.70/2.64  tff(c_106, plain, (![B_46]: (k8_relat_1('#skF_2', B_46)=B_46 | ~v1_relat_1(B_46) | ~r1_tarski(k2_relat_1(B_46), '#skF_1'))), inference(resolution, [status(thm)], [c_43, c_98])).
% 7.70/2.64  tff(c_4226, plain, (![A_221]: (k8_relat_1('#skF_2', k2_wellord1(A_221, '#skF_1'))=k2_wellord1(A_221, '#skF_1') | ~v1_relat_1(k2_wellord1(A_221, '#skF_1')) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_4099, c_106])).
% 7.70/2.64  tff(c_4280, plain, (![A_16]: (k8_relat_1('#skF_2', k2_wellord1(A_16, '#skF_1'))=k2_wellord1(A_16, '#skF_1') | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_16, c_4226])).
% 7.70/2.64  tff(c_7784, plain, (![A_293]: (k2_wellord1(k2_wellord1(A_293, '#skF_1'), '#skF_2')=k2_wellord1(A_293, '#skF_1') | ~v1_relat_1(A_293) | ~v1_relat_1(A_293))), inference(superposition, [status(thm), theory('equality')], [c_7654, c_4280])).
% 7.70/2.64  tff(c_118, plain, (![C_49, B_50, A_51]: (k2_wellord1(k2_wellord1(C_49, B_50), A_51)=k2_wellord1(k2_wellord1(C_49, A_51), B_50) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.70/2.64  tff(c_24, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.70/2.64  tff(c_145, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_24])).
% 7.70/2.64  tff(c_184, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_145])).
% 7.70/2.64  tff(c_7895, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7784, c_184])).
% 7.70/2.64  tff(c_7948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_7895])).
% 7.70/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.64  
% 7.70/2.64  Inference rules
% 7.70/2.64  ----------------------
% 7.70/2.64  #Ref     : 0
% 7.70/2.64  #Sup     : 2172
% 7.70/2.64  #Fact    : 0
% 7.70/2.64  #Define  : 0
% 7.70/2.64  #Split   : 0
% 7.70/2.64  #Chain   : 0
% 7.70/2.64  #Close   : 0
% 7.70/2.64  
% 7.70/2.64  Ordering : KBO
% 7.70/2.64  
% 7.70/2.64  Simplification rules
% 7.70/2.64  ----------------------
% 7.70/2.64  #Subsume      : 375
% 7.70/2.64  #Demod        : 4
% 7.70/2.64  #Tautology    : 95
% 7.70/2.64  #SimpNegUnit  : 0
% 7.70/2.64  #BackRed      : 0
% 7.70/2.64  
% 7.70/2.64  #Partial instantiations: 0
% 7.70/2.64  #Strategies tried      : 1
% 7.70/2.64  
% 7.70/2.64  Timing (in seconds)
% 7.70/2.64  ----------------------
% 7.70/2.64  Preprocessing        : 0.29
% 7.70/2.64  Parsing              : 0.17
% 7.70/2.64  CNF conversion       : 0.02
% 7.70/2.64  Main loop            : 1.54
% 7.70/2.64  Inferencing          : 0.54
% 7.70/2.64  Reduction            : 0.32
% 7.70/2.64  Demodulation         : 0.21
% 7.70/2.64  BG Simplification    : 0.08
% 7.70/2.64  Subsumption          : 0.50
% 7.70/2.64  Abstraction          : 0.07
% 7.70/2.64  MUC search           : 0.00
% 7.70/2.64  Cooper               : 0.00
% 7.70/2.64  Total                : 1.86
% 7.70/2.64  Index Insertion      : 0.00
% 7.70/2.64  Index Deletion       : 0.00
% 7.70/2.64  Index Matching       : 0.00
% 7.70/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
