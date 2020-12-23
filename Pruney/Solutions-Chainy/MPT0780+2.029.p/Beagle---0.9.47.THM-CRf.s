%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:42 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  77 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 ( 151 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k2_wellord1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( k8_relat_1(A_19,k7_relat_1(B_20,A_19)) = k2_wellord1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_11,B_12)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [A_42,B_43] :
      ( k8_relat_1(A_42,B_43) = B_43
      | ~ r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_346,plain,(
    ! [A_67,B_68] :
      ( k8_relat_1(A_67,k8_relat_1(A_67,B_68)) = k8_relat_1(A_67,B_68)
      | ~ v1_relat_1(k8_relat_1(A_67,B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_354,plain,(
    ! [A_69,B_70] :
      ( k8_relat_1(A_69,k8_relat_1(A_69,B_70)) = k8_relat_1(A_69,B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_862,plain,(
    ! [A_108,B_109] :
      ( k8_relat_1(A_108,k7_relat_1(B_109,A_108)) = k8_relat_1(A_108,k2_wellord1(B_109,A_108))
      | ~ v1_relat_1(k7_relat_1(B_109,A_108))
      | ~ v1_relat_1(B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_354])).

tff(c_872,plain,(
    ! [B_110,A_111] :
      ( k8_relat_1(B_110,k7_relat_1(A_111,B_110)) = k8_relat_1(B_110,k2_wellord1(A_111,B_110))
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_4,c_862])).

tff(c_959,plain,(
    ! [B_112,A_113] :
      ( k8_relat_1(B_112,k2_wellord1(A_113,B_112)) = k2_wellord1(A_113,B_112)
      | ~ v1_relat_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_18])).

tff(c_1259,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(k2_wellord1(A_127,B_128)),B_128)
      | ~ v1_relat_1(k2_wellord1(A_127,B_128))
      | ~ v1_relat_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_10])).

tff(c_31,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_2')
      | ~ r1_tarski(A_32,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_94,plain,(
    ! [B_43] :
      ( k8_relat_1('#skF_2',B_43) = B_43
      | ~ v1_relat_1(B_43)
      | ~ r1_tarski(k2_relat_1(B_43),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37,c_86])).

tff(c_1307,plain,(
    ! [A_129] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_129,'#skF_1')) = k2_wellord1(A_129,'#skF_1')
      | ~ v1_relat_1(k2_wellord1(A_129,'#skF_1'))
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_1259,c_94])).

tff(c_1349,plain,(
    ! [A_130] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_130,'#skF_1')) = k2_wellord1(A_130,'#skF_1')
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_14,c_1307])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k7_relat_1(k8_relat_1(A_17,B_18),A_17) = k2_wellord1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3132,plain,(
    ! [A_181] :
      ( k7_relat_1(k2_wellord1(A_181,'#skF_1'),'#skF_2') = k2_wellord1(k2_wellord1(A_181,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(k2_wellord1(A_181,'#skF_1'))
      | ~ v1_relat_1(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_16])).

tff(c_3182,plain,(
    ! [A_182] :
      ( k7_relat_1(k2_wellord1(A_182,'#skF_1'),'#skF_2') = k2_wellord1(k2_wellord1(A_182,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_14,c_3132])).

tff(c_291,plain,(
    ! [C_61,A_62,B_63] :
      ( k7_relat_1(k7_relat_1(C_61,A_62),B_63) = k7_relat_1(C_61,A_62)
      | ~ r1_tarski(A_62,B_63)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1056,plain,(
    ! [A_116,B_117,B_118] :
      ( k7_relat_1(k8_relat_1(A_116,B_117),A_116) = k7_relat_1(k2_wellord1(B_117,A_116),B_118)
      | ~ r1_tarski(A_116,B_118)
      | ~ v1_relat_1(k8_relat_1(A_116,B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_291])).

tff(c_1694,plain,(
    ! [A_136,B_137,B_138] :
      ( k7_relat_1(k8_relat_1(A_136,B_137),A_136) = k7_relat_1(k2_wellord1(B_137,A_136),B_138)
      | ~ r1_tarski(A_136,B_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_1056])).

tff(c_1733,plain,(
    ! [B_137,A_136,B_138] :
      ( k7_relat_1(k2_wellord1(B_137,A_136),B_138) = k2_wellord1(B_137,A_136)
      | ~ v1_relat_1(B_137)
      | ~ r1_tarski(A_136,B_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_16])).

tff(c_3191,plain,(
    ! [A_182] :
      ( k2_wellord1(k2_wellord1(A_182,'#skF_1'),'#skF_2') = k2_wellord1(A_182,'#skF_1')
      | ~ v1_relat_1(A_182)
      | ~ r1_tarski('#skF_1','#skF_2')
      | ~ v1_relat_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3182,c_1733])).

tff(c_3253,plain,(
    ! [A_183] :
      ( k2_wellord1(k2_wellord1(A_183,'#skF_1'),'#skF_2') = k2_wellord1(A_183,'#skF_1')
      | ~ v1_relat_1(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3191])).

tff(c_111,plain,(
    ! [C_48,B_49,A_50] :
      ( k2_wellord1(k2_wellord1(C_48,B_49),A_50) = k2_wellord1(k2_wellord1(C_48,A_50),B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_22])).

tff(c_177,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_138])).

tff(c_3327,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3253,c_177])).

tff(c_3376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.97  
% 4.87/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.97  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.87/1.97  
% 4.87/1.97  %Foreground sorts:
% 4.87/1.97  
% 4.87/1.97  
% 4.87/1.97  %Background operators:
% 4.87/1.97  
% 4.87/1.97  
% 4.87/1.97  %Foreground operators:
% 4.87/1.97  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.87/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.87/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.87/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.87/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.97  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 4.87/1.97  
% 5.20/1.98  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 5.20/1.98  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 5.20/1.98  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.20/1.98  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 5.20/1.98  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 5.20/1.98  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 5.20/1.98  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 5.20/1.98  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.20/1.98  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 5.20/1.98  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 5.20/1.98  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 5.20/1.98  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.20/1.98  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.20/1.98  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k2_wellord1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/1.98  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/1.98  tff(c_18, plain, (![A_19, B_20]: (k8_relat_1(A_19, k7_relat_1(B_20, A_19))=k2_wellord1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.20/1.98  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.20/1.98  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k8_relat_1(A_11, B_12)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.20/1.98  tff(c_86, plain, (![A_42, B_43]: (k8_relat_1(A_42, B_43)=B_43 | ~r1_tarski(k2_relat_1(B_43), A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.98  tff(c_346, plain, (![A_67, B_68]: (k8_relat_1(A_67, k8_relat_1(A_67, B_68))=k8_relat_1(A_67, B_68) | ~v1_relat_1(k8_relat_1(A_67, B_68)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_10, c_86])).
% 5.20/1.98  tff(c_354, plain, (![A_69, B_70]: (k8_relat_1(A_69, k8_relat_1(A_69, B_70))=k8_relat_1(A_69, B_70) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_6, c_346])).
% 5.20/1.98  tff(c_862, plain, (![A_108, B_109]: (k8_relat_1(A_108, k7_relat_1(B_109, A_108))=k8_relat_1(A_108, k2_wellord1(B_109, A_108)) | ~v1_relat_1(k7_relat_1(B_109, A_108)) | ~v1_relat_1(B_109))), inference(superposition, [status(thm), theory('equality')], [c_18, c_354])).
% 5.20/1.98  tff(c_872, plain, (![B_110, A_111]: (k8_relat_1(B_110, k7_relat_1(A_111, B_110))=k8_relat_1(B_110, k2_wellord1(A_111, B_110)) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_4, c_862])).
% 5.20/1.98  tff(c_959, plain, (![B_112, A_113]: (k8_relat_1(B_112, k2_wellord1(A_113, B_112))=k2_wellord1(A_113, B_112) | ~v1_relat_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_872, c_18])).
% 5.20/1.98  tff(c_1259, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(k2_wellord1(A_127, B_128)), B_128) | ~v1_relat_1(k2_wellord1(A_127, B_128)) | ~v1_relat_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_959, c_10])).
% 5.20/1.98  tff(c_31, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.20/1.98  tff(c_37, plain, (![A_32]: (r1_tarski(A_32, '#skF_2') | ~r1_tarski(A_32, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_31])).
% 5.20/1.98  tff(c_94, plain, (![B_43]: (k8_relat_1('#skF_2', B_43)=B_43 | ~v1_relat_1(B_43) | ~r1_tarski(k2_relat_1(B_43), '#skF_1'))), inference(resolution, [status(thm)], [c_37, c_86])).
% 5.20/1.98  tff(c_1307, plain, (![A_129]: (k8_relat_1('#skF_2', k2_wellord1(A_129, '#skF_1'))=k2_wellord1(A_129, '#skF_1') | ~v1_relat_1(k2_wellord1(A_129, '#skF_1')) | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_1259, c_94])).
% 5.20/1.98  tff(c_1349, plain, (![A_130]: (k8_relat_1('#skF_2', k2_wellord1(A_130, '#skF_1'))=k2_wellord1(A_130, '#skF_1') | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_14, c_1307])).
% 5.20/1.98  tff(c_16, plain, (![A_17, B_18]: (k7_relat_1(k8_relat_1(A_17, B_18), A_17)=k2_wellord1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.20/1.98  tff(c_3132, plain, (![A_181]: (k7_relat_1(k2_wellord1(A_181, '#skF_1'), '#skF_2')=k2_wellord1(k2_wellord1(A_181, '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1(A_181, '#skF_1')) | ~v1_relat_1(A_181))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_16])).
% 5.20/1.98  tff(c_3182, plain, (![A_182]: (k7_relat_1(k2_wellord1(A_182, '#skF_1'), '#skF_2')=k2_wellord1(k2_wellord1(A_182, '#skF_1'), '#skF_2') | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_14, c_3132])).
% 5.20/1.98  tff(c_291, plain, (![C_61, A_62, B_63]: (k7_relat_1(k7_relat_1(C_61, A_62), B_63)=k7_relat_1(C_61, A_62) | ~r1_tarski(A_62, B_63) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.20/1.98  tff(c_1056, plain, (![A_116, B_117, B_118]: (k7_relat_1(k8_relat_1(A_116, B_117), A_116)=k7_relat_1(k2_wellord1(B_117, A_116), B_118) | ~r1_tarski(A_116, B_118) | ~v1_relat_1(k8_relat_1(A_116, B_117)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_16, c_291])).
% 5.20/1.98  tff(c_1694, plain, (![A_136, B_137, B_138]: (k7_relat_1(k8_relat_1(A_136, B_137), A_136)=k7_relat_1(k2_wellord1(B_137, A_136), B_138) | ~r1_tarski(A_136, B_138) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_6, c_1056])).
% 5.20/1.98  tff(c_1733, plain, (![B_137, A_136, B_138]: (k7_relat_1(k2_wellord1(B_137, A_136), B_138)=k2_wellord1(B_137, A_136) | ~v1_relat_1(B_137) | ~r1_tarski(A_136, B_138) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_1694, c_16])).
% 5.20/1.98  tff(c_3191, plain, (![A_182]: (k2_wellord1(k2_wellord1(A_182, '#skF_1'), '#skF_2')=k2_wellord1(A_182, '#skF_1') | ~v1_relat_1(A_182) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(A_182) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_3182, c_1733])).
% 5.20/1.98  tff(c_3253, plain, (![A_183]: (k2_wellord1(k2_wellord1(A_183, '#skF_1'), '#skF_2')=k2_wellord1(A_183, '#skF_1') | ~v1_relat_1(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3191])).
% 5.20/1.98  tff(c_111, plain, (![C_48, B_49, A_50]: (k2_wellord1(k2_wellord1(C_48, B_49), A_50)=k2_wellord1(k2_wellord1(C_48, A_50), B_49) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.20/1.98  tff(c_22, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.20/1.98  tff(c_138, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_22])).
% 5.20/1.98  tff(c_177, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_138])).
% 5.20/1.98  tff(c_3327, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3253, c_177])).
% 5.20/1.98  tff(c_3376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_3327])).
% 5.20/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.98  
% 5.20/1.98  Inference rules
% 5.20/1.98  ----------------------
% 5.20/1.98  #Ref     : 0
% 5.20/1.98  #Sup     : 949
% 5.20/1.98  #Fact    : 0
% 5.20/1.98  #Define  : 0
% 5.20/1.98  #Split   : 0
% 5.20/1.98  #Chain   : 0
% 5.20/1.98  #Close   : 0
% 5.20/1.98  
% 5.20/1.98  Ordering : KBO
% 5.20/1.98  
% 5.20/1.98  Simplification rules
% 5.20/1.98  ----------------------
% 5.20/1.98  #Subsume      : 175
% 5.20/1.98  #Demod        : 7
% 5.20/1.98  #Tautology    : 72
% 5.20/1.98  #SimpNegUnit  : 0
% 5.20/1.98  #BackRed      : 0
% 5.20/1.98  
% 5.20/1.98  #Partial instantiations: 0
% 5.20/1.98  #Strategies tried      : 1
% 5.20/1.98  
% 5.20/1.98  Timing (in seconds)
% 5.20/1.98  ----------------------
% 5.20/1.99  Preprocessing        : 0.29
% 5.20/1.99  Parsing              : 0.17
% 5.20/1.99  CNF conversion       : 0.02
% 5.20/1.99  Main loop            : 0.87
% 5.20/1.99  Inferencing          : 0.33
% 5.20/1.99  Reduction            : 0.19
% 5.20/1.99  Demodulation         : 0.13
% 5.20/1.99  BG Simplification    : 0.05
% 5.20/1.99  Subsumption          : 0.24
% 5.20/1.99  Abstraction          : 0.05
% 5.20/1.99  MUC search           : 0.00
% 5.20/1.99  Cooper               : 0.00
% 5.20/1.99  Total                : 1.20
% 5.20/1.99  Index Insertion      : 0.00
% 5.20/1.99  Index Deletion       : 0.00
% 5.20/1.99  Index Matching       : 0.00
% 5.20/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
