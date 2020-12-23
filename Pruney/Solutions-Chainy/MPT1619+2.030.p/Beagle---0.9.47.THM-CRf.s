%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 113 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_yellow_1,type,(
    k6_yellow_1: ( $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v1_yellow_1,type,(
    v1_yellow_1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_39,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(c_20,plain,(
    ! [A_8] : v1_relat_1('#skF_1'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_8] : v1_funct_1('#skF_1'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_8] : v1_partfun1('#skF_1'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_8] : v1_yellow_1('#skF_1'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_8] : v4_relat_1('#skF_1'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_partfun1(A_29,k1_xboole_0)
      | ~ v1_funct_1(A_29)
      | ~ v4_relat_1(A_29,k1_xboole_0)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_102,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_14,c_99])).

tff(c_119,plain,(
    ! [A_30] :
      ( k5_yellow_1(k1_xboole_0,A_30) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_30)
      | ~ v1_partfun1(A_30,k1_xboole_0)
      | ~ v1_funct_1(A_30)
      | ~ v4_relat_1(A_30,k1_xboole_0)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_122,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_1'(k1_xboole_0))
    | ~ v1_yellow_1('#skF_1'(k1_xboole_0))
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_125,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_14,c_12,c_102,c_122])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [A_20] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_20] : k2_funcop_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_22,plain,(
    ! [A_10,B_11] : k7_funcop_1(A_10,B_11) = k2_funcop_1(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k5_yellow_1(A_5,k7_funcop_1(A_5,B_6)) = k6_yellow_1(A_5,B_6)
      | ~ l1_orders_2(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [A_27,B_28] :
      ( k5_yellow_1(A_27,k2_funcop_1(A_27,B_28)) = k6_yellow_1(A_27,B_28)
      | ~ l1_orders_2(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_138,plain,(
    ! [A_31] :
      ( k6_yellow_1(k1_xboole_0,A_31) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_142,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_28,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_143,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_28])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.90/1.18  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.90/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.18  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.90/1.18  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.90/1.18  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.90/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.90/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.90/1.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.90/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.18  
% 1.90/1.19  tff(f_50, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_yellow_1)).
% 1.90/1.19  tff(f_62, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_pboole)).
% 1.90/1.19  tff(f_74, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 1.90/1.19  tff(f_79, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 1.90/1.19  tff(f_39, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 1.90/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.90/1.19  tff(f_52, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 1.90/1.19  tff(f_37, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 1.90/1.19  tff(c_20, plain, (![A_8]: (v1_relat_1('#skF_1'(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_16, plain, (![A_8]: (v1_funct_1('#skF_1'(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_14, plain, (![A_8]: (v1_partfun1('#skF_1'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_12, plain, (![A_8]: (v1_yellow_1('#skF_1'(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_18, plain, (![A_8]: (v4_relat_1('#skF_1'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_95, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_partfun1(A_29, k1_xboole_0) | ~v1_funct_1(A_29) | ~v4_relat_1(A_29, k1_xboole_0) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.19  tff(c_99, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_95])).
% 1.90/1.19  tff(c_102, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_99])).
% 1.90/1.19  tff(c_119, plain, (![A_30]: (k5_yellow_1(k1_xboole_0, A_30)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_30) | ~v1_partfun1(A_30, k1_xboole_0) | ~v1_funct_1(A_30) | ~v4_relat_1(A_30, k1_xboole_0) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.90/1.19  tff(c_122, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_1'(k1_xboole_0)) | ~v1_yellow_1('#skF_1'(k1_xboole_0)) | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_119])).
% 1.90/1.19  tff(c_125, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_12, c_102, c_122])).
% 1.90/1.19  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.90/1.19  tff(c_38, plain, (![A_20]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_20)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.19  tff(c_42, plain, (![A_20]: (k2_funcop_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.90/1.19  tff(c_22, plain, (![A_10, B_11]: (k7_funcop_1(A_10, B_11)=k2_funcop_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.19  tff(c_8, plain, (![A_5, B_6]: (k5_yellow_1(A_5, k7_funcop_1(A_5, B_6))=k6_yellow_1(A_5, B_6) | ~l1_orders_2(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.19  tff(c_83, plain, (![A_27, B_28]: (k5_yellow_1(A_27, k2_funcop_1(A_27, B_28))=k6_yellow_1(A_27, B_28) | ~l1_orders_2(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8])).
% 1.90/1.19  tff(c_138, plain, (![A_31]: (k6_yellow_1(k1_xboole_0, A_31)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_31))), inference(superposition, [status(thm), theory('equality')], [c_42, c_83])).
% 1.90/1.19  tff(c_142, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_138])).
% 1.90/1.19  tff(c_28, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.90/1.19  tff(c_143, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_28])).
% 1.90/1.19  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_143])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 0
% 1.90/1.19  #Sup     : 29
% 1.90/1.19  #Fact    : 0
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 0
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 0
% 1.90/1.19  #Demod        : 21
% 1.90/1.19  #Tautology    : 19
% 1.90/1.19  #SimpNegUnit  : 0
% 1.90/1.19  #BackRed      : 3
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.19  Preprocessing        : 0.29
% 1.90/1.19  Parsing              : 0.16
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.13
% 1.90/1.19  Inferencing          : 0.05
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
