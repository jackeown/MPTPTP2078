%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 142 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

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

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(k2_funcop_1(A,B))
      & v4_relat_1(k2_funcop_1(A,B),A)
      & v1_funct_1(k2_funcop_1(A,B))
      & v1_partfun1(k2_funcop_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).

tff(f_52,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(c_22,plain,(
    ! [A_6] : v1_relat_1('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_6] : v1_funct_1('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_6] : v1_partfun1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_6] : v4_relat_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_partfun1(A_30,k1_xboole_0)
      | ~ v1_funct_1(A_30)
      | ~ v4_relat_1(A_30,k1_xboole_0)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_84,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_16,c_78])).

tff(c_14,plain,(
    ! [A_6] : v1_yellow_1('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [A_31] :
      ( k5_yellow_1(k1_xboole_0,A_31) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_31)
      | ~ v1_partfun1(A_31,k1_xboole_0)
      | ~ v1_funct_1(A_31)
      | ~ v4_relat_1(A_31,k1_xboole_0)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_91,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_1'(k1_xboole_0))
    | ~ v1_yellow_1('#skF_1'(k1_xboole_0))
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_97,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_1'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_16,c_14,c_91])).

tff(c_160,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_funcop_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_4,B_5] : v1_funct_1(k2_funcop_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_4,B_5] : v1_partfun1(k2_funcop_1(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_4,B_5] : v4_relat_1(k2_funcop_1(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [B_5] :
      ( k2_funcop_1(k1_xboole_0,B_5) = k1_xboole_0
      | ~ v1_partfun1(k2_funcop_1(k1_xboole_0,B_5),k1_xboole_0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,B_5))
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,B_5)) ) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_126,plain,(
    ! [B_32] : k2_funcop_1(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_12,c_74])).

tff(c_24,plain,(
    ! [A_8,B_9] : k7_funcop_1(A_8,B_9) = k2_funcop_1(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k5_yellow_1(A_2,k7_funcop_1(A_2,B_3)) = k6_yellow_1(A_2,B_3)
      | ~ l1_orders_2(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_2,B_3] :
      ( k5_yellow_1(A_2,k2_funcop_1(A_2,B_3)) = k6_yellow_1(A_2,B_3)
      | ~ l1_orders_2(B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_150,plain,(
    ! [B_33] :
      ( k6_yellow_1(k1_xboole_0,B_33) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_33])).

tff(c_154,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_30,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_30])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.18  
% 2.06/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.19  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 2.06/1.19  
% 2.06/1.19  %Foreground sorts:
% 2.06/1.19  
% 2.06/1.19  
% 2.06/1.19  %Background operators:
% 2.06/1.19  
% 2.06/1.19  
% 2.06/1.19  %Foreground operators:
% 2.06/1.19  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.06/1.19  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.06/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.19  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.06/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.19  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.06/1.19  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.06/1.19  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.06/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.06/1.19  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.06/1.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.06/1.19  
% 2.06/1.20  tff(f_50, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 2.06/1.20  tff(f_62, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_pboole)).
% 2.06/1.20  tff(f_74, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.06/1.20  tff(f_79, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.06/1.20  tff(f_39, axiom, (![A, B]: (((v1_relat_1(k2_funcop_1(A, B)) & v4_relat_1(k2_funcop_1(A, B), A)) & v1_funct_1(k2_funcop_1(A, B))) & v1_partfun1(k2_funcop_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc20_funcop_1)).
% 2.06/1.20  tff(f_52, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.06/1.20  tff(f_31, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.06/1.20  tff(c_22, plain, (![A_6]: (v1_relat_1('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.20  tff(c_18, plain, (![A_6]: (v1_funct_1('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.20  tff(c_16, plain, (![A_6]: (v1_partfun1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.20  tff(c_20, plain, (![A_6]: (v4_relat_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.20  tff(c_70, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_partfun1(A_30, k1_xboole_0) | ~v1_funct_1(A_30) | ~v4_relat_1(A_30, k1_xboole_0) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.20  tff(c_78, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_70])).
% 2.06/1.20  tff(c_84, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_16, c_78])).
% 2.06/1.20  tff(c_14, plain, (![A_6]: (v1_yellow_1('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.20  tff(c_85, plain, (![A_31]: (k5_yellow_1(k1_xboole_0, A_31)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_31) | ~v1_partfun1(A_31, k1_xboole_0) | ~v1_funct_1(A_31) | ~v4_relat_1(A_31, k1_xboole_0) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.20  tff(c_91, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_1'(k1_xboole_0)) | ~v1_yellow_1('#skF_1'(k1_xboole_0)) | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_85])).
% 2.06/1.20  tff(c_97, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_1'(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_16, c_14, c_91])).
% 2.06/1.20  tff(c_160, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97])).
% 2.06/1.20  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.20  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_funcop_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.20  tff(c_10, plain, (![A_4, B_5]: (v1_funct_1(k2_funcop_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.20  tff(c_12, plain, (![A_4, B_5]: (v1_partfun1(k2_funcop_1(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.20  tff(c_8, plain, (![A_4, B_5]: (v4_relat_1(k2_funcop_1(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.20  tff(c_74, plain, (![B_5]: (k2_funcop_1(k1_xboole_0, B_5)=k1_xboole_0 | ~v1_partfun1(k2_funcop_1(k1_xboole_0, B_5), k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0, B_5)) | ~v1_relat_1(k2_funcop_1(k1_xboole_0, B_5)))), inference(resolution, [status(thm)], [c_8, c_70])).
% 2.06/1.20  tff(c_126, plain, (![B_32]: (k2_funcop_1(k1_xboole_0, B_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_12, c_74])).
% 2.06/1.20  tff(c_24, plain, (![A_8, B_9]: (k7_funcop_1(A_8, B_9)=k2_funcop_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.20  tff(c_4, plain, (![A_2, B_3]: (k5_yellow_1(A_2, k7_funcop_1(A_2, B_3))=k6_yellow_1(A_2, B_3) | ~l1_orders_2(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.20  tff(c_33, plain, (![A_2, B_3]: (k5_yellow_1(A_2, k2_funcop_1(A_2, B_3))=k6_yellow_1(A_2, B_3) | ~l1_orders_2(B_3))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4])).
% 2.06/1.20  tff(c_150, plain, (![B_33]: (k6_yellow_1(k1_xboole_0, B_33)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(B_33))), inference(superposition, [status(thm), theory('equality')], [c_126, c_33])).
% 2.06/1.20  tff(c_154, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.06/1.20  tff(c_30, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.20  tff(c_155, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_30])).
% 2.06/1.20  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_155])).
% 2.06/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.20  
% 2.06/1.20  Inference rules
% 2.06/1.20  ----------------------
% 2.06/1.20  #Ref     : 0
% 2.06/1.20  #Sup     : 31
% 2.06/1.20  #Fact    : 0
% 2.06/1.20  #Define  : 0
% 2.06/1.20  #Split   : 0
% 2.06/1.20  #Chain   : 0
% 2.06/1.20  #Close   : 0
% 2.06/1.20  
% 2.06/1.20  Ordering : KBO
% 2.06/1.20  
% 2.06/1.20  Simplification rules
% 2.06/1.20  ----------------------
% 2.06/1.20  #Subsume      : 0
% 2.06/1.20  #Demod        : 27
% 2.06/1.20  #Tautology    : 19
% 2.06/1.20  #SimpNegUnit  : 0
% 2.06/1.20  #BackRed      : 2
% 2.06/1.20  
% 2.06/1.20  #Partial instantiations: 0
% 2.06/1.20  #Strategies tried      : 1
% 2.06/1.20  
% 2.06/1.20  Timing (in seconds)
% 2.06/1.20  ----------------------
% 2.06/1.20  Preprocessing        : 0.29
% 2.06/1.20  Parsing              : 0.15
% 2.06/1.20  CNF conversion       : 0.02
% 2.06/1.20  Main loop            : 0.14
% 2.06/1.20  Inferencing          : 0.05
% 2.06/1.20  Reduction            : 0.05
% 2.06/1.20  Demodulation         : 0.04
% 2.06/1.20  BG Simplification    : 0.01
% 2.06/1.20  Subsumption          : 0.02
% 2.06/1.20  Abstraction          : 0.01
% 2.06/1.20  MUC search           : 0.00
% 2.06/1.20  Cooper               : 0.00
% 2.06/1.20  Total                : 0.46
% 2.06/1.20  Index Insertion      : 0.00
% 2.06/1.20  Index Deletion       : 0.00
% 2.06/1.20  Index Matching       : 0.00
% 2.06/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
