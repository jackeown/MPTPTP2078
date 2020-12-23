%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 132 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_54,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_44,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_34,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v1_funct_1(k6_relat_1(A))
      & v1_partfun1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_32,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_77,plain,(
    ! [A_21] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_21] : k2_funcop_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_26,plain,(
    ! [A_12,B_13] : k7_funcop_1(A_12,B_13) = k2_funcop_1(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k5_yellow_1(A_7,k7_funcop_1(A_7,B_8)) = k6_yellow_1(A_7,B_8)
      | ~ l1_orders_2(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [A_30,B_31] :
      ( k5_yellow_1(A_30,k2_funcop_1(A_30,B_31)) = k6_yellow_1(A_30,B_31)
      | ~ l1_orders_2(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_142,plain,(
    ! [A_32] :
      ( k6_yellow_1(k1_xboole_0,A_32) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_130])).

tff(c_146,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_142])).

tff(c_30,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_30])).

tff(c_44,plain,(
    ! [A_17] : k6_relat_1(A_17) = k6_partfun1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_18,plain,(
    ! [A_6] : k6_relat_1(A_6) = k6_partfun1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_37])).

tff(c_14,plain,(
    ! [A_5] : v1_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [A_5] : v1_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_67,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_35])).

tff(c_16,plain,(
    ! [A_5] : v1_partfun1(k6_relat_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_5] : v1_partfun1(k6_partfun1(A_5),A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_63,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_104,plain,(
    ! [A_24,B_25] :
      ( v1_yellow_1(k2_funcop_1(A_24,B_25))
      | ~ l1_orders_2(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_21] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_104])).

tff(c_108,plain,(
    ! [A_21] : ~ l1_orders_2(A_21) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_32])).

tff(c_111,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_12,plain,(
    ! [A_5] : v4_relat_1(k6_relat_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [A_19] : v4_relat_1(k6_partfun1(A_19),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12])).

tff(c_75,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_72])).

tff(c_152,plain,(
    ! [A_33] :
      ( k5_yellow_1(k1_xboole_0,A_33) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_33)
      | ~ v1_partfun1(A_33,k1_xboole_0)
      | ~ v1_funct_1(A_33)
      | ~ v4_relat_1(A_33,k1_xboole_0)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_75,c_152])).

tff(c_160,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_67,c_63,c_111,c_154])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.88/1.18  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.88/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.88/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.18  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.88/1.18  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.88/1.18  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.88/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.88/1.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.88/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.18  
% 1.88/1.19  tff(f_73, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 1.88/1.19  tff(f_54, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 1.88/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.88/1.19  tff(f_56, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 1.88/1.19  tff(f_48, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 1.88/1.19  tff(f_44, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.88/1.19  tff(f_34, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.88/1.19  tff(f_42, axiom, (![A]: (((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v1_funct_1(k6_relat_1(A))) & v1_partfun1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_funct_2)).
% 1.88/1.19  tff(f_52, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 1.88/1.19  tff(f_68, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 1.88/1.19  tff(c_32, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.19  tff(c_77, plain, (![A_21]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_21)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.19  tff(c_81, plain, (![A_21]: (k2_funcop_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_2])).
% 1.88/1.19  tff(c_26, plain, (![A_12, B_13]: (k7_funcop_1(A_12, B_13)=k2_funcop_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.19  tff(c_20, plain, (![A_7, B_8]: (k5_yellow_1(A_7, k7_funcop_1(A_7, B_8))=k6_yellow_1(A_7, B_8) | ~l1_orders_2(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.19  tff(c_130, plain, (![A_30, B_31]: (k5_yellow_1(A_30, k2_funcop_1(A_30, B_31))=k6_yellow_1(A_30, B_31) | ~l1_orders_2(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 1.88/1.19  tff(c_142, plain, (![A_32]: (k6_yellow_1(k1_xboole_0, A_32)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_32))), inference(superposition, [status(thm), theory('equality')], [c_81, c_130])).
% 1.88/1.19  tff(c_146, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_142])).
% 1.88/1.19  tff(c_30, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.19  tff(c_147, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_30])).
% 1.88/1.19  tff(c_44, plain, (![A_17]: (k6_relat_1(A_17)=k6_partfun1(A_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.19  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.19  tff(c_50, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44, c_8])).
% 1.88/1.19  tff(c_18, plain, (![A_6]: (k6_relat_1(A_6)=k6_partfun1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.19  tff(c_10, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_37, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10])).
% 1.88/1.19  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_37])).
% 1.88/1.19  tff(c_14, plain, (![A_5]: (v1_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_35, plain, (![A_5]: (v1_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 1.88/1.19  tff(c_67, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_35])).
% 1.88/1.19  tff(c_16, plain, (![A_5]: (v1_partfun1(k6_relat_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_34, plain, (![A_5]: (v1_partfun1(k6_partfun1(A_5), A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 1.88/1.19  tff(c_63, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_34])).
% 1.88/1.19  tff(c_104, plain, (![A_24, B_25]: (v1_yellow_1(k2_funcop_1(A_24, B_25)) | ~l1_orders_2(B_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.19  tff(c_107, plain, (![A_21]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_21))), inference(superposition, [status(thm), theory('equality')], [c_81, c_104])).
% 1.88/1.19  tff(c_108, plain, (![A_21]: (~l1_orders_2(A_21))), inference(splitLeft, [status(thm)], [c_107])).
% 1.88/1.19  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_32])).
% 1.88/1.19  tff(c_111, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_107])).
% 1.88/1.19  tff(c_12, plain, (![A_5]: (v4_relat_1(k6_relat_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.19  tff(c_72, plain, (![A_19]: (v4_relat_1(k6_partfun1(A_19), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12])).
% 1.88/1.19  tff(c_75, plain, (v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_72])).
% 1.88/1.19  tff(c_152, plain, (![A_33]: (k5_yellow_1(k1_xboole_0, A_33)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_33) | ~v1_partfun1(A_33, k1_xboole_0) | ~v1_funct_1(A_33) | ~v4_relat_1(A_33, k1_xboole_0) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.19  tff(c_154, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_152])).
% 1.88/1.19  tff(c_160, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_67, c_63, c_111, c_154])).
% 1.88/1.19  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_160])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 31
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 1
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 1
% 1.88/1.19  #Demod        : 12
% 1.88/1.19  #Tautology    : 20
% 1.88/1.19  #SimpNegUnit  : 2
% 1.88/1.19  #BackRed      : 3
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.20  Preprocessing        : 0.29
% 1.88/1.20  Parsing              : 0.15
% 1.88/1.20  CNF conversion       : 0.02
% 1.88/1.20  Main loop            : 0.15
% 1.88/1.20  Inferencing          : 0.05
% 1.88/1.20  Reduction            : 0.05
% 1.88/1.20  Demodulation         : 0.04
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.20  Subsumption          : 0.02
% 1.88/1.20  Abstraction          : 0.01
% 1.88/1.20  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.47
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.88/1.20  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
