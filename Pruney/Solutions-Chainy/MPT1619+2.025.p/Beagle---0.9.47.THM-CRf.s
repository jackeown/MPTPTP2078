%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 150 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_63,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_65,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_53,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v1_funct_1(k6_relat_1(A))
      & v1_partfun1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_38,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_19] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_102,plain,(
    ! [B_34,A_35] :
      ( ~ v1_xboole_0(B_34)
      | B_34 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_109,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_116,plain,(
    ! [A_19] : k2_funcop_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_32,plain,(
    ! [A_20,B_21] : k7_funcop_1(A_20,B_21) = k2_funcop_1(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( k5_yellow_1(A_15,k7_funcop_1(A_15,B_16)) = k6_yellow_1(A_15,B_16)
      | ~ l1_orders_2(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    ! [A_43,B_44] :
      ( k5_yellow_1(A_43,k2_funcop_1(A_43,B_44)) = k6_yellow_1(A_43,B_44)
      | ~ l1_orders_2(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_175,plain,(
    ! [A_49] :
      ( k6_yellow_1(k1_xboole_0,A_49) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_154])).

tff(c_179,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_36,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_180,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_36])).

tff(c_53,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_24,plain,(
    ! [A_14] : k6_relat_1(A_14) = k6_partfun1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_43])).

tff(c_20,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    ! [A_13] : v1_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20])).

tff(c_78,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_41])).

tff(c_22,plain,(
    ! [A_13] : v1_partfun1(k6_relat_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_13] : v1_partfun1(k6_partfun1(A_13),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_74,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_40])).

tff(c_121,plain,(
    ! [A_37] : k2_funcop_1(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( v1_yellow_1(k2_funcop_1(A_17,B_18))
      | ~ l1_orders_2(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,(
    ! [A_37] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_28])).

tff(c_131,plain,(
    ! [A_37] : ~ l1_orders_2(A_37) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_38])).

tff(c_134,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_18,plain,(
    ! [A_13] : v4_relat_1(k6_relat_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_13] : v4_relat_1(k6_partfun1(A_13),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18])).

tff(c_71,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_42])).

tff(c_185,plain,(
    ! [A_50] :
      ( k5_yellow_1(k1_xboole_0,A_50) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_50)
      | ~ v1_partfun1(A_50,k1_xboole_0)
      | ~ v1_funct_1(A_50)
      | ~ v4_relat_1(A_50,k1_xboole_0)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_187,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_71,c_185])).

tff(c_193,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_74,c_134,c_187])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.31  
% 1.95/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.31  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.95/1.31  
% 1.95/1.31  %Foreground sorts:
% 1.95/1.31  
% 1.95/1.31  
% 1.95/1.31  %Background operators:
% 1.95/1.31  
% 1.95/1.31  
% 1.95/1.31  %Foreground operators:
% 1.95/1.31  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.95/1.31  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.95/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.31  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.95/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.31  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.95/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.31  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.95/1.31  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.95/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.95/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.95/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.31  
% 2.24/1.33  tff(f_82, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.24/1.33  tff(f_63, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.24/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.33  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.24/1.33  tff(f_65, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.24/1.33  tff(f_57, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.24/1.33  tff(f_53, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.24/1.33  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.24/1.33  tff(f_51, axiom, (![A]: (((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v1_funct_1(k6_relat_1(A))) & v1_partfun1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_funct_2)).
% 2.24/1.33  tff(f_61, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.24/1.33  tff(f_77, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.24/1.33  tff(c_38, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.33  tff(c_30, plain, (![A_19]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.33  tff(c_102, plain, (![B_34, A_35]: (~v1_xboole_0(B_34) | B_34=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.33  tff(c_109, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_102])).
% 2.24/1.33  tff(c_116, plain, (![A_19]: (k2_funcop_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_109])).
% 2.24/1.33  tff(c_32, plain, (![A_20, B_21]: (k7_funcop_1(A_20, B_21)=k2_funcop_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.33  tff(c_26, plain, (![A_15, B_16]: (k5_yellow_1(A_15, k7_funcop_1(A_15, B_16))=k6_yellow_1(A_15, B_16) | ~l1_orders_2(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.33  tff(c_154, plain, (![A_43, B_44]: (k5_yellow_1(A_43, k2_funcop_1(A_43, B_44))=k6_yellow_1(A_43, B_44) | ~l1_orders_2(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.24/1.33  tff(c_175, plain, (![A_49]: (k6_yellow_1(k1_xboole_0, A_49)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_116, c_154])).
% 2.24/1.33  tff(c_179, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_175])).
% 2.24/1.33  tff(c_36, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.33  tff(c_180, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_36])).
% 2.24/1.33  tff(c_53, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.33  tff(c_59, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_53, c_14])).
% 2.24/1.33  tff(c_24, plain, (![A_14]: (k6_relat_1(A_14)=k6_partfun1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.33  tff(c_43, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 2.24/1.33  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_43])).
% 2.24/1.33  tff(c_20, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.33  tff(c_41, plain, (![A_13]: (v1_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20])).
% 2.24/1.33  tff(c_78, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_41])).
% 2.24/1.33  tff(c_22, plain, (![A_13]: (v1_partfun1(k6_relat_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.33  tff(c_40, plain, (![A_13]: (v1_partfun1(k6_partfun1(A_13), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 2.24/1.33  tff(c_74, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_40])).
% 2.24/1.33  tff(c_121, plain, (![A_37]: (k2_funcop_1(k1_xboole_0, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_109])).
% 2.24/1.33  tff(c_28, plain, (![A_17, B_18]: (v1_yellow_1(k2_funcop_1(A_17, B_18)) | ~l1_orders_2(B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.33  tff(c_126, plain, (![A_37]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_37))), inference(superposition, [status(thm), theory('equality')], [c_121, c_28])).
% 2.24/1.33  tff(c_131, plain, (![A_37]: (~l1_orders_2(A_37))), inference(splitLeft, [status(thm)], [c_126])).
% 2.24/1.33  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_38])).
% 2.24/1.33  tff(c_134, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 2.24/1.33  tff(c_18, plain, (![A_13]: (v4_relat_1(k6_relat_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.33  tff(c_42, plain, (![A_13]: (v4_relat_1(k6_partfun1(A_13), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18])).
% 2.24/1.33  tff(c_71, plain, (v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_42])).
% 2.24/1.33  tff(c_185, plain, (![A_50]: (k5_yellow_1(k1_xboole_0, A_50)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_50) | ~v1_partfun1(A_50, k1_xboole_0) | ~v1_funct_1(A_50) | ~v4_relat_1(A_50, k1_xboole_0) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.33  tff(c_187, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_185])).
% 2.24/1.33  tff(c_193, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_74, c_134, c_187])).
% 2.24/1.33  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_193])).
% 2.24/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  Inference rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Ref     : 0
% 2.24/1.33  #Sup     : 37
% 2.24/1.33  #Fact    : 0
% 2.24/1.33  #Define  : 0
% 2.24/1.33  #Split   : 1
% 2.24/1.33  #Chain   : 0
% 2.24/1.33  #Close   : 0
% 2.24/1.33  
% 2.24/1.33  Ordering : KBO
% 2.24/1.33  
% 2.24/1.33  Simplification rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Subsume      : 2
% 2.24/1.33  #Demod        : 14
% 2.24/1.33  #Tautology    : 25
% 2.24/1.33  #SimpNegUnit  : 2
% 2.24/1.33  #BackRed      : 3
% 2.24/1.33  
% 2.24/1.33  #Partial instantiations: 0
% 2.24/1.33  #Strategies tried      : 1
% 2.24/1.33  
% 2.24/1.33  Timing (in seconds)
% 2.24/1.33  ----------------------
% 2.24/1.33  Preprocessing        : 0.34
% 2.24/1.33  Parsing              : 0.18
% 2.24/1.33  CNF conversion       : 0.02
% 2.24/1.33  Main loop            : 0.16
% 2.24/1.33  Inferencing          : 0.06
% 2.24/1.33  Reduction            : 0.05
% 2.24/1.33  Demodulation         : 0.04
% 2.24/1.33  BG Simplification    : 0.01
% 2.24/1.33  Subsumption          : 0.02
% 2.24/1.33  Abstraction          : 0.01
% 2.24/1.33  MUC search           : 0.00
% 2.24/1.33  Cooper               : 0.00
% 2.24/1.33  Total                : 0.54
% 2.24/1.33  Index Insertion      : 0.00
% 2.24/1.33  Index Deletion       : 0.00
% 2.24/1.33  Index Matching       : 0.00
% 2.24/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
