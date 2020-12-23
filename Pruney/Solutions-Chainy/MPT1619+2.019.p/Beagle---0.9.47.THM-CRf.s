%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 122 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 150 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_yellow_1,type,(
    k6_yellow_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_66,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_56,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v1_funct_1(k6_relat_1(A))
      & v1_partfun1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [A_19] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_107,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35),A_35)
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_116,plain,(
    ! [A_19] : k2_funcop_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_32,plain,(
    ! [A_20,B_21] : k7_funcop_1(A_20,B_21) = k2_funcop_1(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( k5_yellow_1(A_15,k7_funcop_1(A_15,B_16)) = k6_yellow_1(A_15,B_16)
      | ~ l1_orders_2(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,(
    ! [A_47,B_48] :
      ( k5_yellow_1(A_47,k2_funcop_1(A_47,B_48)) = k6_yellow_1(A_47,B_48)
      | ~ l1_orders_2(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_177,plain,(
    ! [A_49] :
      ( k6_yellow_1(k1_xboole_0,A_49) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_165])).

tff(c_181,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_3') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_36,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_182,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_36])).

tff(c_50,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_24,plain,(
    ! [A_14] : k6_relat_1(A_14) = k6_partfun1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_43,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_43])).

tff(c_20,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_13] : v1_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20])).

tff(c_70,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_41])).

tff(c_22,plain,(
    ! [A_13] : v1_partfun1(k6_relat_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_28] : v1_partfun1(k6_partfun1(A_28),A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_82,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_79])).

tff(c_130,plain,(
    ! [A_38,B_39] :
      ( v1_yellow_1(k2_funcop_1(A_38,B_39))
      | ~ l1_orders_2(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    ! [A_19] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_130])).

tff(c_134,plain,(
    ! [A_19] : ~ l1_orders_2(A_19) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_38])).

tff(c_146,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_18,plain,(
    ! [A_13] : v4_relat_1(k6_relat_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_27] : v4_relat_1(k6_partfun1(A_27),A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18])).

tff(c_78,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_75])).

tff(c_187,plain,(
    ! [A_50] :
      ( k5_yellow_1(k1_xboole_0,A_50) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_50)
      | ~ v1_partfun1(A_50,k1_xboole_0)
      | ~ v1_funct_1(A_50)
      | ~ v4_relat_1(A_50,k1_xboole_0)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_189,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78,c_187])).

tff(c_195,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_82,c_146,c_189])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  %$ v4_relat_1 > v1_partfun1 > r2_hidden > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 2.13/1.24  
% 2.13/1.24  %Foreground sorts:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Background operators:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Foreground operators:
% 2.13/1.24  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.13/1.24  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.13/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.24  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.13/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.24  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.13/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.24  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.13/1.24  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.13/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.13/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.13/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.13/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.24  
% 2.13/1.25  tff(f_85, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.13/1.25  tff(f_66, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.13/1.25  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.13/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.25  tff(f_68, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.13/1.25  tff(f_60, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.13/1.25  tff(f_56, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.13/1.25  tff(f_46, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.13/1.25  tff(f_54, axiom, (![A]: (((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v1_funct_1(k6_relat_1(A))) & v1_partfun1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_funct_2)).
% 2.13/1.25  tff(f_64, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.13/1.25  tff(f_80, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.13/1.25  tff(c_38, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.25  tff(c_30, plain, (![A_19]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.25  tff(c_107, plain, (![A_35]: (r2_hidden('#skF_2'(A_35), A_35) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.25  tff(c_112, plain, (![A_36]: (~v1_xboole_0(A_36) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.13/1.25  tff(c_116, plain, (![A_19]: (k2_funcop_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_112])).
% 2.13/1.25  tff(c_32, plain, (![A_20, B_21]: (k7_funcop_1(A_20, B_21)=k2_funcop_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.25  tff(c_26, plain, (![A_15, B_16]: (k5_yellow_1(A_15, k7_funcop_1(A_15, B_16))=k6_yellow_1(A_15, B_16) | ~l1_orders_2(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.25  tff(c_165, plain, (![A_47, B_48]: (k5_yellow_1(A_47, k2_funcop_1(A_47, B_48))=k6_yellow_1(A_47, B_48) | ~l1_orders_2(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.13/1.25  tff(c_177, plain, (![A_49]: (k6_yellow_1(k1_xboole_0, A_49)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_116, c_165])).
% 2.13/1.25  tff(c_181, plain, (k6_yellow_1(k1_xboole_0, '#skF_3')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_177])).
% 2.13/1.25  tff(c_36, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.25  tff(c_182, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_36])).
% 2.13/1.25  tff(c_50, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.25  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.25  tff(c_56, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_14])).
% 2.13/1.25  tff(c_24, plain, (![A_14]: (k6_relat_1(A_14)=k6_partfun1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.25  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_43, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 2.13/1.25  tff(c_68, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_43])).
% 2.13/1.25  tff(c_20, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_41, plain, (![A_13]: (v1_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20])).
% 2.13/1.25  tff(c_70, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_41])).
% 2.13/1.25  tff(c_22, plain, (![A_13]: (v1_partfun1(k6_relat_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_79, plain, (![A_28]: (v1_partfun1(k6_partfun1(A_28), A_28))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 2.13/1.25  tff(c_82, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_79])).
% 2.13/1.25  tff(c_130, plain, (![A_38, B_39]: (v1_yellow_1(k2_funcop_1(A_38, B_39)) | ~l1_orders_2(B_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.25  tff(c_133, plain, (![A_19]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_19))), inference(superposition, [status(thm), theory('equality')], [c_116, c_130])).
% 2.13/1.25  tff(c_134, plain, (![A_19]: (~l1_orders_2(A_19))), inference(splitLeft, [status(thm)], [c_133])).
% 2.13/1.25  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_38])).
% 2.13/1.25  tff(c_146, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_133])).
% 2.13/1.25  tff(c_18, plain, (![A_13]: (v4_relat_1(k6_relat_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_75, plain, (![A_27]: (v4_relat_1(k6_partfun1(A_27), A_27))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18])).
% 2.13/1.25  tff(c_78, plain, (v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_75])).
% 2.13/1.25  tff(c_187, plain, (![A_50]: (k5_yellow_1(k1_xboole_0, A_50)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_50) | ~v1_partfun1(A_50, k1_xboole_0) | ~v1_funct_1(A_50) | ~v4_relat_1(A_50, k1_xboole_0) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.25  tff(c_189, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_187])).
% 2.13/1.25  tff(c_195, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_82, c_146, c_189])).
% 2.13/1.25  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_195])).
% 2.13/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  Inference rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Ref     : 0
% 2.13/1.25  #Sup     : 37
% 2.13/1.25  #Fact    : 0
% 2.13/1.25  #Define  : 0
% 2.13/1.25  #Split   : 1
% 2.13/1.25  #Chain   : 0
% 2.13/1.25  #Close   : 0
% 2.13/1.25  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 1
% 2.13/1.25  #Demod        : 12
% 2.13/1.25  #Tautology    : 25
% 2.13/1.25  #SimpNegUnit  : 2
% 2.13/1.25  #BackRed      : 3
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.26  Preprocessing        : 0.31
% 2.13/1.26  Parsing              : 0.16
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.17
% 2.13/1.26  Inferencing          : 0.06
% 2.13/1.26  Reduction            : 0.06
% 2.13/1.26  Demodulation         : 0.04
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.02
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.52
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
