%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:40 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 125 expanded)
%              Number of leaves         :   45 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 159 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r1_tarski > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_82,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_54,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [A_35] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_108,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_115,plain,(
    ! [A_35] : k2_funcop_1(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_48,plain,(
    ! [A_36,B_37] : k7_funcop_1(A_36,B_37) = k2_funcop_1(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( k5_yellow_1(A_31,k7_funcop_1(A_31,B_32)) = k6_yellow_1(A_31,B_32)
      | ~ l1_orders_2(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_206,plain,(
    ! [A_64,B_65] :
      ( k5_yellow_1(A_64,k2_funcop_1(A_64,B_65)) = k6_yellow_1(A_64,B_65)
      | ~ l1_orders_2(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_218,plain,(
    ! [A_66] :
      ( k6_yellow_1(k1_xboole_0,A_66) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_206])).

tff(c_222,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_54,c_218])).

tff(c_52,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_236,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_73,plain,(
    ! [A_42] :
      ( v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_78,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_30])).

tff(c_40,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_27] : v1_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ! [A_27] : v1_funct_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_97,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_56])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [B_60,A_61] :
      ( v4_relat_1(B_60,A_61)
      | ~ r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_186,plain,(
    ! [A_61] :
      ( v4_relat_1(k1_xboole_0,A_61)
      | ~ r1_tarski(k1_xboole_0,A_61)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_180])).

tff(c_196,plain,(
    ! [A_63] : v4_relat_1(k1_xboole_0,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6,c_186])).

tff(c_36,plain,(
    ! [B_29] :
      ( v1_partfun1(B_29,k1_relat_1(B_29))
      | ~ v4_relat_1(B_29,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_200,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_196,c_36])).

tff(c_203,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_28,c_200])).

tff(c_139,plain,(
    ! [A_49,B_50] :
      ( v1_yellow_1(k2_funcop_1(A_49,B_50))
      | ~ l1_orders_2(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    ! [A_35] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_139])).

tff(c_143,plain,(
    ! [A_35] : ~ l1_orders_2(A_35) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_54])).

tff(c_146,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_189,plain,(
    ! [A_61] : v4_relat_1(k1_xboole_0,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6,c_186])).

tff(c_268,plain,(
    ! [A_85] :
      ( k5_yellow_1(k1_xboole_0,A_85) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_85)
      | ~ v1_partfun1(A_85,k1_xboole_0)
      | ~ v1_funct_1(A_85)
      | ~ v4_relat_1(A_85,k1_xboole_0)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_271,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_189,c_268])).

tff(c_274,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_97,c_203,c_146,c_271])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.24  
% 2.26/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.24  %$ v4_relat_1 > v1_partfun1 > r1_tarski > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.26/1.24  
% 2.26/1.24  %Foreground sorts:
% 2.26/1.24  
% 2.26/1.24  
% 2.26/1.24  %Background operators:
% 2.26/1.24  
% 2.26/1.24  
% 2.26/1.24  %Foreground operators:
% 2.26/1.24  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.26/1.24  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.26/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.24  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.26/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.24  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.26/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.24  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.26/1.24  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.26/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.26/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.26/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.26/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.26/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.24  
% 2.26/1.25  tff(f_101, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.26/1.25  tff(f_82, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.26/1.25  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.26/1.25  tff(f_84, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.26/1.25  tff(f_76, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.26/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.25  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.26/1.25  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.26/1.25  tff(f_58, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.26/1.25  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.26/1.25  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.25  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.26/1.25  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.26/1.25  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.26/1.25  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.26/1.25  tff(f_96, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.26/1.25  tff(c_54, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.26/1.25  tff(c_46, plain, (![A_35]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_35)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.25  tff(c_108, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.26/1.25  tff(c_115, plain, (![A_35]: (k2_funcop_1(k1_xboole_0, A_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_108])).
% 2.26/1.25  tff(c_48, plain, (![A_36, B_37]: (k7_funcop_1(A_36, B_37)=k2_funcop_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.26/1.25  tff(c_42, plain, (![A_31, B_32]: (k5_yellow_1(A_31, k7_funcop_1(A_31, B_32))=k6_yellow_1(A_31, B_32) | ~l1_orders_2(B_32))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.26/1.25  tff(c_206, plain, (![A_64, B_65]: (k5_yellow_1(A_64, k2_funcop_1(A_64, B_65))=k6_yellow_1(A_64, B_65) | ~l1_orders_2(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 2.26/1.25  tff(c_218, plain, (![A_66]: (k6_yellow_1(k1_xboole_0, A_66)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_66))), inference(superposition, [status(thm), theory('equality')], [c_115, c_206])).
% 2.26/1.25  tff(c_222, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_218])).
% 2.26/1.25  tff(c_52, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.26/1.25  tff(c_236, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_52])).
% 2.26/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.25  tff(c_73, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.25  tff(c_77, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_73])).
% 2.26/1.25  tff(c_78, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.25  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.25  tff(c_84, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78, c_30])).
% 2.26/1.25  tff(c_40, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.25  tff(c_34, plain, (![A_27]: (v1_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.25  tff(c_56, plain, (![A_27]: (v1_funct_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 2.26/1.25  tff(c_97, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_56])).
% 2.26/1.25  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.26/1.25  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.25  tff(c_180, plain, (![B_60, A_61]: (v4_relat_1(B_60, A_61) | ~r1_tarski(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.25  tff(c_186, plain, (![A_61]: (v4_relat_1(k1_xboole_0, A_61) | ~r1_tarski(k1_xboole_0, A_61) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_180])).
% 2.26/1.25  tff(c_196, plain, (![A_63]: (v4_relat_1(k1_xboole_0, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6, c_186])).
% 2.26/1.25  tff(c_36, plain, (![B_29]: (v1_partfun1(B_29, k1_relat_1(B_29)) | ~v4_relat_1(B_29, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.25  tff(c_200, plain, (v1_partfun1(k1_xboole_0, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_36])).
% 2.26/1.25  tff(c_203, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_28, c_200])).
% 2.26/1.25  tff(c_139, plain, (![A_49, B_50]: (v1_yellow_1(k2_funcop_1(A_49, B_50)) | ~l1_orders_2(B_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.25  tff(c_142, plain, (![A_35]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_35))), inference(superposition, [status(thm), theory('equality')], [c_115, c_139])).
% 2.26/1.25  tff(c_143, plain, (![A_35]: (~l1_orders_2(A_35))), inference(splitLeft, [status(thm)], [c_142])).
% 2.26/1.25  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_54])).
% 2.26/1.25  tff(c_146, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_142])).
% 2.26/1.25  tff(c_189, plain, (![A_61]: (v4_relat_1(k1_xboole_0, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6, c_186])).
% 2.26/1.25  tff(c_268, plain, (![A_85]: (k5_yellow_1(k1_xboole_0, A_85)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_85) | ~v1_partfun1(A_85, k1_xboole_0) | ~v1_funct_1(A_85) | ~v4_relat_1(A_85, k1_xboole_0) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.25  tff(c_271, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_268])).
% 2.26/1.25  tff(c_274, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_97, c_203, c_146, c_271])).
% 2.26/1.25  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_274])).
% 2.26/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  Inference rules
% 2.26/1.25  ----------------------
% 2.26/1.25  #Ref     : 0
% 2.26/1.25  #Sup     : 49
% 2.26/1.25  #Fact    : 0
% 2.26/1.25  #Define  : 0
% 2.26/1.25  #Split   : 1
% 2.26/1.25  #Chain   : 0
% 2.26/1.25  #Close   : 0
% 2.26/1.25  
% 2.26/1.25  Ordering : KBO
% 2.26/1.25  
% 2.26/1.25  Simplification rules
% 2.26/1.25  ----------------------
% 2.26/1.25  #Subsume      : 1
% 2.26/1.25  #Demod        : 26
% 2.26/1.25  #Tautology    : 39
% 2.26/1.25  #SimpNegUnit  : 2
% 2.26/1.25  #BackRed      : 4
% 2.26/1.25  
% 2.26/1.25  #Partial instantiations: 0
% 2.26/1.25  #Strategies tried      : 1
% 2.26/1.25  
% 2.26/1.25  Timing (in seconds)
% 2.26/1.25  ----------------------
% 2.26/1.26  Preprocessing        : 0.31
% 2.26/1.26  Parsing              : 0.17
% 2.26/1.26  CNF conversion       : 0.02
% 2.26/1.26  Main loop            : 0.17
% 2.26/1.26  Inferencing          : 0.06
% 2.26/1.26  Reduction            : 0.06
% 2.26/1.26  Demodulation         : 0.04
% 2.26/1.26  BG Simplification    : 0.01
% 2.26/1.26  Subsumption          : 0.02
% 2.26/1.26  Abstraction          : 0.01
% 2.26/1.26  MUC search           : 0.00
% 2.26/1.26  Cooper               : 0.00
% 2.26/1.26  Total                : 0.52
% 2.26/1.26  Index Insertion      : 0.00
% 2.26/1.26  Index Deletion       : 0.00
% 2.26/1.26  Index Matching       : 0.00
% 2.26/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
