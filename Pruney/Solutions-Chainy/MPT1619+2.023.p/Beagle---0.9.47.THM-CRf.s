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

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 112 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_68,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_58,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_87,plain,(
    ! [A_50] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_50] : k2_funcop_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_40,plain,(
    ! [A_40,B_41] : k7_funcop_1(A_40,B_41) = k2_funcop_1(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_35,B_36] :
      ( k5_yellow_1(A_35,k7_funcop_1(A_35,B_36)) = k6_yellow_1(A_35,B_36)
      | ~ l1_orders_2(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_153,plain,(
    ! [A_63,B_64] :
      ( k5_yellow_1(A_63,k2_funcop_1(A_63,B_64)) = k6_yellow_1(A_63,B_64)
      | ~ l1_orders_2(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_174,plain,(
    ! [A_69] :
      ( k6_yellow_1(k1_xboole_0,A_69) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_153])).

tff(c_178,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_174])).

tff(c_44,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_179,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_44])).

tff(c_59,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_22])).

tff(c_32,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_49])).

tff(c_26,plain,(
    ! [A_32] : v1_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ! [A_32] : v1_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_81,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_28,plain,(
    ! [A_33] : v1_partfun1(k6_partfun1(A_33),A_33) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_28])).

tff(c_114,plain,(
    ! [A_53,B_54] :
      ( v1_yellow_1(k2_funcop_1(A_53,B_54))
      | ~ l1_orders_2(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,(
    ! [A_50] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_114])).

tff(c_118,plain,(
    ! [A_50] : ~ l1_orders_2(A_50) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_46])).

tff(c_121,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_18,plain,(
    ! [A_30] : v4_relat_1(k1_xboole_0,A_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [A_88] :
      ( k5_yellow_1(k1_xboole_0,A_88) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_88)
      | ~ v1_partfun1(A_88,k1_xboole_0)
      | ~ v1_funct_1(A_88)
      | ~ v4_relat_1(A_88,k1_xboole_0)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_211])).

tff(c_217,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_81,c_77,c_121,c_214])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.19/1.27  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.19/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.19/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.27  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.19/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.27  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.19/1.27  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.19/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.28  tff(f_87, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.19/1.28  tff(f_68, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.19/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.19/1.28  tff(f_70, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.19/1.28  tff(f_62, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.19/1.28  tff(f_58, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.19/1.28  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.19/1.28  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.19/1.28  tff(f_56, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.19/1.28  tff(f_66, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.19/1.28  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 2.19/1.28  tff(f_82, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.19/1.28  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.19/1.28  tff(c_87, plain, (![A_50]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_50)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.28  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.28  tff(c_91, plain, (![A_50]: (k2_funcop_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.19/1.28  tff(c_40, plain, (![A_40, B_41]: (k7_funcop_1(A_40, B_41)=k2_funcop_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.28  tff(c_34, plain, (![A_35, B_36]: (k5_yellow_1(A_35, k7_funcop_1(A_35, B_36))=k6_yellow_1(A_35, B_36) | ~l1_orders_2(B_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.28  tff(c_153, plain, (![A_63, B_64]: (k5_yellow_1(A_63, k2_funcop_1(A_63, B_64))=k6_yellow_1(A_63, B_64) | ~l1_orders_2(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 2.19/1.28  tff(c_174, plain, (![A_69]: (k6_yellow_1(k1_xboole_0, A_69)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_69))), inference(superposition, [status(thm), theory('equality')], [c_91, c_153])).
% 2.19/1.28  tff(c_178, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_174])).
% 2.19/1.28  tff(c_44, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.19/1.28  tff(c_179, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_44])).
% 2.19/1.28  tff(c_59, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.28  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.28  tff(c_65, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59, c_22])).
% 2.19/1.28  tff(c_32, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.28  tff(c_24, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.28  tff(c_49, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 2.19/1.28  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_49])).
% 2.19/1.28  tff(c_26, plain, (![A_32]: (v1_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.28  tff(c_48, plain, (![A_32]: (v1_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.19/1.28  tff(c_81, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_48])).
% 2.19/1.28  tff(c_28, plain, (![A_33]: (v1_partfun1(k6_partfun1(A_33), A_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.28  tff(c_77, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_28])).
% 2.19/1.28  tff(c_114, plain, (![A_53, B_54]: (v1_yellow_1(k2_funcop_1(A_53, B_54)) | ~l1_orders_2(B_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.28  tff(c_117, plain, (![A_50]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_50))), inference(superposition, [status(thm), theory('equality')], [c_91, c_114])).
% 2.19/1.28  tff(c_118, plain, (![A_50]: (~l1_orders_2(A_50))), inference(splitLeft, [status(thm)], [c_117])).
% 2.19/1.28  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_46])).
% 2.19/1.28  tff(c_121, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_117])).
% 2.19/1.28  tff(c_18, plain, (![A_30]: (v4_relat_1(k1_xboole_0, A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.28  tff(c_211, plain, (![A_88]: (k5_yellow_1(k1_xboole_0, A_88)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_88) | ~v1_partfun1(A_88, k1_xboole_0) | ~v1_funct_1(A_88) | ~v4_relat_1(A_88, k1_xboole_0) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_214, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_211])).
% 2.19/1.28  tff(c_217, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_81, c_77, c_121, c_214])).
% 2.19/1.28  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_217])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 40
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 1
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 1
% 2.19/1.28  #Demod        : 10
% 2.19/1.28  #Tautology    : 30
% 2.19/1.28  #SimpNegUnit  : 2
% 2.19/1.28  #BackRed      : 3
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.29  Preprocessing        : 0.33
% 2.19/1.29  Parsing              : 0.18
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.18
% 2.19/1.29  Inferencing          : 0.07
% 2.19/1.29  Reduction            : 0.06
% 2.19/1.29  Demodulation         : 0.04
% 2.19/1.29  BG Simplification    : 0.02
% 2.19/1.29  Subsumption          : 0.02
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.55
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
