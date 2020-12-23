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
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   72 (  89 expanded)
%              Number of leaves         :   44 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 (  98 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v5_ordinal1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_72,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_62,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_50,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,(
    ! [A_46] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_46] : k2_funcop_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_44,plain,(
    ! [A_40,B_41] : k7_funcop_1(A_40,B_41) = k2_funcop_1(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( k5_yellow_1(A_35,k7_funcop_1(A_35,B_36)) = k6_yellow_1(A_35,B_36)
      | ~ l1_orders_2(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    ! [A_61,B_62] :
      ( k5_yellow_1(A_61,k2_funcop_1(A_61,B_62)) = k6_yellow_1(A_61,B_62)
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_162,plain,(
    ! [A_63] :
      ( k6_yellow_1(k1_xboole_0,A_63) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_150])).

tff(c_166,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_162])).

tff(c_48,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_167,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_48])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_22])).

tff(c_85,plain,(
    ! [A_48] : v1_partfun1(k6_partfun1(A_48),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_85])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( v1_yellow_1(k2_funcop_1(A_51,B_52))
      | ~ l1_orders_2(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,(
    ! [A_46] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_111])).

tff(c_124,plain,(
    ! [A_46] : ~ l1_orders_2(A_46) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_50])).

tff(c_127,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_18,plain,(
    ! [A_30] : v4_relat_1(k1_xboole_0,A_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_208,plain,(
    ! [A_86] :
      ( k5_yellow_1(k1_xboole_0,A_86) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_86)
      | ~ v1_partfun1(A_86,k1_xboole_0)
      | ~ v1_funct_1(A_86)
      | ~ v4_relat_1(A_86,k1_xboole_0)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_208])).

tff(c_214,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_88,c_127,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v5_ordinal1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.26/1.28  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.26/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.26/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.26/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.28  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.26/1.28  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.26/1.28  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.26/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.26/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.26/1.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.26/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.28  
% 2.26/1.29  tff(f_91, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.26/1.29  tff(f_72, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.26/1.29  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.26/1.29  tff(f_74, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.26/1.29  tff(f_66, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.26/1.29  tff(f_56, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 2.26/1.29  tff(f_62, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.26/1.29  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.26/1.29  tff(f_60, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.26/1.29  tff(f_70, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.26/1.29  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 2.26/1.29  tff(f_86, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.26/1.29  tff(c_50, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.26/1.29  tff(c_60, plain, (![A_46]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_46)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.29  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.29  tff(c_64, plain, (![A_46]: (k2_funcop_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.26/1.29  tff(c_44, plain, (![A_40, B_41]: (k7_funcop_1(A_40, B_41)=k2_funcop_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.29  tff(c_38, plain, (![A_35, B_36]: (k5_yellow_1(A_35, k7_funcop_1(A_35, B_36))=k6_yellow_1(A_35, B_36) | ~l1_orders_2(B_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.29  tff(c_150, plain, (![A_61, B_62]: (k5_yellow_1(A_61, k2_funcop_1(A_61, B_62))=k6_yellow_1(A_61, B_62) | ~l1_orders_2(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 2.26/1.29  tff(c_162, plain, (![A_63]: (k6_yellow_1(k1_xboole_0, A_63)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_63))), inference(superposition, [status(thm), theory('equality')], [c_64, c_150])).
% 2.26/1.29  tff(c_166, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_162])).
% 2.26/1.29  tff(c_48, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.26/1.29  tff(c_167, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_48])).
% 2.26/1.29  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.29  tff(c_28, plain, (v1_funct_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.29  tff(c_65, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.29  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.29  tff(c_71, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_65, c_22])).
% 2.26/1.29  tff(c_85, plain, (![A_48]: (v1_partfun1(k6_partfun1(A_48), A_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.29  tff(c_88, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_85])).
% 2.26/1.29  tff(c_111, plain, (![A_51, B_52]: (v1_yellow_1(k2_funcop_1(A_51, B_52)) | ~l1_orders_2(B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.29  tff(c_114, plain, (![A_46]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_46))), inference(superposition, [status(thm), theory('equality')], [c_64, c_111])).
% 2.26/1.29  tff(c_124, plain, (![A_46]: (~l1_orders_2(A_46))), inference(splitLeft, [status(thm)], [c_114])).
% 2.26/1.29  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_50])).
% 2.26/1.29  tff(c_127, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_114])).
% 2.26/1.29  tff(c_18, plain, (![A_30]: (v4_relat_1(k1_xboole_0, A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.29  tff(c_208, plain, (![A_86]: (k5_yellow_1(k1_xboole_0, A_86)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_86) | ~v1_partfun1(A_86, k1_xboole_0) | ~v1_funct_1(A_86) | ~v4_relat_1(A_86, k1_xboole_0) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.26/1.29  tff(c_211, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_208])).
% 2.26/1.29  tff(c_214, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_88, c_127, c_211])).
% 2.26/1.29  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_214])).
% 2.26/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  Inference rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Ref     : 0
% 2.26/1.29  #Sup     : 38
% 2.26/1.29  #Fact    : 0
% 2.26/1.29  #Define  : 0
% 2.26/1.29  #Split   : 1
% 2.26/1.29  #Chain   : 0
% 2.26/1.29  #Close   : 0
% 2.26/1.29  
% 2.26/1.29  Ordering : KBO
% 2.26/1.29  
% 2.26/1.29  Simplification rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Subsume      : 1
% 2.26/1.29  #Demod        : 9
% 2.26/1.29  #Tautology    : 31
% 2.26/1.29  #SimpNegUnit  : 2
% 2.26/1.29  #BackRed      : 3
% 2.26/1.29  
% 2.26/1.29  #Partial instantiations: 0
% 2.26/1.29  #Strategies tried      : 1
% 2.26/1.29  
% 2.26/1.29  Timing (in seconds)
% 2.26/1.29  ----------------------
% 2.26/1.30  Preprocessing        : 0.33
% 2.26/1.30  Parsing              : 0.18
% 2.26/1.30  CNF conversion       : 0.02
% 2.26/1.30  Main loop            : 0.17
% 2.26/1.30  Inferencing          : 0.06
% 2.26/1.30  Reduction            : 0.05
% 2.26/1.30  Demodulation         : 0.04
% 2.26/1.30  BG Simplification    : 0.01
% 2.26/1.30  Subsumption          : 0.02
% 2.26/1.30  Abstraction          : 0.01
% 2.26/1.30  MUC search           : 0.00
% 2.26/1.30  Cooper               : 0.00
% 2.26/1.30  Total                : 0.52
% 2.26/1.30  Index Insertion      : 0.00
% 2.26/1.30  Index Deletion       : 0.00
% 2.26/1.30  Index Matching       : 0.00
% 2.26/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
