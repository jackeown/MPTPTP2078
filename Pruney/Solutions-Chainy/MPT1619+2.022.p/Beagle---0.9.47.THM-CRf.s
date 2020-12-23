%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 126 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 260 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k2_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_45,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_8] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_8] : k2_funcop_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_26,plain,(
    ! [A_11,B_12] : k7_funcop_1(A_11,B_12) = k2_funcop_1(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k5_yellow_1(A_3,k7_funcop_1(A_3,B_4)) = k6_yellow_1(A_3,B_4)
      | ~ l1_orders_2(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_31,B_32] :
      ( k5_yellow_1(A_31,k2_funcop_1(A_31,B_32)) = k6_yellow_1(A_31,B_32)
      | ~ l1_orders_2(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_133,plain,(
    ! [A_33] :
      ( k6_yellow_1(k1_xboole_0,A_33) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_121])).

tff(c_141,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_32,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_142,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_32])).

tff(c_24,plain,(
    ! [A_9] : v1_relat_1('#skF_1'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_9] : v1_funct_1('#skF_1'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_9] : v1_partfun1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_9] : v4_relat_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_partfun1(A_30,k1_xboole_0)
      | ~ v1_funct_1(A_30)
      | ~ v4_relat_1(A_30,k1_xboole_0)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_96,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_18,c_93])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_24])).

tff(c_109,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_20])).

tff(c_100,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_71,plain,(
    ! [A_26,B_27] :
      ( v1_yellow_1(k2_funcop_1(A_26,B_27))
      | ~ l1_orders_2(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_8] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_84,plain,(
    ! [A_8] : ~ l1_orders_2(A_8) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_10,plain,(
    ! [A_5] : l1_orders_2(k2_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_10])).

tff(c_88,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_103,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_22])).

tff(c_154,plain,(
    ! [A_35] :
      ( k5_yellow_1(k1_xboole_0,A_35) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_35)
      | ~ v1_partfun1(A_35,k1_xboole_0)
      | ~ v1_funct_1(A_35)
      | ~ v4_relat_1(A_35,k1_xboole_0)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_156,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_103,c_154])).

tff(c_162,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_109,c_100,c_88,c_156])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:50:26 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k2_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 1.89/1.17  
% 1.89/1.17  %Foreground sorts:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Background operators:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Foreground operators:
% 1.89/1.17  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.89/1.17  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.89/1.17  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.89/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.17  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.89/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.17  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.89/1.17  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.89/1.17  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.89/1.17  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.89/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.89/1.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.89/1.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.17  
% 2.22/1.19  tff(f_85, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.22/1.19  tff(f_45, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.22/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.22/1.19  tff(f_58, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.22/1.19  tff(f_35, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.22/1.19  tff(f_56, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 2.22/1.19  tff(f_68, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_pboole)).
% 2.22/1.19  tff(f_43, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.22/1.19  tff(f_39, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.22/1.19  tff(f_80, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.22/1.19  tff(c_34, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.22/1.19  tff(c_14, plain, (![A_8]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.19  tff(c_44, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.19  tff(c_48, plain, (![A_8]: (k2_funcop_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.22/1.19  tff(c_26, plain, (![A_11, B_12]: (k7_funcop_1(A_11, B_12)=k2_funcop_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.19  tff(c_6, plain, (![A_3, B_4]: (k5_yellow_1(A_3, k7_funcop_1(A_3, B_4))=k6_yellow_1(A_3, B_4) | ~l1_orders_2(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.19  tff(c_121, plain, (![A_31, B_32]: (k5_yellow_1(A_31, k2_funcop_1(A_31, B_32))=k6_yellow_1(A_31, B_32) | ~l1_orders_2(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.22/1.19  tff(c_133, plain, (![A_33]: (k6_yellow_1(k1_xboole_0, A_33)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_33))), inference(superposition, [status(thm), theory('equality')], [c_48, c_121])).
% 2.22/1.19  tff(c_141, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_133])).
% 2.22/1.19  tff(c_32, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.22/1.19  tff(c_142, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_32])).
% 2.22/1.19  tff(c_24, plain, (![A_9]: (v1_relat_1('#skF_1'(A_9)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.19  tff(c_20, plain, (![A_9]: (v1_funct_1('#skF_1'(A_9)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.19  tff(c_18, plain, (![A_9]: (v1_partfun1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.19  tff(c_22, plain, (![A_9]: (v4_relat_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.19  tff(c_89, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_partfun1(A_30, k1_xboole_0) | ~v1_funct_1(A_30) | ~v4_relat_1(A_30, k1_xboole_0) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.19  tff(c_93, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_89])).
% 2.22/1.19  tff(c_96, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_18, c_93])).
% 2.22/1.19  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_24])).
% 2.22/1.19  tff(c_109, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_20])).
% 2.22/1.19  tff(c_100, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_18])).
% 2.22/1.19  tff(c_71, plain, (![A_26, B_27]: (v1_yellow_1(k2_funcop_1(A_26, B_27)) | ~l1_orders_2(B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.19  tff(c_74, plain, (![A_8]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_8))), inference(superposition, [status(thm), theory('equality')], [c_48, c_71])).
% 2.22/1.19  tff(c_84, plain, (![A_8]: (~l1_orders_2(A_8))), inference(splitLeft, [status(thm)], [c_74])).
% 2.22/1.19  tff(c_10, plain, (![A_5]: (l1_orders_2(k2_yellow_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.19  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_10])).
% 2.22/1.19  tff(c_88, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_74])).
% 2.22/1.19  tff(c_103, plain, (v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_22])).
% 2.22/1.19  tff(c_154, plain, (![A_35]: (k5_yellow_1(k1_xboole_0, A_35)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_35) | ~v1_partfun1(A_35, k1_xboole_0) | ~v1_funct_1(A_35) | ~v4_relat_1(A_35, k1_xboole_0) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.19  tff(c_156, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_154])).
% 2.22/1.19  tff(c_162, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_109, c_100, c_88, c_156])).
% 2.22/1.19  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_162])).
% 2.22/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.19  
% 2.22/1.19  Inference rules
% 2.22/1.19  ----------------------
% 2.22/1.19  #Ref     : 0
% 2.22/1.19  #Sup     : 29
% 2.22/1.19  #Fact    : 0
% 2.22/1.19  #Define  : 0
% 2.22/1.19  #Split   : 1
% 2.22/1.19  #Chain   : 0
% 2.22/1.19  #Close   : 0
% 2.22/1.19  
% 2.22/1.19  Ordering : KBO
% 2.22/1.19  
% 2.22/1.19  Simplification rules
% 2.22/1.19  ----------------------
% 2.22/1.19  #Subsume      : 1
% 2.22/1.19  #Demod        : 13
% 2.22/1.19  #Tautology    : 17
% 2.22/1.19  #SimpNegUnit  : 3
% 2.22/1.19  #BackRed      : 4
% 2.22/1.19  
% 2.22/1.19  #Partial instantiations: 0
% 2.22/1.19  #Strategies tried      : 1
% 2.22/1.19  
% 2.22/1.19  Timing (in seconds)
% 2.22/1.19  ----------------------
% 2.22/1.19  Preprocessing        : 0.30
% 2.22/1.19  Parsing              : 0.16
% 2.22/1.19  CNF conversion       : 0.02
% 2.22/1.19  Main loop            : 0.14
% 2.22/1.19  Inferencing          : 0.05
% 2.22/1.19  Reduction            : 0.04
% 2.22/1.19  Demodulation         : 0.03
% 2.22/1.19  BG Simplification    : 0.01
% 2.22/1.19  Subsumption          : 0.02
% 2.22/1.19  Abstraction          : 0.01
% 2.22/1.19  MUC search           : 0.00
% 2.22/1.19  Cooper               : 0.00
% 2.22/1.19  Total                : 0.47
% 2.22/1.19  Index Insertion      : 0.00
% 2.22/1.19  Index Deletion       : 0.00
% 2.22/1.19  Index Matching       : 0.00
% 2.22/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
