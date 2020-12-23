%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_57,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_21] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_2'(A_39),A_39)
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_68,plain,(
    ! [A_21] : k2_funcop_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_32,plain,(
    ! [A_24,B_25] : k7_funcop_1(A_24,B_25) = k2_funcop_1(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k5_yellow_1(A_17,k7_funcop_1(A_17,B_18)) = k6_yellow_1(A_17,B_18)
      | ~ l1_orders_2(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( k5_yellow_1(A_50,k2_funcop_1(A_50,B_51)) = k6_yellow_1(A_50,B_51)
      | ~ l1_orders_2(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_133,plain,(
    ! [A_52] :
      ( k6_yellow_1(k1_xboole_0,A_52) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_121])).

tff(c_137,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_4') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_38,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_138,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_38])).

tff(c_30,plain,(
    ! [A_22] : v1_relat_1('#skF_3'(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_22] : v1_funct_1('#skF_3'(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_22] : v1_partfun1('#skF_3'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_22] : v1_yellow_1('#skF_3'(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_22] : v4_relat_1('#skF_3'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_partfun1(A_57,k1_xboole_0)
      | ~ v1_funct_1(A_57)
      | ~ v4_relat_1(A_57,k1_xboole_0)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_156,plain,
    ( '#skF_3'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_3'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_3'(k1_xboole_0))
    | ~ v1_relat_1('#skF_3'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_152])).

tff(c_159,plain,(
    '#skF_3'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_156])).

tff(c_177,plain,(
    ! [A_58] :
      ( k5_yellow_1(k1_xboole_0,A_58) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_58)
      | ~ v1_partfun1(A_58,k1_xboole_0)
      | ~ v1_funct_1(A_58)
      | ~ v4_relat_1(A_58,k1_xboole_0)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_180,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_3'(k1_xboole_0))
    | ~ v1_yellow_1('#skF_3'(k1_xboole_0))
    | ~ v1_partfun1('#skF_3'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_3'(k1_xboole_0))
    | ~ v1_relat_1('#skF_3'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_177])).

tff(c_183,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_22,c_159,c_180])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  %$ v4_relat_1 > v1_partfun1 > r2_hidden > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.98/1.20  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.98/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.98/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.20  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.98/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.98/1.20  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.98/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.20  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.98/1.20  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.98/1.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.20  
% 1.98/1.22  tff(f_97, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 1.98/1.22  tff(f_57, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 1.98/1.22  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.98/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.22  tff(f_70, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 1.98/1.22  tff(f_51, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 1.98/1.22  tff(f_68, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_yellow_1)).
% 1.98/1.22  tff(f_80, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_pboole)).
% 1.98/1.22  tff(f_92, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 1.98/1.22  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.98/1.22  tff(c_20, plain, (![A_21]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.22  tff(c_59, plain, (![A_39]: (r2_hidden('#skF_2'(A_39), A_39) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.22  tff(c_64, plain, (![A_40]: (~v1_xboole_0(A_40) | k1_xboole_0=A_40)), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.98/1.22  tff(c_68, plain, (![A_21]: (k2_funcop_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.98/1.22  tff(c_32, plain, (![A_24, B_25]: (k7_funcop_1(A_24, B_25)=k2_funcop_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.22  tff(c_16, plain, (![A_17, B_18]: (k5_yellow_1(A_17, k7_funcop_1(A_17, B_18))=k6_yellow_1(A_17, B_18) | ~l1_orders_2(B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.22  tff(c_121, plain, (![A_50, B_51]: (k5_yellow_1(A_50, k2_funcop_1(A_50, B_51))=k6_yellow_1(A_50, B_51) | ~l1_orders_2(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 1.98/1.22  tff(c_133, plain, (![A_52]: (k6_yellow_1(k1_xboole_0, A_52)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_52))), inference(superposition, [status(thm), theory('equality')], [c_68, c_121])).
% 1.98/1.22  tff(c_137, plain, (k6_yellow_1(k1_xboole_0, '#skF_4')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_133])).
% 1.98/1.22  tff(c_38, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.98/1.22  tff(c_138, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_38])).
% 1.98/1.22  tff(c_30, plain, (![A_22]: (v1_relat_1('#skF_3'(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_26, plain, (![A_22]: (v1_funct_1('#skF_3'(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_24, plain, (![A_22]: (v1_partfun1('#skF_3'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_22, plain, (![A_22]: (v1_yellow_1('#skF_3'(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_28, plain, (![A_22]: (v4_relat_1('#skF_3'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_152, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_partfun1(A_57, k1_xboole_0) | ~v1_funct_1(A_57) | ~v4_relat_1(A_57, k1_xboole_0) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.98/1.22  tff(c_156, plain, ('#skF_3'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_3'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_3'(k1_xboole_0)) | ~v1_relat_1('#skF_3'(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_152])).
% 1.98/1.22  tff(c_159, plain, ('#skF_3'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_156])).
% 1.98/1.22  tff(c_177, plain, (![A_58]: (k5_yellow_1(k1_xboole_0, A_58)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_58) | ~v1_partfun1(A_58, k1_xboole_0) | ~v1_funct_1(A_58) | ~v4_relat_1(A_58, k1_xboole_0) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.22  tff(c_180, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_3'(k1_xboole_0)) | ~v1_yellow_1('#skF_3'(k1_xboole_0)) | ~v1_partfun1('#skF_3'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_3'(k1_xboole_0)) | ~v1_relat_1('#skF_3'(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_177])).
% 1.98/1.22  tff(c_183, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_22, c_159, c_180])).
% 1.98/1.22  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_183])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 32
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 1
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 1
% 1.98/1.22  #Demod        : 12
% 1.98/1.22  #Tautology    : 21
% 1.98/1.22  #SimpNegUnit  : 2
% 1.98/1.22  #BackRed      : 3
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.22  Preprocessing        : 0.31
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.16
% 1.98/1.22  Inferencing          : 0.06
% 1.98/1.22  Reduction            : 0.05
% 1.98/1.22  Demodulation         : 0.03
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.02
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.49
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
