%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:42 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 120 expanded)
%              Number of equality atoms :   29 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_70,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_52,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_96,plain,(
    ! [A_36] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_36] : k2_funcop_1(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_46,plain,(
    ! [A_23,B_24] : k7_funcop_1(A_23,B_24) = k2_funcop_1(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k5_yellow_1(A_18,k7_funcop_1(A_18,B_19)) = k6_yellow_1(A_18,B_19)
      | ~ l1_orders_2(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_194,plain,(
    ! [A_53,B_54] :
      ( k5_yellow_1(A_53,k2_funcop_1(A_53,B_54)) = k6_yellow_1(A_53,B_54)
      | ~ l1_orders_2(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32])).

tff(c_206,plain,(
    ! [A_55] :
      ( k6_yellow_1(k1_xboole_0,A_55) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_194])).

tff(c_210,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_206])).

tff(c_50,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_212,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_50])).

tff(c_44,plain,(
    ! [A_21] : v1_relat_1('#skF_1'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [A_21] : v1_funct_1('#skF_1'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_21] : v1_partfun1('#skF_1'(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_21] : v1_yellow_1('#skF_1'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [A_21] : v4_relat_1('#skF_1'(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_226,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(B_61) = A_62
      | ~ v1_partfun1(B_61,A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_229,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_1'(A_21)) = A_21
      | ~ v1_partfun1('#skF_1'(A_21),A_21)
      | ~ v1_relat_1('#skF_1'(A_21)) ) ),
    inference(resolution,[status(thm)],[c_42,c_226])).

tff(c_232,plain,(
    ! [A_21] : k1_relat_1('#skF_1'(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_229])).

tff(c_132,plain,(
    ! [A_41] :
      ( k1_relat_1(A_41) != k1_xboole_0
      | k1_xboole_0 = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_1'(A_21)) != k1_xboole_0
      | '#skF_1'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_248,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_145])).

tff(c_291,plain,(
    ! [A_65] :
      ( k5_yellow_1(k1_xboole_0,A_65) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_65)
      | ~ v1_partfun1(A_65,k1_xboole_0)
      | ~ v1_funct_1(A_65)
      | ~ v4_relat_1(A_65,k1_xboole_0)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_294,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_1'(k1_xboole_0))
    | ~ v1_yellow_1('#skF_1'(k1_xboole_0))
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_42,c_291])).

tff(c_297,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_248,c_294])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:08:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  %$ v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.41/1.32  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.41/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.41/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.41/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.32  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.41/1.32  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.41/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.41/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.41/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.41/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.32  
% 2.41/1.33  tff(f_100, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.41/1.33  tff(f_70, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.41/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.41/1.33  tff(f_83, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.41/1.33  tff(f_68, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.41/1.33  tff(f_81, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 2.41/1.33  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.41/1.33  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.41/1.33  tff(f_95, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.41/1.33  tff(c_52, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.33  tff(c_96, plain, (![A_36]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_36)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.33  tff(c_100, plain, (![A_36]: (k2_funcop_1(k1_xboole_0, A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.41/1.33  tff(c_46, plain, (![A_23, B_24]: (k7_funcop_1(A_23, B_24)=k2_funcop_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.33  tff(c_32, plain, (![A_18, B_19]: (k5_yellow_1(A_18, k7_funcop_1(A_18, B_19))=k6_yellow_1(A_18, B_19) | ~l1_orders_2(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.33  tff(c_194, plain, (![A_53, B_54]: (k5_yellow_1(A_53, k2_funcop_1(A_53, B_54))=k6_yellow_1(A_53, B_54) | ~l1_orders_2(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32])).
% 2.41/1.33  tff(c_206, plain, (![A_55]: (k6_yellow_1(k1_xboole_0, A_55)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_55))), inference(superposition, [status(thm), theory('equality')], [c_100, c_194])).
% 2.41/1.33  tff(c_210, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_206])).
% 2.41/1.33  tff(c_50, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.33  tff(c_212, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_50])).
% 2.41/1.33  tff(c_44, plain, (![A_21]: (v1_relat_1('#skF_1'(A_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_40, plain, (![A_21]: (v1_funct_1('#skF_1'(A_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_38, plain, (![A_21]: (v1_partfun1('#skF_1'(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_36, plain, (![A_21]: (v1_yellow_1('#skF_1'(A_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_42, plain, (![A_21]: (v4_relat_1('#skF_1'(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_226, plain, (![B_61, A_62]: (k1_relat_1(B_61)=A_62 | ~v1_partfun1(B_61, A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.33  tff(c_229, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21))=A_21 | ~v1_partfun1('#skF_1'(A_21), A_21) | ~v1_relat_1('#skF_1'(A_21)))), inference(resolution, [status(thm)], [c_42, c_226])).
% 2.41/1.33  tff(c_232, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_229])).
% 2.41/1.33  tff(c_132, plain, (![A_41]: (k1_relat_1(A_41)!=k1_xboole_0 | k1_xboole_0=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.33  tff(c_145, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21))!=k1_xboole_0 | '#skF_1'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_132])).
% 2.41/1.33  tff(c_248, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_232, c_145])).
% 2.41/1.33  tff(c_291, plain, (![A_65]: (k5_yellow_1(k1_xboole_0, A_65)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_65) | ~v1_partfun1(A_65, k1_xboole_0) | ~v1_funct_1(A_65) | ~v4_relat_1(A_65, k1_xboole_0) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.41/1.33  tff(c_294, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_1'(k1_xboole_0)) | ~v1_yellow_1('#skF_1'(k1_xboole_0)) | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_291])).
% 2.41/1.33  tff(c_297, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_36, c_248, c_294])).
% 2.41/1.33  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_297])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 54
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 1
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 7
% 2.41/1.33  #Demod        : 22
% 2.41/1.33  #Tautology    : 35
% 2.41/1.33  #SimpNegUnit  : 11
% 2.41/1.33  #BackRed      : 7
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.34
% 2.41/1.33  Parsing              : 0.19
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.33  Main loop            : 0.19
% 2.41/1.33  Inferencing          : 0.07
% 2.41/1.33  Reduction            : 0.06
% 2.41/1.33  Demodulation         : 0.04
% 2.41/1.33  BG Simplification    : 0.01
% 2.41/1.33  Subsumption          : 0.02
% 2.41/1.33  Abstraction          : 0.01
% 2.41/1.33  MUC search           : 0.00
% 2.41/1.33  Cooper               : 0.00
% 2.41/1.33  Total                : 0.55
% 2.41/1.33  Index Insertion      : 0.00
% 2.41/1.33  Index Deletion       : 0.00
% 2.41/1.33  Index Matching       : 0.00
% 2.41/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
