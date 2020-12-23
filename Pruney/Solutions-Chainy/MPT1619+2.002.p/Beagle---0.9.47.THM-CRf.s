%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 112 expanded)
%              Number of leaves         :   55 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :   93 ( 124 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_91,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_81,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v7_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_64,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    ! [A_41] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_118,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_125,plain,(
    ! [A_41] : k2_funcop_1(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_58,plain,(
    ! [A_42,B_43] : k7_funcop_1(A_42,B_43) = k2_funcop_1(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [A_37,B_38] :
      ( k5_yellow_1(A_37,k7_funcop_1(A_37,B_38)) = k6_yellow_1(A_37,B_38)
      | ~ l1_orders_2(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_222,plain,(
    ! [A_75,B_76] :
      ( k5_yellow_1(A_75,k2_funcop_1(A_75,B_76)) = k6_yellow_1(A_75,B_76)
      | ~ l1_orders_2(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52])).

tff(c_234,plain,(
    ! [A_77] :
      ( k6_yellow_1(k1_xboole_0,A_77) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_222])).

tff(c_242,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_234])).

tff(c_62,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_247,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_62])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_99,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_104,plain,(
    ! [A_48] :
      ( v1_funct_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_79,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_32])).

tff(c_128,plain,(
    ! [A_51] : v1_partfun1(k6_partfun1(A_51),A_51) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_131,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_128])).

tff(c_165,plain,(
    ! [A_58,B_59] :
      ( v1_yellow_1(k2_funcop_1(A_58,B_59))
      | ~ l1_orders_2(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_168,plain,(
    ! [A_41] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_165])).

tff(c_178,plain,(
    ! [A_41] : ~ l1_orders_2(A_41) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_50,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_50])).

tff(c_182,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_196,plain,(
    ! [B_66,A_67] :
      ( v4_relat_1(B_66,A_67)
      | ~ r1_tarski(k1_relat_1(B_66),A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_199,plain,(
    ! [A_67] :
      ( v4_relat_1(k1_xboole_0,A_67)
      | ~ r1_tarski(k1_xboole_0,A_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_196])).

tff(c_201,plain,(
    ! [A_67] : v4_relat_1(k1_xboole_0,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_6,c_199])).

tff(c_279,plain,(
    ! [A_96] :
      ( k5_yellow_1(k1_xboole_0,A_96) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_96)
      | ~ v1_partfun1(A_96,k1_xboole_0)
      | ~ v1_funct_1(A_96)
      | ~ v4_relat_1(A_96,k1_xboole_0)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_282,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_201,c_279])).

tff(c_285,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_108,c_131,c_182,c_282])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:27:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  %$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.51/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.34  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.51/1.34  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.51/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.51/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.51/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.34  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.51/1.34  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.51/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.34  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.51/1.34  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.51/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.51/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.34  
% 2.51/1.35  tff(f_110, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.51/1.35  tff(f_91, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.51/1.35  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.51/1.35  tff(f_93, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.51/1.35  tff(f_85, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.51/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.51/1.35  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.51/1.35  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.51/1.35  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.51/1.35  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.51/1.35  tff(f_68, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.51/1.35  tff(f_89, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.51/1.35  tff(f_81, axiom, (?[A]: ((((l1_orders_2(A) & ~v2_struct_0(A)) & v7_struct_0(A)) & v1_orders_2(A)) & v3_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_0)).
% 2.51/1.35  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.35  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.51/1.35  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.51/1.35  tff(f_105, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.51/1.35  tff(c_64, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.51/1.35  tff(c_56, plain, (![A_41]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_41)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.35  tff(c_118, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.51/1.35  tff(c_125, plain, (![A_41]: (k2_funcop_1(k1_xboole_0, A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_118])).
% 2.51/1.35  tff(c_58, plain, (![A_42, B_43]: (k7_funcop_1(A_42, B_43)=k2_funcop_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_52, plain, (![A_37, B_38]: (k5_yellow_1(A_37, k7_funcop_1(A_37, B_38))=k6_yellow_1(A_37, B_38) | ~l1_orders_2(B_38))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.51/1.35  tff(c_222, plain, (![A_75, B_76]: (k5_yellow_1(A_75, k2_funcop_1(A_75, B_76))=k6_yellow_1(A_75, B_76) | ~l1_orders_2(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52])).
% 2.51/1.35  tff(c_234, plain, (![A_77]: (k6_yellow_1(k1_xboole_0, A_77)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_77))), inference(superposition, [status(thm), theory('equality')], [c_125, c_222])).
% 2.51/1.35  tff(c_242, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_234])).
% 2.51/1.35  tff(c_62, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.51/1.35  tff(c_247, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_62])).
% 2.51/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.51/1.35  tff(c_99, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.35  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_99])).
% 2.51/1.35  tff(c_104, plain, (![A_48]: (v1_funct_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.35  tff(c_108, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_104])).
% 2.51/1.35  tff(c_79, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.35  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.35  tff(c_85, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_79, c_32])).
% 2.51/1.35  tff(c_128, plain, (![A_51]: (v1_partfun1(k6_partfun1(A_51), A_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.35  tff(c_131, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_128])).
% 2.51/1.35  tff(c_165, plain, (![A_58, B_59]: (v1_yellow_1(k2_funcop_1(A_58, B_59)) | ~l1_orders_2(B_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.51/1.35  tff(c_168, plain, (![A_41]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_41))), inference(superposition, [status(thm), theory('equality')], [c_125, c_165])).
% 2.51/1.35  tff(c_178, plain, (![A_41]: (~l1_orders_2(A_41))), inference(splitLeft, [status(thm)], [c_168])).
% 2.51/1.35  tff(c_50, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.51/1.35  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_50])).
% 2.51/1.35  tff(c_182, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_168])).
% 2.51/1.35  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.35  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.35  tff(c_196, plain, (![B_66, A_67]: (v4_relat_1(B_66, A_67) | ~r1_tarski(k1_relat_1(B_66), A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.35  tff(c_199, plain, (![A_67]: (v4_relat_1(k1_xboole_0, A_67) | ~r1_tarski(k1_xboole_0, A_67) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_196])).
% 2.51/1.35  tff(c_201, plain, (![A_67]: (v4_relat_1(k1_xboole_0, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_6, c_199])).
% 2.51/1.35  tff(c_279, plain, (![A_96]: (k5_yellow_1(k1_xboole_0, A_96)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_96) | ~v1_partfun1(A_96, k1_xboole_0) | ~v1_funct_1(A_96) | ~v4_relat_1(A_96, k1_xboole_0) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.51/1.35  tff(c_282, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_201, c_279])).
% 2.51/1.35  tff(c_285, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_108, c_131, c_182, c_282])).
% 2.51/1.35  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_285])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 0
% 2.51/1.35  #Sup     : 52
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 1
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 1
% 2.51/1.35  #Demod        : 18
% 2.51/1.35  #Tautology    : 41
% 2.51/1.35  #SimpNegUnit  : 3
% 2.51/1.35  #BackRed      : 6
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.36  Preprocessing        : 0.34
% 2.51/1.36  Parsing              : 0.18
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.20
% 2.51/1.36  Inferencing          : 0.08
% 2.51/1.36  Reduction            : 0.07
% 2.51/1.36  Demodulation         : 0.05
% 2.51/1.36  BG Simplification    : 0.01
% 2.51/1.36  Subsumption          : 0.02
% 2.51/1.36  Abstraction          : 0.01
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.57
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
