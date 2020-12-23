%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 110 expanded)
%              Number of leaves         :   53 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 ( 122 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_86,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_76,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & v2_struct_0(A)
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_orders_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_60,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [A_41] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_102,plain,(
    ! [A_41] : k2_funcop_1(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_54,plain,(
    ! [A_42,B_43] : k7_funcop_1(A_42,B_43) = k2_funcop_1(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( k5_yellow_1(A_37,k7_funcop_1(A_37,B_38)) = k6_yellow_1(A_37,B_38)
      | ~ l1_orders_2(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_205,plain,(
    ! [A_69,B_70] :
      ( k5_yellow_1(A_69,k2_funcop_1(A_69,B_70)) = k6_yellow_1(A_69,B_70)
      | ~ l1_orders_2(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_217,plain,(
    ! [A_71] :
      ( k6_yellow_1(k1_xboole_0,A_71) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_205])).

tff(c_225,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_217])).

tff(c_58,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_226,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_75,plain,(
    ! [A_46] :
      ( v1_relat_1(A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_85,plain,(
    ! [A_48] :
      ( v1_funct_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_93,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_105,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_32])).

tff(c_36,plain,(
    ! [A_35] : v1_partfun1(k6_partfun1(A_35),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_36])).

tff(c_148,plain,(
    ! [A_54,B_55] :
      ( v1_yellow_1(k2_funcop_1(A_54,B_55))
      | ~ l1_orders_2(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_151,plain,(
    ! [A_41] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_148])).

tff(c_152,plain,(
    ! [A_41] : ~ l1_orders_2(A_41) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_46])).

tff(c_156,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [B_61,A_62] :
      ( v4_relat_1(B_61,A_62)
      | ~ r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_182,plain,(
    ! [A_62] :
      ( v4_relat_1(k1_xboole_0,A_62)
      | ~ r1_tarski(k1_xboole_0,A_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_179])).

tff(c_184,plain,(
    ! [A_62] : v4_relat_1(k1_xboole_0,A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6,c_182])).

tff(c_271,plain,(
    ! [A_94] :
      ( k5_yellow_1(k1_xboole_0,A_94) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_94)
      | ~ v1_partfun1(A_94,k1_xboole_0)
      | ~ v1_funct_1(A_94)
      | ~ v4_relat_1(A_94,k1_xboole_0)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_274,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_184,c_271])).

tff(c_277,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_93,c_123,c_156,c_274])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:29:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.46  
% 2.52/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.46  %$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.68/1.46  
% 2.68/1.46  %Foreground sorts:
% 2.68/1.46  
% 2.68/1.46  
% 2.68/1.46  %Background operators:
% 2.68/1.46  
% 2.68/1.46  
% 2.68/1.46  %Foreground operators:
% 2.68/1.46  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.68/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.46  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.68/1.46  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.68/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.46  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.68/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.46  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.68/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.46  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.68/1.46  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.68/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.68/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.68/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.46  
% 2.68/1.47  tff(f_105, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.68/1.47  tff(f_86, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.68/1.47  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.68/1.47  tff(f_88, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.68/1.47  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.68/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.47  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.68/1.47  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.68/1.47  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.68/1.47  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.68/1.47  tff(f_68, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.68/1.47  tff(f_84, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.68/1.47  tff(f_76, axiom, (?[A]: ((l1_orders_2(A) & v2_struct_0(A)) & v1_orders_2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_orders_2)).
% 2.68/1.47  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.68/1.47  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.47  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.68/1.47  tff(f_100, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.68/1.47  tff(c_60, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.68/1.47  tff(c_52, plain, (![A_41]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_41)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.68/1.47  tff(c_95, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.47  tff(c_102, plain, (![A_41]: (k2_funcop_1(k1_xboole_0, A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_95])).
% 2.68/1.47  tff(c_54, plain, (![A_42, B_43]: (k7_funcop_1(A_42, B_43)=k2_funcop_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.68/1.47  tff(c_48, plain, (![A_37, B_38]: (k5_yellow_1(A_37, k7_funcop_1(A_37, B_38))=k6_yellow_1(A_37, B_38) | ~l1_orders_2(B_38))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.68/1.47  tff(c_205, plain, (![A_69, B_70]: (k5_yellow_1(A_69, k2_funcop_1(A_69, B_70))=k6_yellow_1(A_69, B_70) | ~l1_orders_2(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 2.68/1.47  tff(c_217, plain, (![A_71]: (k6_yellow_1(k1_xboole_0, A_71)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_71))), inference(superposition, [status(thm), theory('equality')], [c_102, c_205])).
% 2.68/1.47  tff(c_225, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_217])).
% 2.68/1.47  tff(c_58, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.68/1.47  tff(c_226, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_225, c_58])).
% 2.68/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.47  tff(c_75, plain, (![A_46]: (v1_relat_1(A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.47  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_75])).
% 2.68/1.47  tff(c_85, plain, (![A_48]: (v1_funct_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.47  tff(c_93, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_85])).
% 2.68/1.47  tff(c_105, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.47  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.47  tff(c_111, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_32])).
% 2.68/1.47  tff(c_36, plain, (![A_35]: (v1_partfun1(k6_partfun1(A_35), A_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.47  tff(c_123, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_36])).
% 2.68/1.47  tff(c_148, plain, (![A_54, B_55]: (v1_yellow_1(k2_funcop_1(A_54, B_55)) | ~l1_orders_2(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.68/1.47  tff(c_151, plain, (![A_41]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_41))), inference(superposition, [status(thm), theory('equality')], [c_102, c_148])).
% 2.68/1.47  tff(c_152, plain, (![A_41]: (~l1_orders_2(A_41))), inference(splitLeft, [status(thm)], [c_151])).
% 2.68/1.47  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.47  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_46])).
% 2.68/1.47  tff(c_156, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_151])).
% 2.68/1.47  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.47  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.47  tff(c_179, plain, (![B_61, A_62]: (v4_relat_1(B_61, A_62) | ~r1_tarski(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.47  tff(c_182, plain, (![A_62]: (v4_relat_1(k1_xboole_0, A_62) | ~r1_tarski(k1_xboole_0, A_62) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_179])).
% 2.68/1.47  tff(c_184, plain, (![A_62]: (v4_relat_1(k1_xboole_0, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_6, c_182])).
% 2.68/1.47  tff(c_271, plain, (![A_94]: (k5_yellow_1(k1_xboole_0, A_94)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_94) | ~v1_partfun1(A_94, k1_xboole_0) | ~v1_funct_1(A_94) | ~v4_relat_1(A_94, k1_xboole_0) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.68/1.47  tff(c_274, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_184, c_271])).
% 2.68/1.47  tff(c_277, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_93, c_123, c_156, c_274])).
% 2.68/1.47  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_277])).
% 2.68/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.47  
% 2.68/1.47  Inference rules
% 2.68/1.47  ----------------------
% 2.68/1.47  #Ref     : 0
% 2.68/1.47  #Sup     : 52
% 2.68/1.47  #Fact    : 0
% 2.68/1.47  #Define  : 0
% 2.68/1.47  #Split   : 1
% 2.68/1.47  #Chain   : 0
% 2.68/1.47  #Close   : 0
% 2.68/1.47  
% 2.68/1.47  Ordering : KBO
% 2.68/1.47  
% 2.68/1.47  Simplification rules
% 2.68/1.47  ----------------------
% 2.68/1.47  #Subsume      : 1
% 2.68/1.47  #Demod        : 18
% 2.68/1.47  #Tautology    : 41
% 2.68/1.47  #SimpNegUnit  : 3
% 2.68/1.47  #BackRed      : 4
% 2.68/1.47  
% 2.68/1.47  #Partial instantiations: 0
% 2.68/1.47  #Strategies tried      : 1
% 2.68/1.47  
% 2.68/1.47  Timing (in seconds)
% 2.68/1.47  ----------------------
% 2.68/1.48  Preprocessing        : 0.44
% 2.68/1.48  Parsing              : 0.23
% 2.68/1.48  CNF conversion       : 0.02
% 2.68/1.48  Main loop            : 0.20
% 2.68/1.48  Inferencing          : 0.07
% 2.68/1.48  Reduction            : 0.07
% 2.68/1.48  Demodulation         : 0.05
% 2.68/1.48  BG Simplification    : 0.02
% 2.68/1.48  Subsumption          : 0.03
% 2.68/1.48  Abstraction          : 0.01
% 2.68/1.48  MUC search           : 0.00
% 2.68/1.48  Cooper               : 0.00
% 2.68/1.48  Total                : 0.68
% 2.68/1.48  Index Insertion      : 0.00
% 2.68/1.48  Index Deletion       : 0.00
% 2.68/1.48  Index Matching       : 0.00
% 2.68/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
