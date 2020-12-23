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
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 126 expanded)
%              Number of leaves         :   47 (  67 expanded)
%              Depth                    :    6
%              Number of atoms          :   79 ( 133 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_76,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_60,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_66,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & v2_struct_0(A)
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_orders_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_52,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_91,plain,(
    ! [A_49] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_49] : k2_funcop_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_46,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_186,plain,(
    ! [A_70,B_71] :
      ( k5_yellow_1(A_70,k2_funcop_1(A_70,B_71)) = k6_yellow_1(A_70,B_71)
      | ~ l1_orders_2(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40])).

tff(c_198,plain,(
    ! [A_72] :
      ( k6_yellow_1(k1_xboole_0,A_72) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_186])).

tff(c_206,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_198])).

tff(c_50,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_211,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_50])).

tff(c_63,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_32,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [A_30] : v1_relat_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_55])).

tff(c_22,plain,(
    ! [A_30] : v1_funct_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_30] : v1_funct_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_82,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_54])).

tff(c_28,plain,(
    ! [A_34] : v1_partfun1(k6_partfun1(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_118,plain,(
    ! [A_52,B_53] :
      ( v1_yellow_1(k2_funcop_1(A_52,B_53))
      | ~ l1_orders_2(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,(
    ! [A_49] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_118])).

tff(c_122,plain,(
    ! [A_49] : ~ l1_orders_2(A_49) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_38,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_38])).

tff(c_126,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_30,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_172,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_180,plain,(
    ! [A_34] : v4_relat_1(k6_partfun1(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_252,plain,(
    ! [A_95] :
      ( k5_yellow_1(k1_xboole_0,A_95) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_95)
      | ~ v1_partfun1(A_95,k1_xboole_0)
      | ~ v1_funct_1(A_95)
      | ~ v4_relat_1(A_95,k1_xboole_0)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_255,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | ~ v1_yellow_1(k6_partfun1(k1_xboole_0))
    | ~ v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_180,c_252])).

tff(c_260,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_69,c_82,c_69,c_28,c_126,c_69,c_69,c_255])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.23/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.29  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.23/1.29  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.23/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.23/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.29  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.23/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.29  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.23/1.29  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.23/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.23/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.29  
% 2.23/1.30  tff(f_95, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.23/1.30  tff(f_76, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.23/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.30  tff(f_78, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.23/1.30  tff(f_70, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.23/1.30  tff(f_60, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.23/1.30  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.23/1.30  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.23/1.30  tff(f_58, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.23/1.30  tff(f_74, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.23/1.30  tff(f_66, axiom, (?[A]: ((l1_orders_2(A) & v2_struct_0(A)) & v1_orders_2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_orders_2)).
% 2.23/1.30  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.23/1.30  tff(f_90, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.23/1.30  tff(c_52, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.23/1.30  tff(c_91, plain, (![A_49]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_49)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.30  tff(c_95, plain, (![A_49]: (k2_funcop_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_2])).
% 2.23/1.30  tff(c_46, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.30  tff(c_40, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.30  tff(c_186, plain, (![A_70, B_71]: (k5_yellow_1(A_70, k2_funcop_1(A_70, B_71))=k6_yellow_1(A_70, B_71) | ~l1_orders_2(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40])).
% 2.23/1.30  tff(c_198, plain, (![A_72]: (k6_yellow_1(k1_xboole_0, A_72)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_72))), inference(superposition, [status(thm), theory('equality')], [c_95, c_186])).
% 2.23/1.30  tff(c_206, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_198])).
% 2.23/1.30  tff(c_50, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.23/1.30  tff(c_211, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_206, c_50])).
% 2.23/1.30  tff(c_63, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.30  tff(c_69, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63, c_18])).
% 2.23/1.30  tff(c_32, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_20, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.30  tff(c_55, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_20])).
% 2.23/1.30  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_55])).
% 2.23/1.30  tff(c_22, plain, (![A_30]: (v1_funct_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.30  tff(c_54, plain, (![A_30]: (v1_funct_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22])).
% 2.23/1.30  tff(c_82, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_54])).
% 2.23/1.30  tff(c_28, plain, (![A_34]: (v1_partfun1(k6_partfun1(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.30  tff(c_118, plain, (![A_52, B_53]: (v1_yellow_1(k2_funcop_1(A_52, B_53)) | ~l1_orders_2(B_53))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_121, plain, (![A_49]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_95, c_118])).
% 2.23/1.30  tff(c_122, plain, (![A_49]: (~l1_orders_2(A_49))), inference(splitLeft, [status(thm)], [c_121])).
% 2.23/1.30  tff(c_38, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.30  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_38])).
% 2.23/1.30  tff(c_126, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_121])).
% 2.23/1.30  tff(c_30, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.30  tff(c_172, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.23/1.30  tff(c_180, plain, (![A_34]: (v4_relat_1(k6_partfun1(A_34), A_34))), inference(resolution, [status(thm)], [c_30, c_172])).
% 2.23/1.30  tff(c_252, plain, (![A_95]: (k5_yellow_1(k1_xboole_0, A_95)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_95) | ~v1_partfun1(A_95, k1_xboole_0) | ~v1_funct_1(A_95) | ~v4_relat_1(A_95, k1_xboole_0) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.30  tff(c_255, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k6_partfun1(k1_xboole_0)) | ~v1_yellow_1(k6_partfun1(k1_xboole_0)) | ~v1_partfun1(k6_partfun1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_relat_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_252])).
% 2.23/1.30  tff(c_260, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_69, c_82, c_69, c_28, c_126, c_69, c_69, c_255])).
% 2.23/1.30  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_260])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 50
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 1
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.31  #Subsume      : 1
% 2.23/1.31  #Demod        : 16
% 2.23/1.31  #Tautology    : 34
% 2.23/1.31  #SimpNegUnit  : 3
% 2.23/1.31  #BackRed      : 4
% 2.23/1.31  
% 2.23/1.31  #Partial instantiations: 0
% 2.23/1.31  #Strategies tried      : 1
% 2.23/1.31  
% 2.23/1.31  Timing (in seconds)
% 2.23/1.31  ----------------------
% 2.23/1.31  Preprocessing        : 0.35
% 2.23/1.31  Parsing              : 0.19
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.20
% 2.50/1.31  Inferencing          : 0.08
% 2.50/1.31  Reduction            : 0.06
% 2.50/1.31  Demodulation         : 0.05
% 2.50/1.31  BG Simplification    : 0.01
% 2.50/1.31  Subsumption          : 0.02
% 2.50/1.31  Abstraction          : 0.01
% 2.50/1.31  MUC search           : 0.00
% 2.50/1.31  Cooper               : 0.00
% 2.50/1.31  Total                : 0.58
% 2.50/1.31  Index Insertion      : 0.00
% 2.50/1.31  Index Deletion       : 0.00
% 2.50/1.31  Index Matching       : 0.00
% 2.50/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
