%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 127 expanded)
%              Number of leaves         :   51 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :   85 ( 136 expanded)
%              Number of equality atoms :   22 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_86,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_80,axiom,(
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

tff(f_65,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_76,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v7_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_58,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_76,plain,(
    ! [A_48] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_83,plain,(
    ! [A_48] : k2_funcop_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_52,plain,(
    ! [A_42,B_43] : k7_funcop_1(A_42,B_43) = k2_funcop_1(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_37,B_38] :
      ( k5_yellow_1(A_37,k7_funcop_1(A_37,B_38)) = k6_yellow_1(A_37,B_38)
      | ~ l1_orders_2(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_216,plain,(
    ! [A_76,B_77] :
      ( k5_yellow_1(A_76,k2_funcop_1(A_76,B_77)) = k6_yellow_1(A_76,B_77)
      | ~ l1_orders_2(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46])).

tff(c_228,plain,(
    ! [A_78] :
      ( k6_yellow_1(k1_xboole_0,A_78) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_216])).

tff(c_236,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58,c_228])).

tff(c_56,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_241,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_56])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_85,plain,(
    ! [A_49] :
      ( v1_relat_1(A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_94,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_22])).

tff(c_64,plain,(
    ! [A_45] :
      ( v1_funct_1(A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_30,plain,(
    ! [A_35] : v1_partfun1(k6_partfun1(A_35),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_30])).

tff(c_139,plain,(
    ! [A_54,B_55] :
      ( v1_yellow_1(k2_funcop_1(A_54,B_55))
      | ~ l1_orders_2(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_142,plain,(
    ! [A_48] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_139])).

tff(c_152,plain,(
    ! [A_48] : ~ l1_orders_2(A_48) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_44])).

tff(c_156,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_32,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    ! [A_35] : v4_relat_1(k6_partfun1(A_35),A_35) ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_273,plain,(
    ! [A_97] :
      ( k5_yellow_1(k1_xboole_0,A_97) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_97)
      | ~ v1_partfun1(A_97,k1_xboole_0)
      | ~ v1_funct_1(A_97)
      | ~ v4_relat_1(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_276,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | ~ v1_yellow_1(k6_partfun1(k1_xboole_0))
    | ~ v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_187,c_273])).

tff(c_281,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_100,c_68,c_100,c_112,c_100,c_156,c_100,c_100,c_276])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.24  
% 2.29/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.24  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.29/1.24  
% 2.29/1.24  %Foreground sorts:
% 2.29/1.24  
% 2.29/1.24  
% 2.29/1.24  %Background operators:
% 2.29/1.24  
% 2.29/1.24  
% 2.29/1.24  %Foreground operators:
% 2.29/1.24  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.29/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.24  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.29/1.24  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.29/1.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.29/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.24  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.29/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.24  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.29/1.24  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.29/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.24  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.29/1.24  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.29/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.29/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.29/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.29/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.29/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.24  
% 2.29/1.26  tff(f_105, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.29/1.26  tff(f_86, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.29/1.26  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.29/1.26  tff(f_88, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.29/1.26  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.29/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.26  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.29/1.26  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.29/1.26  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.29/1.26  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.29/1.26  tff(f_63, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.29/1.26  tff(f_84, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.29/1.26  tff(f_76, axiom, (?[A]: ((((l1_orders_2(A) & ~v2_struct_0(A)) & v7_struct_0(A)) & v1_orders_2(A)) & v3_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_0)).
% 2.29/1.26  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.29/1.26  tff(f_100, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.29/1.26  tff(c_58, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.26  tff(c_76, plain, (![A_48]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_48)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.29/1.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.29/1.26  tff(c_83, plain, (![A_48]: (k2_funcop_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_4])).
% 2.29/1.26  tff(c_52, plain, (![A_42, B_43]: (k7_funcop_1(A_42, B_43)=k2_funcop_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.29/1.26  tff(c_46, plain, (![A_37, B_38]: (k5_yellow_1(A_37, k7_funcop_1(A_37, B_38))=k6_yellow_1(A_37, B_38) | ~l1_orders_2(B_38))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.26  tff(c_216, plain, (![A_76, B_77]: (k5_yellow_1(A_76, k2_funcop_1(A_76, B_77))=k6_yellow_1(A_76, B_77) | ~l1_orders_2(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46])).
% 2.29/1.26  tff(c_228, plain, (![A_78]: (k6_yellow_1(k1_xboole_0, A_78)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_78))), inference(superposition, [status(thm), theory('equality')], [c_83, c_216])).
% 2.29/1.26  tff(c_236, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_228])).
% 2.29/1.26  tff(c_56, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.26  tff(c_241, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_56])).
% 2.29/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.29/1.26  tff(c_85, plain, (![A_49]: (v1_relat_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.26  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_85])).
% 2.29/1.26  tff(c_94, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.26  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.29/1.26  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_22])).
% 2.29/1.26  tff(c_64, plain, (![A_45]: (v1_funct_1(A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.26  tff(c_68, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_64])).
% 2.29/1.26  tff(c_30, plain, (![A_35]: (v1_partfun1(k6_partfun1(A_35), A_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.29/1.26  tff(c_112, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_30])).
% 2.29/1.26  tff(c_139, plain, (![A_54, B_55]: (v1_yellow_1(k2_funcop_1(A_54, B_55)) | ~l1_orders_2(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.29/1.26  tff(c_142, plain, (![A_48]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_48))), inference(superposition, [status(thm), theory('equality')], [c_83, c_139])).
% 2.29/1.26  tff(c_152, plain, (![A_48]: (~l1_orders_2(A_48))), inference(splitLeft, [status(thm)], [c_142])).
% 2.29/1.26  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.26  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_44])).
% 2.29/1.26  tff(c_156, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_142])).
% 2.29/1.26  tff(c_32, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.29/1.26  tff(c_179, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.29/1.26  tff(c_187, plain, (![A_35]: (v4_relat_1(k6_partfun1(A_35), A_35))), inference(resolution, [status(thm)], [c_32, c_179])).
% 2.29/1.26  tff(c_273, plain, (![A_97]: (k5_yellow_1(k1_xboole_0, A_97)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_97) | ~v1_partfun1(A_97, k1_xboole_0) | ~v1_funct_1(A_97) | ~v4_relat_1(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.26  tff(c_276, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k6_partfun1(k1_xboole_0)) | ~v1_yellow_1(k6_partfun1(k1_xboole_0)) | ~v1_partfun1(k6_partfun1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_relat_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_187, c_273])).
% 2.29/1.26  tff(c_281, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_100, c_68, c_100, c_112, c_100, c_156, c_100, c_100, c_276])).
% 2.29/1.26  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_281])).
% 2.29/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.26  
% 2.29/1.26  Inference rules
% 2.29/1.26  ----------------------
% 2.29/1.26  #Ref     : 0
% 2.29/1.26  #Sup     : 52
% 2.29/1.26  #Fact    : 0
% 2.29/1.26  #Define  : 0
% 2.29/1.26  #Split   : 1
% 2.29/1.26  #Chain   : 0
% 2.29/1.26  #Close   : 0
% 2.29/1.26  
% 2.29/1.26  Ordering : KBO
% 2.29/1.26  
% 2.29/1.26  Simplification rules
% 2.29/1.26  ----------------------
% 2.29/1.26  #Subsume      : 1
% 2.29/1.26  #Demod        : 20
% 2.29/1.26  #Tautology    : 37
% 2.29/1.26  #SimpNegUnit  : 3
% 2.29/1.26  #BackRed      : 5
% 2.29/1.26  
% 2.29/1.26  #Partial instantiations: 0
% 2.29/1.26  #Strategies tried      : 1
% 2.29/1.26  
% 2.29/1.26  Timing (in seconds)
% 2.29/1.26  ----------------------
% 2.41/1.26  Preprocessing        : 0.32
% 2.41/1.26  Parsing              : 0.17
% 2.41/1.26  CNF conversion       : 0.02
% 2.41/1.26  Main loop            : 0.19
% 2.41/1.26  Inferencing          : 0.07
% 2.41/1.26  Reduction            : 0.06
% 2.41/1.26  Demodulation         : 0.04
% 2.41/1.26  BG Simplification    : 0.01
% 2.41/1.26  Subsumption          : 0.02
% 2.41/1.26  Abstraction          : 0.01
% 2.41/1.26  MUC search           : 0.00
% 2.41/1.26  Cooper               : 0.00
% 2.41/1.26  Total                : 0.53
% 2.41/1.26  Index Insertion      : 0.00
% 2.41/1.26  Index Deletion       : 0.00
% 2.41/1.26  Index Matching       : 0.00
% 2.41/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
