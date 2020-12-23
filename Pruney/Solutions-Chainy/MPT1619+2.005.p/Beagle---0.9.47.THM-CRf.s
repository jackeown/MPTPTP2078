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

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   84 (  99 expanded)
%              Number of leaves         :   51 (  58 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 105 expanded)
%              Number of equality atoms :   23 (  29 expanded)
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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_84,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_78,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_63,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_53,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_74,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v7_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_98,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    ! [A_40] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_83,plain,(
    ! [A_40] : k2_funcop_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_52,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_183,plain,(
    ! [A_66,B_67] :
      ( k5_yellow_1(A_66,k2_funcop_1(A_66,B_67)) = k6_yellow_1(A_66,B_67)
      | ~ l1_orders_2(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46])).

tff(c_195,plain,(
    ! [A_68] :
      ( k6_yellow_1(k1_xboole_0,A_68) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_183])).

tff(c_203,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58,c_195])).

tff(c_56,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_208,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_56])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_86,plain,(
    ! [A_49] :
      ( v1_funct_1(A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_96,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_26])).

tff(c_30,plain,(
    ! [A_34] : v1_partfun1(k6_partfun1(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_30])).

tff(c_137,plain,(
    ! [A_57] : k2_funcop_1(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_48,plain,(
    ! [A_38,B_39] :
      ( v1_yellow_1(k2_funcop_1(A_38,B_39))
      | ~ l1_orders_2(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_142,plain,(
    ! [A_57] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_147,plain,(
    ! [A_57] : ~ l1_orders_2(A_57) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_44])).

tff(c_151,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_22,plain,(
    ! [A_31] : v4_relat_1(k1_xboole_0,A_31) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_249,plain,(
    ! [A_91] :
      ( k5_yellow_1(k1_xboole_0,A_91) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_91)
      | ~ v1_partfun1(A_91,k1_xboole_0)
      | ~ v1_funct_1(A_91)
      | ~ v4_relat_1(A_91,k1_xboole_0)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_252,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_255,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_94,c_123,c_151,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.15/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.29  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.15/1.29  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.15/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.15/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.15/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.29  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.15/1.29  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.15/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.29  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.15/1.29  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.15/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.15/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.29  
% 2.15/1.30  tff(f_103, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.15/1.30  tff(f_84, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.15/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.15/1.30  tff(f_86, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.15/1.30  tff(f_78, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.15/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.30  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.15/1.30  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.15/1.30  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.15/1.30  tff(f_53, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.15/1.30  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.15/1.30  tff(f_82, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.15/1.30  tff(f_74, axiom, (?[A]: ((((l1_orders_2(A) & ~v2_struct_0(A)) & v7_struct_0(A)) & v1_orders_2(A)) & v3_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_0)).
% 2.15/1.30  tff(f_52, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 2.15/1.30  tff(f_98, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.15/1.30  tff(c_58, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.15/1.30  tff(c_50, plain, (![A_40]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_40)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.15/1.30  tff(c_76, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.15/1.30  tff(c_83, plain, (![A_40]: (k2_funcop_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_76])).
% 2.15/1.30  tff(c_52, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.15/1.30  tff(c_46, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.30  tff(c_183, plain, (![A_66, B_67]: (k5_yellow_1(A_66, k2_funcop_1(A_66, B_67))=k6_yellow_1(A_66, B_67) | ~l1_orders_2(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46])).
% 2.15/1.30  tff(c_195, plain, (![A_68]: (k6_yellow_1(k1_xboole_0, A_68)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_68))), inference(superposition, [status(thm), theory('equality')], [c_83, c_183])).
% 2.15/1.30  tff(c_203, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_195])).
% 2.15/1.30  tff(c_56, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.15/1.30  tff(c_208, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_56])).
% 2.15/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.30  tff(c_67, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.30  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_67])).
% 2.15/1.30  tff(c_86, plain, (![A_49]: (v1_funct_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.30  tff(c_94, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.15/1.30  tff(c_96, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.30  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.30  tff(c_102, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_96, c_26])).
% 2.15/1.30  tff(c_30, plain, (![A_34]: (v1_partfun1(k6_partfun1(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.30  tff(c_123, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_30])).
% 2.15/1.30  tff(c_137, plain, (![A_57]: (k2_funcop_1(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_76])).
% 2.15/1.30  tff(c_48, plain, (![A_38, B_39]: (v1_yellow_1(k2_funcop_1(A_38, B_39)) | ~l1_orders_2(B_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.30  tff(c_142, plain, (![A_57]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_57))), inference(superposition, [status(thm), theory('equality')], [c_137, c_48])).
% 2.15/1.30  tff(c_147, plain, (![A_57]: (~l1_orders_2(A_57))), inference(splitLeft, [status(thm)], [c_142])).
% 2.15/1.30  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.30  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_44])).
% 2.15/1.30  tff(c_151, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_142])).
% 2.15/1.30  tff(c_22, plain, (![A_31]: (v4_relat_1(k1_xboole_0, A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.30  tff(c_249, plain, (![A_91]: (k5_yellow_1(k1_xboole_0, A_91)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_91) | ~v1_partfun1(A_91, k1_xboole_0) | ~v1_funct_1(A_91) | ~v4_relat_1(A_91, k1_xboole_0) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.15/1.30  tff(c_252, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_249])).
% 2.15/1.30  tff(c_255, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_94, c_123, c_151, c_252])).
% 2.15/1.30  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_255])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 0
% 2.15/1.30  #Sup     : 45
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 1
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.42/1.30  #Subsume      : 1
% 2.42/1.30  #Demod        : 13
% 2.42/1.30  #Tautology    : 35
% 2.42/1.30  #SimpNegUnit  : 3
% 2.42/1.30  #BackRed      : 6
% 2.42/1.30  
% 2.42/1.30  #Partial instantiations: 0
% 2.42/1.30  #Strategies tried      : 1
% 2.42/1.30  
% 2.42/1.30  Timing (in seconds)
% 2.42/1.30  ----------------------
% 2.42/1.30  Preprocessing        : 0.32
% 2.42/1.30  Parsing              : 0.17
% 2.42/1.30  CNF conversion       : 0.02
% 2.42/1.30  Main loop            : 0.18
% 2.42/1.30  Inferencing          : 0.07
% 2.42/1.30  Reduction            : 0.06
% 2.42/1.30  Demodulation         : 0.04
% 2.42/1.30  BG Simplification    : 0.01
% 2.42/1.30  Subsumption          : 0.02
% 2.42/1.30  Abstraction          : 0.01
% 2.42/1.30  MUC search           : 0.00
% 2.42/1.30  Cooper               : 0.00
% 2.42/1.30  Total                : 0.53
% 2.42/1.30  Index Insertion      : 0.00
% 2.42/1.30  Index Deletion       : 0.00
% 2.42/1.30  Index Matching       : 0.00
% 2.42/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
