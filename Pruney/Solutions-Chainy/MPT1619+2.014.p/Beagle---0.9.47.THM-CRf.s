%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 128 expanded)
%              Number of leaves         :   49 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 135 expanded)
%              Number of equality atoms :   23 (  58 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_82,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_61,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_72,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v7_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [A_40] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_40] : k2_funcop_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_52,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_214,plain,(
    ! [A_76,B_77] :
      ( k5_yellow_1(A_76,k2_funcop_1(A_76,B_77)) = k6_yellow_1(A_76,B_77)
      | ~ l1_orders_2(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46])).

tff(c_226,plain,(
    ! [A_78] :
      ( k6_yellow_1(k1_xboole_0,A_78) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_214])).

tff(c_234,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58,c_226])).

tff(c_56,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_239,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_56])).

tff(c_68,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_34,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [A_30] : v1_relat_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_61])).

tff(c_24,plain,(
    ! [A_30] : v1_funct_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_30] : v1_funct_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_85,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_60])).

tff(c_30,plain,(
    ! [A_34] : v1_partfun1(k6_partfun1(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_52,B_53] :
      ( v1_yellow_1(k2_funcop_1(A_52,B_53))
      | ~ l1_orders_2(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_131,plain,(
    ! [A_40] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_128])).

tff(c_132,plain,(
    ! [A_40] : ~ l1_orders_2(A_40) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_44])).

tff(c_145,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_32,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [A_34] : v4_relat_1(k6_partfun1(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_271,plain,(
    ! [A_97] :
      ( k5_yellow_1(k1_xboole_0,A_97) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_97)
      | ~ v1_partfun1(A_97,k1_xboole_0)
      | ~ v1_funct_1(A_97)
      | ~ v4_relat_1(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_274,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | ~ v1_yellow_1(k6_partfun1(k1_xboole_0))
    | ~ v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_194,c_271])).

tff(c_279,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_74,c_85,c_74,c_30,c_145,c_74,c_74,c_274])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.21/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.34  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.21/1.34  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.21/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.21/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.21/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.34  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.21/1.34  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.21/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.34  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.21/1.34  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.21/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.21/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.34  
% 2.51/1.36  tff(f_101, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.51/1.36  tff(f_82, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.51/1.36  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.51/1.36  tff(f_84, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.51/1.36  tff(f_76, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.51/1.36  tff(f_61, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.51/1.36  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.51/1.36  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.51/1.36  tff(f_59, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.51/1.36  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.51/1.36  tff(f_72, axiom, (?[A]: ((((l1_orders_2(A) & ~v2_struct_0(A)) & v7_struct_0(A)) & v1_orders_2(A)) & v3_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_0)).
% 2.51/1.36  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.36  tff(f_96, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.51/1.36  tff(c_58, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.36  tff(c_50, plain, (![A_40]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_40)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.51/1.36  tff(c_93, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.36  tff(c_97, plain, (![A_40]: (k2_funcop_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_93])).
% 2.51/1.36  tff(c_52, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.51/1.36  tff(c_46, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.36  tff(c_214, plain, (![A_76, B_77]: (k5_yellow_1(A_76, k2_funcop_1(A_76, B_77))=k6_yellow_1(A_76, B_77) | ~l1_orders_2(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46])).
% 2.51/1.36  tff(c_226, plain, (![A_78]: (k6_yellow_1(k1_xboole_0, A_78)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_78))), inference(superposition, [status(thm), theory('equality')], [c_97, c_214])).
% 2.51/1.36  tff(c_234, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_226])).
% 2.51/1.36  tff(c_56, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.36  tff(c_239, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_234, c_56])).
% 2.51/1.36  tff(c_68, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.36  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.36  tff(c_74, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_68, c_20])).
% 2.51/1.36  tff(c_34, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.36  tff(c_22, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.36  tff(c_61, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22])).
% 2.51/1.36  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_61])).
% 2.51/1.36  tff(c_24, plain, (![A_30]: (v1_funct_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.36  tff(c_60, plain, (![A_30]: (v1_funct_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 2.51/1.36  tff(c_85, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_60])).
% 2.51/1.36  tff(c_30, plain, (![A_34]: (v1_partfun1(k6_partfun1(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.36  tff(c_128, plain, (![A_52, B_53]: (v1_yellow_1(k2_funcop_1(A_52, B_53)) | ~l1_orders_2(B_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.51/1.36  tff(c_131, plain, (![A_40]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_40))), inference(superposition, [status(thm), theory('equality')], [c_97, c_128])).
% 2.51/1.36  tff(c_132, plain, (![A_40]: (~l1_orders_2(A_40))), inference(splitLeft, [status(thm)], [c_131])).
% 2.51/1.36  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.36  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_44])).
% 2.51/1.36  tff(c_145, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_131])).
% 2.51/1.36  tff(c_32, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.36  tff(c_186, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.36  tff(c_194, plain, (![A_34]: (v4_relat_1(k6_partfun1(A_34), A_34))), inference(resolution, [status(thm)], [c_32, c_186])).
% 2.51/1.36  tff(c_271, plain, (![A_97]: (k5_yellow_1(k1_xboole_0, A_97)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_97) | ~v1_partfun1(A_97, k1_xboole_0) | ~v1_funct_1(A_97) | ~v4_relat_1(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.51/1.36  tff(c_274, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k6_partfun1(k1_xboole_0)) | ~v1_yellow_1(k6_partfun1(k1_xboole_0)) | ~v1_partfun1(k6_partfun1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_relat_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_194, c_271])).
% 2.51/1.36  tff(c_279, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_74, c_85, c_74, c_30, c_145, c_74, c_74, c_274])).
% 2.51/1.36  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_279])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 54
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 1
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 1
% 2.51/1.36  #Demod        : 16
% 2.51/1.36  #Tautology    : 38
% 2.51/1.36  #SimpNegUnit  : 3
% 2.51/1.36  #BackRed      : 4
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.35
% 2.51/1.36  Parsing              : 0.18
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.22
% 2.51/1.36  Inferencing          : 0.08
% 2.51/1.36  Reduction            : 0.07
% 2.51/1.36  Demodulation         : 0.05
% 2.51/1.36  BG Simplification    : 0.01
% 2.51/1.36  Subsumption          : 0.03
% 2.51/1.36  Abstraction          : 0.02
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.61
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
