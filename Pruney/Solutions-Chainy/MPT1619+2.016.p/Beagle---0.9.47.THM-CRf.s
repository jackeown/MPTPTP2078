%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 130 expanded)
%              Number of leaves         :   53 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 139 expanded)
%              Number of equality atoms :   26 (  53 expanded)
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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_86,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
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

tff(f_65,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_63,axiom,(
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
      & ~ v2_struct_0(A)
      & v7_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_0)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
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

tff(c_62,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_106,plain,(
    ! [A_49] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_49] : k2_funcop_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_56,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,(
    ! [A_68,B_69] :
      ( k5_yellow_1(A_68,k2_funcop_1(A_68,B_69)) = k6_yellow_1(A_68,B_69)
      | ~ l1_orders_2(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_206,plain,(
    ! [A_70] :
      ( k6_yellow_1(k1_xboole_0,A_70) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_194])).

tff(c_214,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_62,c_206])).

tff(c_60,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_215,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_60])).

tff(c_81,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_28])).

tff(c_38,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_33] : v1_relat_1(k6_partfun1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_65])).

tff(c_32,plain,(
    ! [A_33] : v1_funct_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_33] : v1_funct_1(k6_partfun1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_100,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_64])).

tff(c_111,plain,(
    ! [A_50] : v1_partfun1(k6_partfun1(A_50),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_111])).

tff(c_146,plain,(
    ! [A_55,B_56] :
      ( v1_yellow_1(k2_funcop_1(A_55,B_56))
      | ~ l1_orders_2(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_149,plain,(
    ! [A_49] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_146])).

tff(c_150,plain,(
    ! [A_49] : ~ l1_orders_2(A_49) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_48])).

tff(c_154,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_177,plain,(
    ! [B_63,A_64] :
      ( v4_relat_1(B_63,A_64)
      | ~ r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_64] :
      ( v4_relat_1(k1_xboole_0,A_64)
      | ~ r1_tarski(k1_xboole_0,A_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_177])).

tff(c_182,plain,(
    ! [A_64] : v4_relat_1(k1_xboole_0,A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_4,c_180])).

tff(c_260,plain,(
    ! [A_93] :
      ( k5_yellow_1(k1_xboole_0,A_93) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_93)
      | ~ v1_partfun1(A_93,k1_xboole_0)
      | ~ v1_funct_1(A_93)
      | ~ v4_relat_1(A_93,k1_xboole_0)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_263,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_182,c_260])).

tff(c_266,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_100,c_114,c_154,c_263])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:44:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.26  
% 2.32/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.26  %$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v7_struct_0 > v3_orders_2 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.32/1.26  
% 2.32/1.26  %Foreground sorts:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Background operators:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Foreground operators:
% 2.32/1.26  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.32/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.26  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.32/1.26  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.32/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.32/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.26  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.32/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.26  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.32/1.26  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.32/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.26  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.32/1.26  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.32/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.32/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.32/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.26  
% 2.32/1.28  tff(f_105, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.32/1.28  tff(f_86, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.32/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.32/1.28  tff(f_88, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.32/1.28  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.32/1.28  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.32/1.28  tff(f_55, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.32/1.28  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.32/1.28  tff(f_63, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.32/1.28  tff(f_84, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.32/1.28  tff(f_76, axiom, (?[A]: ((((l1_orders_2(A) & ~v2_struct_0(A)) & v7_struct_0(A)) & v1_orders_2(A)) & v3_orders_2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_yellow_0)).
% 2.32/1.28  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.32/1.28  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.32/1.28  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.32/1.28  tff(f_100, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.32/1.28  tff(c_62, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.32/1.28  tff(c_106, plain, (![A_49]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_49)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.32/1.28  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.28  tff(c_110, plain, (![A_49]: (k2_funcop_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.32/1.28  tff(c_56, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.32/1.28  tff(c_50, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.28  tff(c_194, plain, (![A_68, B_69]: (k5_yellow_1(A_68, k2_funcop_1(A_68, B_69))=k6_yellow_1(A_68, B_69) | ~l1_orders_2(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 2.32/1.28  tff(c_206, plain, (![A_70]: (k6_yellow_1(k1_xboole_0, A_70)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_70))), inference(superposition, [status(thm), theory('equality')], [c_110, c_194])).
% 2.32/1.28  tff(c_214, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_206])).
% 2.32/1.28  tff(c_60, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.32/1.28  tff(c_215, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_60])).
% 2.32/1.28  tff(c_81, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.28  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.32/1.28  tff(c_87, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_81, c_28])).
% 2.32/1.28  tff(c_38, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.28  tff(c_30, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.28  tff(c_65, plain, (![A_33]: (v1_relat_1(k6_partfun1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30])).
% 2.32/1.28  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_65])).
% 2.32/1.28  tff(c_32, plain, (![A_33]: (v1_funct_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.28  tff(c_64, plain, (![A_33]: (v1_funct_1(k6_partfun1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.32/1.28  tff(c_100, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_64])).
% 2.32/1.28  tff(c_111, plain, (![A_50]: (v1_partfun1(k6_partfun1(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.28  tff(c_114, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_111])).
% 2.32/1.28  tff(c_146, plain, (![A_55, B_56]: (v1_yellow_1(k2_funcop_1(A_55, B_56)) | ~l1_orders_2(B_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.32/1.28  tff(c_149, plain, (![A_49]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_110, c_146])).
% 2.32/1.28  tff(c_150, plain, (![A_49]: (~l1_orders_2(A_49))), inference(splitLeft, [status(thm)], [c_149])).
% 2.32/1.28  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.32/1.28  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_48])).
% 2.32/1.28  tff(c_154, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_149])).
% 2.32/1.28  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.28  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.28  tff(c_177, plain, (![B_63, A_64]: (v4_relat_1(B_63, A_64) | ~r1_tarski(k1_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.28  tff(c_180, plain, (![A_64]: (v4_relat_1(k1_xboole_0, A_64) | ~r1_tarski(k1_xboole_0, A_64) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_177])).
% 2.32/1.28  tff(c_182, plain, (![A_64]: (v4_relat_1(k1_xboole_0, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_4, c_180])).
% 2.32/1.28  tff(c_260, plain, (![A_93]: (k5_yellow_1(k1_xboole_0, A_93)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_93) | ~v1_partfun1(A_93, k1_xboole_0) | ~v1_funct_1(A_93) | ~v4_relat_1(A_93, k1_xboole_0) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.28  tff(c_263, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_182, c_260])).
% 2.32/1.28  tff(c_266, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_100, c_114, c_154, c_263])).
% 2.32/1.28  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_266])).
% 2.32/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.28  
% 2.32/1.28  Inference rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Ref     : 0
% 2.32/1.28  #Sup     : 50
% 2.32/1.28  #Fact    : 0
% 2.32/1.28  #Define  : 0
% 2.32/1.28  #Split   : 1
% 2.32/1.28  #Chain   : 0
% 2.32/1.28  #Close   : 0
% 2.32/1.28  
% 2.32/1.28  Ordering : KBO
% 2.32/1.28  
% 2.32/1.28  Simplification rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Subsume      : 1
% 2.32/1.28  #Demod        : 14
% 2.32/1.28  #Tautology    : 38
% 2.32/1.28  #SimpNegUnit  : 3
% 2.32/1.28  #BackRed      : 4
% 2.32/1.28  
% 2.32/1.28  #Partial instantiations: 0
% 2.32/1.28  #Strategies tried      : 1
% 2.32/1.28  
% 2.32/1.28  Timing (in seconds)
% 2.32/1.28  ----------------------
% 2.32/1.28  Preprocessing        : 0.33
% 2.32/1.28  Parsing              : 0.18
% 2.32/1.28  CNF conversion       : 0.02
% 2.32/1.28  Main loop            : 0.19
% 2.32/1.28  Inferencing          : 0.07
% 2.32/1.28  Reduction            : 0.06
% 2.32/1.28  Demodulation         : 0.05
% 2.32/1.28  BG Simplification    : 0.01
% 2.32/1.28  Subsumption          : 0.02
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.55
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
