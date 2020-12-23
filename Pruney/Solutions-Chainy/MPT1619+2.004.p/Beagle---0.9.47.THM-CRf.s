%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   80 (  96 expanded)
%              Number of leaves         :   48 (  55 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 102 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_77,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_71,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_67,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_orders_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_91,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [A_40] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_110,plain,(
    ! [A_40] : k2_funcop_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_46,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,(
    ! [A_65,B_66] :
      ( k5_yellow_1(A_65,k2_funcop_1(A_65,B_66)) = k6_yellow_1(A_65,B_66)
      | ~ l1_orders_2(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40])).

tff(c_187,plain,(
    ! [A_67] :
      ( k6_yellow_1(k1_xboole_0,A_67) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_175])).

tff(c_195,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_187])).

tff(c_50,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_209,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_50])).

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
    ! [A_50] :
      ( v1_funct_1(A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_94])).

tff(c_61,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_26])).

tff(c_30,plain,(
    ! [A_34] : v1_partfun1(k6_partfun1(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_30])).

tff(c_144,plain,(
    ! [A_57,B_58] :
      ( v1_yellow_1(k2_funcop_1(A_57,B_58))
      | ~ l1_orders_2(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [A_40] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_144])).

tff(c_157,plain,(
    ! [A_40] : ~ l1_orders_2(A_40) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_38,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_38])).

tff(c_161,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_22,plain,(
    ! [A_31] : v4_relat_1(k1_xboole_0,A_31) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_241,plain,(
    ! [A_90] :
      ( k5_yellow_1(k1_xboole_0,A_90) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_90)
      | ~ v1_partfun1(A_90,k1_xboole_0)
      | ~ v1_funct_1(A_90)
      | ~ v4_relat_1(A_90,k1_xboole_0)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_244,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_241])).

tff(c_247,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_102,c_79,c_161,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.25  % Computer   : n019.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.07/0.25  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.09  
% 1.84/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.10  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.07/1.10  
% 2.07/1.10  %Foreground sorts:
% 2.07/1.10  
% 2.07/1.10  
% 2.07/1.10  %Background operators:
% 2.07/1.10  
% 2.07/1.10  
% 2.07/1.10  %Foreground operators:
% 2.07/1.10  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.07/1.10  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.07/1.10  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.07/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.10  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.07/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.10  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.07/1.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.10  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.07/1.10  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.07/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.10  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.07/1.10  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.07/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.07/1.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.07/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.07/1.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.10  
% 2.07/1.11  tff(f_96, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.07/1.11  tff(f_77, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.07/1.11  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.11  tff(f_79, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.07/1.11  tff(f_71, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.07/1.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.11  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.07/1.11  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.07/1.11  tff(f_63, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.07/1.11  tff(f_53, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.07/1.11  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.07/1.11  tff(f_75, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.07/1.11  tff(f_67, axiom, (?[A]: (l1_orders_2(A) & v1_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_orders_2)).
% 2.07/1.11  tff(f_52, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 2.07/1.11  tff(f_91, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.07/1.11  tff(c_52, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.07/1.11  tff(c_44, plain, (![A_40]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_40)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.11  tff(c_103, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.07/1.11  tff(c_110, plain, (![A_40]: (k2_funcop_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_103])).
% 2.07/1.11  tff(c_46, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.11  tff(c_40, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.11  tff(c_175, plain, (![A_65, B_66]: (k5_yellow_1(A_65, k2_funcop_1(A_65, B_66))=k6_yellow_1(A_65, B_66) | ~l1_orders_2(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40])).
% 2.07/1.11  tff(c_187, plain, (![A_67]: (k6_yellow_1(k1_xboole_0, A_67)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_67))), inference(superposition, [status(thm), theory('equality')], [c_110, c_175])).
% 2.07/1.11  tff(c_195, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_187])).
% 2.07/1.11  tff(c_50, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.07/1.11  tff(c_209, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_50])).
% 2.07/1.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.07/1.11  tff(c_85, plain, (![A_49]: (v1_relat_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.11  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_85])).
% 2.07/1.11  tff(c_94, plain, (![A_50]: (v1_funct_1(A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.11  tff(c_102, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_94])).
% 2.07/1.11  tff(c_61, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.07/1.11  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.11  tff(c_67, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61, c_26])).
% 2.07/1.11  tff(c_30, plain, (![A_34]: (v1_partfun1(k6_partfun1(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.11  tff(c_79, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_30])).
% 2.07/1.11  tff(c_144, plain, (![A_57, B_58]: (v1_yellow_1(k2_funcop_1(A_57, B_58)) | ~l1_orders_2(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.11  tff(c_147, plain, (![A_40]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_40))), inference(superposition, [status(thm), theory('equality')], [c_110, c_144])).
% 2.07/1.11  tff(c_157, plain, (![A_40]: (~l1_orders_2(A_40))), inference(splitLeft, [status(thm)], [c_147])).
% 2.07/1.11  tff(c_38, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.07/1.11  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_38])).
% 2.07/1.11  tff(c_161, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_147])).
% 2.07/1.11  tff(c_22, plain, (![A_31]: (v4_relat_1(k1_xboole_0, A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.11  tff(c_241, plain, (![A_90]: (k5_yellow_1(k1_xboole_0, A_90)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_90) | ~v1_partfun1(A_90, k1_xboole_0) | ~v1_funct_1(A_90) | ~v4_relat_1(A_90, k1_xboole_0) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.07/1.11  tff(c_244, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_241])).
% 2.07/1.11  tff(c_247, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_102, c_79, c_161, c_244])).
% 2.07/1.11  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_247])).
% 2.07/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.11  
% 2.07/1.11  Inference rules
% 2.07/1.11  ----------------------
% 2.07/1.11  #Ref     : 0
% 2.07/1.11  #Sup     : 45
% 2.07/1.11  #Fact    : 0
% 2.07/1.11  #Define  : 0
% 2.07/1.11  #Split   : 1
% 2.07/1.11  #Chain   : 0
% 2.07/1.11  #Close   : 0
% 2.07/1.11  
% 2.07/1.11  Ordering : KBO
% 2.07/1.11  
% 2.07/1.11  Simplification rules
% 2.07/1.11  ----------------------
% 2.07/1.11  #Subsume      : 1
% 2.07/1.11  #Demod        : 13
% 2.07/1.11  #Tautology    : 35
% 2.07/1.11  #SimpNegUnit  : 3
% 2.07/1.11  #BackRed      : 5
% 2.07/1.11  
% 2.07/1.11  #Partial instantiations: 0
% 2.07/1.11  #Strategies tried      : 1
% 2.07/1.11  
% 2.07/1.11  Timing (in seconds)
% 2.07/1.11  ----------------------
% 2.07/1.11  Preprocessing        : 0.33
% 2.07/1.11  Parsing              : 0.18
% 2.07/1.11  CNF conversion       : 0.02
% 2.07/1.11  Main loop            : 0.17
% 2.07/1.11  Inferencing          : 0.07
% 2.07/1.11  Reduction            : 0.05
% 2.07/1.11  Demodulation         : 0.04
% 2.07/1.11  BG Simplification    : 0.01
% 2.07/1.11  Subsumption          : 0.02
% 2.07/1.11  Abstraction          : 0.01
% 2.07/1.11  MUC search           : 0.00
% 2.07/1.11  Cooper               : 0.00
% 2.07/1.11  Total                : 0.54
% 2.07/1.11  Index Insertion      : 0.00
% 2.07/1.11  Index Deletion       : 0.00
% 2.07/1.11  Index Matching       : 0.00
% 2.07/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
