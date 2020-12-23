%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 115 expanded)
%              Number of leaves         :   52 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 ( 126 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
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
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_orders_2)).

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

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_60,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,(
    ! [A_50] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_90,plain,(
    ! [A_50] : k2_funcop_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_54,plain,(
    ! [A_42,B_43] : k7_funcop_1(A_42,B_43) = k2_funcop_1(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( k5_yellow_1(A_37,k7_funcop_1(A_37,B_38)) = k6_yellow_1(A_37,B_38)
      | ~ l1_orders_2(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,(
    ! [A_69,B_70] :
      ( k5_yellow_1(A_69,k2_funcop_1(A_69,B_70)) = k6_yellow_1(A_69,B_70)
      | ~ l1_orders_2(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_216,plain,(
    ! [A_72] :
      ( k6_yellow_1(k1_xboole_0,A_72) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_203])).

tff(c_224,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_216])).

tff(c_58,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_229,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_106,plain,(
    ! [A_52] :
      ( v1_relat_1(A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_91,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_32])).

tff(c_42,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ! [A_34] : v1_funct_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_34] : v1_funct_1(k6_partfun1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_120,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_62])).

tff(c_38,plain,(
    ! [A_35] : v1_partfun1(k6_partfun1(A_35),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_38])).

tff(c_156,plain,(
    ! [A_57,B_58] :
      ( v1_yellow_1(k2_funcop_1(A_57,B_58))
      | ~ l1_orders_2(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_159,plain,(
    ! [A_50] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_156])).

tff(c_160,plain,(
    ! [A_50] : ~ l1_orders_2(A_50) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_46])).

tff(c_164,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_193,plain,(
    ! [B_67,A_68] :
      ( v4_relat_1(B_67,A_68)
      | ~ r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_199,plain,(
    ! [A_68] :
      ( v4_relat_1(k1_xboole_0,A_68)
      | ~ r1_tarski(k1_xboole_0,A_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_193])).

tff(c_202,plain,(
    ! [A_68] : v4_relat_1(k1_xboole_0,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_6,c_199])).

tff(c_270,plain,(
    ! [A_95] :
      ( k5_yellow_1(k1_xboole_0,A_95) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_95)
      | ~ v1_partfun1(A_95,k1_xboole_0)
      | ~ v1_funct_1(A_95)
      | ~ v4_relat_1(A_95,k1_xboole_0)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_273,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_202,c_270])).

tff(c_276,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_120,c_118,c_164,c_273])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:53:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  
% 2.44/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  %$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.44/1.32  
% 2.44/1.32  %Foreground sorts:
% 2.44/1.32  
% 2.44/1.32  
% 2.44/1.32  %Background operators:
% 2.44/1.32  
% 2.44/1.32  
% 2.44/1.32  %Foreground operators:
% 2.44/1.32  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.44/1.32  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.44/1.32  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.44/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.32  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.44/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.32  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.44/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.32  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.44/1.32  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.44/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.44/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.44/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.44/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.44/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.32  
% 2.44/1.34  tff(f_103, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.44/1.34  tff(f_84, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.44/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.44/1.34  tff(f_86, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.44/1.34  tff(f_78, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.44/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.34  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.44/1.34  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.44/1.34  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.44/1.34  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.44/1.34  tff(f_68, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.44/1.34  tff(f_82, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.44/1.34  tff(f_74, axiom, (?[A]: (l1_orders_2(A) & v1_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_orders_2)).
% 2.44/1.34  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.44/1.34  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.44/1.34  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.44/1.34  tff(f_98, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.44/1.34  tff(c_60, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.34  tff(c_86, plain, (![A_50]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_50)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.44/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.44/1.34  tff(c_90, plain, (![A_50]: (k2_funcop_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_4])).
% 2.44/1.34  tff(c_54, plain, (![A_42, B_43]: (k7_funcop_1(A_42, B_43)=k2_funcop_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.44/1.34  tff(c_48, plain, (![A_37, B_38]: (k5_yellow_1(A_37, k7_funcop_1(A_37, B_38))=k6_yellow_1(A_37, B_38) | ~l1_orders_2(B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.34  tff(c_203, plain, (![A_69, B_70]: (k5_yellow_1(A_69, k2_funcop_1(A_69, B_70))=k6_yellow_1(A_69, B_70) | ~l1_orders_2(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 2.44/1.34  tff(c_216, plain, (![A_72]: (k6_yellow_1(k1_xboole_0, A_72)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_72))), inference(superposition, [status(thm), theory('equality')], [c_90, c_203])).
% 2.44/1.34  tff(c_224, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_216])).
% 2.44/1.34  tff(c_58, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.34  tff(c_229, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_58])).
% 2.44/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.44/1.34  tff(c_106, plain, (![A_52]: (v1_relat_1(A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.34  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_106])).
% 2.44/1.34  tff(c_91, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.34  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.44/1.34  tff(c_97, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91, c_32])).
% 2.44/1.34  tff(c_42, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.34  tff(c_36, plain, (![A_34]: (v1_funct_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.34  tff(c_62, plain, (![A_34]: (v1_funct_1(k6_partfun1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 2.44/1.34  tff(c_120, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_62])).
% 2.44/1.34  tff(c_38, plain, (![A_35]: (v1_partfun1(k6_partfun1(A_35), A_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.34  tff(c_118, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_38])).
% 2.44/1.34  tff(c_156, plain, (![A_57, B_58]: (v1_yellow_1(k2_funcop_1(A_57, B_58)) | ~l1_orders_2(B_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.44/1.34  tff(c_159, plain, (![A_50]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_50))), inference(superposition, [status(thm), theory('equality')], [c_90, c_156])).
% 2.44/1.34  tff(c_160, plain, (![A_50]: (~l1_orders_2(A_50))), inference(splitLeft, [status(thm)], [c_159])).
% 2.44/1.34  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.34  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_46])).
% 2.44/1.34  tff(c_164, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_159])).
% 2.44/1.34  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.34  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.34  tff(c_193, plain, (![B_67, A_68]: (v4_relat_1(B_67, A_68) | ~r1_tarski(k1_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.44/1.34  tff(c_199, plain, (![A_68]: (v4_relat_1(k1_xboole_0, A_68) | ~r1_tarski(k1_xboole_0, A_68) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_193])).
% 2.44/1.34  tff(c_202, plain, (![A_68]: (v4_relat_1(k1_xboole_0, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_6, c_199])).
% 2.44/1.34  tff(c_270, plain, (![A_95]: (k5_yellow_1(k1_xboole_0, A_95)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_95) | ~v1_partfun1(A_95, k1_xboole_0) | ~v1_funct_1(A_95) | ~v4_relat_1(A_95, k1_xboole_0) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.44/1.34  tff(c_273, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_270])).
% 2.44/1.34  tff(c_276, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_120, c_118, c_164, c_273])).
% 2.44/1.34  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_276])).
% 2.44/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  Inference rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Ref     : 0
% 2.44/1.34  #Sup     : 52
% 2.44/1.34  #Fact    : 0
% 2.44/1.34  #Define  : 0
% 2.44/1.34  #Split   : 1
% 2.44/1.34  #Chain   : 0
% 2.44/1.34  #Close   : 0
% 2.44/1.34  
% 2.44/1.34  Ordering : KBO
% 2.44/1.34  
% 2.44/1.34  Simplification rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Subsume      : 1
% 2.44/1.34  #Demod        : 18
% 2.44/1.34  #Tautology    : 41
% 2.44/1.34  #SimpNegUnit  : 3
% 2.44/1.34  #BackRed      : 4
% 2.44/1.34  
% 2.44/1.34  #Partial instantiations: 0
% 2.44/1.34  #Strategies tried      : 1
% 2.44/1.34  
% 2.44/1.34  Timing (in seconds)
% 2.44/1.34  ----------------------
% 2.44/1.34  Preprocessing        : 0.35
% 2.44/1.34  Parsing              : 0.19
% 2.44/1.34  CNF conversion       : 0.02
% 2.44/1.34  Main loop            : 0.19
% 2.44/1.34  Inferencing          : 0.07
% 2.44/1.34  Reduction            : 0.06
% 2.44/1.34  Demodulation         : 0.05
% 2.44/1.34  BG Simplification    : 0.02
% 2.44/1.34  Subsumption          : 0.02
% 2.44/1.34  Abstraction          : 0.01
% 2.44/1.34  MUC search           : 0.00
% 2.44/1.34  Cooper               : 0.00
% 2.44/1.34  Total                : 0.57
% 2.44/1.34  Index Insertion      : 0.00
% 2.44/1.34  Index Deletion       : 0.00
% 2.44/1.34  Index Matching       : 0.00
% 2.44/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
