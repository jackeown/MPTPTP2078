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
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 115 expanded)
%              Number of leaves         :   52 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :   92 ( 127 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_66,axiom,(
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
      & v2_struct_0(A)
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_orders_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
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

tff(c_52,plain,(
    ! [A_34] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_88,plain,(
    ! [A_34] : k2_funcop_1(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_54,plain,(
    ! [A_35,B_36] : k7_funcop_1(A_35,B_36) = k2_funcop_1(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( k5_yellow_1(A_30,k7_funcop_1(A_30,B_31)) = k6_yellow_1(A_30,B_31)
      | ~ l1_orders_2(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,(
    ! [A_63,B_64] :
      ( k5_yellow_1(A_63,k2_funcop_1(A_63,B_64)) = k6_yellow_1(A_63,B_64)
      | ~ l1_orders_2(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_216,plain,(
    ! [A_65] :
      ( k6_yellow_1(k1_xboole_0,A_65) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_204])).

tff(c_224,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_216])).

tff(c_58,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_225,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_91,plain,(
    ! [A_44] :
      ( v1_relat_1(A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_100,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_30])).

tff(c_40,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [A_27] : v1_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62,plain,(
    ! [A_27] : v1_funct_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_120,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_62])).

tff(c_36,plain,(
    ! [A_28] : v1_partfun1(k6_partfun1(A_28),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_118,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_36])).

tff(c_156,plain,(
    ! [A_50,B_51] :
      ( v1_yellow_1(k2_funcop_1(A_50,B_51))
      | ~ l1_orders_2(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_159,plain,(
    ! [A_34] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_156])).

tff(c_160,plain,(
    ! [A_34] : ~ l1_orders_2(A_34) ),
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

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [B_55,A_56] :
      ( v4_relat_1(B_55,A_56)
      | ~ r1_tarski(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_181,plain,(
    ! [A_56] :
      ( v4_relat_1(k1_xboole_0,A_56)
      | ~ r1_tarski(k1_xboole_0,A_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_178])).

tff(c_183,plain,(
    ! [A_56] : v4_relat_1(k1_xboole_0,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_6,c_181])).

tff(c_261,plain,(
    ! [A_81] :
      ( k5_yellow_1(k1_xboole_0,A_81) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_81)
      | ~ v1_partfun1(A_81,k1_xboole_0)
      | ~ v1_funct_1(A_81)
      | ~ v4_relat_1(A_81,k1_xboole_0)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_264,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_183,c_261])).

tff(c_267,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_120,c_118,c_164,c_264])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  %$ v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.20/1.29  
% 2.20/1.29  %Foreground sorts:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Background operators:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Foreground operators:
% 2.20/1.29  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.20/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.29  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.20/1.29  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.20/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.29  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.20/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.29  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.20/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.29  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.20/1.29  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.20/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.29  
% 2.49/1.31  tff(f_103, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.49/1.31  tff(f_84, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.49/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.49/1.31  tff(f_86, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.49/1.31  tff(f_78, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.49/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.49/1.31  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.49/1.31  tff(f_68, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.49/1.31  tff(f_58, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.49/1.31  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.49/1.31  tff(f_66, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.49/1.31  tff(f_82, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.49/1.31  tff(f_74, axiom, (?[A]: ((l1_orders_2(A) & v2_struct_0(A)) & v1_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_orders_2)).
% 2.49/1.31  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.31  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.49/1.31  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.49/1.31  tff(f_98, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.49/1.31  tff(c_60, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.31  tff(c_52, plain, (![A_34]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_34)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.31  tff(c_81, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.49/1.31  tff(c_88, plain, (![A_34]: (k2_funcop_1(k1_xboole_0, A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_81])).
% 2.49/1.31  tff(c_54, plain, (![A_35, B_36]: (k7_funcop_1(A_35, B_36)=k2_funcop_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.31  tff(c_48, plain, (![A_30, B_31]: (k5_yellow_1(A_30, k7_funcop_1(A_30, B_31))=k6_yellow_1(A_30, B_31) | ~l1_orders_2(B_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.49/1.31  tff(c_204, plain, (![A_63, B_64]: (k5_yellow_1(A_63, k2_funcop_1(A_63, B_64))=k6_yellow_1(A_63, B_64) | ~l1_orders_2(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 2.49/1.31  tff(c_216, plain, (![A_65]: (k6_yellow_1(k1_xboole_0, A_65)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_65))), inference(superposition, [status(thm), theory('equality')], [c_88, c_204])).
% 2.49/1.31  tff(c_224, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_216])).
% 2.49/1.31  tff(c_58, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.31  tff(c_225, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_58])).
% 2.49/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.49/1.31  tff(c_91, plain, (![A_44]: (v1_relat_1(A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.31  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_91])).
% 2.49/1.31  tff(c_100, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.31  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.31  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_30])).
% 2.49/1.31  tff(c_40, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.31  tff(c_34, plain, (![A_27]: (v1_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.49/1.31  tff(c_62, plain, (![A_27]: (v1_funct_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 2.49/1.31  tff(c_120, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_62])).
% 2.49/1.31  tff(c_36, plain, (![A_28]: (v1_partfun1(k6_partfun1(A_28), A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.31  tff(c_118, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_36])).
% 2.49/1.31  tff(c_156, plain, (![A_50, B_51]: (v1_yellow_1(k2_funcop_1(A_50, B_51)) | ~l1_orders_2(B_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.49/1.31  tff(c_159, plain, (![A_34]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_34))), inference(superposition, [status(thm), theory('equality')], [c_88, c_156])).
% 2.49/1.31  tff(c_160, plain, (![A_34]: (~l1_orders_2(A_34))), inference(splitLeft, [status(thm)], [c_159])).
% 2.49/1.31  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.31  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_46])).
% 2.49/1.31  tff(c_164, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_159])).
% 2.49/1.31  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.31  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.31  tff(c_178, plain, (![B_55, A_56]: (v4_relat_1(B_55, A_56) | ~r1_tarski(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.31  tff(c_181, plain, (![A_56]: (v4_relat_1(k1_xboole_0, A_56) | ~r1_tarski(k1_xboole_0, A_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_178])).
% 2.49/1.31  tff(c_183, plain, (![A_56]: (v4_relat_1(k1_xboole_0, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_6, c_181])).
% 2.49/1.31  tff(c_261, plain, (![A_81]: (k5_yellow_1(k1_xboole_0, A_81)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_81) | ~v1_partfun1(A_81, k1_xboole_0) | ~v1_funct_1(A_81) | ~v4_relat_1(A_81, k1_xboole_0) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.49/1.31  tff(c_264, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_183, c_261])).
% 2.49/1.31  tff(c_267, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_120, c_118, c_164, c_264])).
% 2.49/1.31  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_267])).
% 2.49/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.31  
% 2.49/1.31  Inference rules
% 2.49/1.31  ----------------------
% 2.49/1.31  #Ref     : 0
% 2.49/1.31  #Sup     : 50
% 2.49/1.31  #Fact    : 0
% 2.49/1.31  #Define  : 0
% 2.49/1.31  #Split   : 1
% 2.49/1.31  #Chain   : 0
% 2.49/1.31  #Close   : 0
% 2.49/1.31  
% 2.49/1.31  Ordering : KBO
% 2.49/1.31  
% 2.49/1.31  Simplification rules
% 2.49/1.31  ----------------------
% 2.49/1.31  #Subsume      : 1
% 2.49/1.31  #Demod        : 19
% 2.49/1.31  #Tautology    : 39
% 2.49/1.31  #SimpNegUnit  : 3
% 2.49/1.31  #BackRed      : 4
% 2.49/1.31  
% 2.49/1.31  #Partial instantiations: 0
% 2.49/1.31  #Strategies tried      : 1
% 2.49/1.31  
% 2.49/1.31  Timing (in seconds)
% 2.49/1.31  ----------------------
% 2.49/1.31  Preprocessing        : 0.34
% 2.49/1.31  Parsing              : 0.18
% 2.49/1.31  CNF conversion       : 0.02
% 2.49/1.31  Main loop            : 0.20
% 2.49/1.31  Inferencing          : 0.07
% 2.49/1.31  Reduction            : 0.07
% 2.49/1.31  Demodulation         : 0.05
% 2.49/1.31  BG Simplification    : 0.02
% 2.49/1.31  Subsumption          : 0.03
% 2.49/1.31  Abstraction          : 0.01
% 2.49/1.31  MUC search           : 0.00
% 2.49/1.31  Cooper               : 0.00
% 2.49/1.31  Total                : 0.57
% 2.49/1.31  Index Insertion      : 0.00
% 2.49/1.31  Index Deletion       : 0.00
% 2.49/1.31  Index Matching       : 0.00
% 2.49/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
