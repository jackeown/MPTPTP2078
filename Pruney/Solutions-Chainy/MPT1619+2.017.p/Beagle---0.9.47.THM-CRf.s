%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 103 expanded)
%              Number of leaves         :   53 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :   85 ( 116 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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

tff(f_29,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_70,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
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
      & v2_struct_0(A)
      & v1_orders_2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_orders_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_100,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_109,plain,(
    ! [A_49] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_49] : k2_funcop_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_58,plain,(
    ! [A_41,B_42] : k7_funcop_1(A_41,B_42) = k2_funcop_1(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    ! [A_36,B_37] :
      ( k5_yellow_1(A_36,k7_funcop_1(A_36,B_37)) = k6_yellow_1(A_36,B_37)
      | ~ l1_orders_2(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_193,plain,(
    ! [A_67,B_68] :
      ( k5_yellow_1(A_67,k2_funcop_1(A_67,B_68)) = k6_yellow_1(A_67,B_68)
      | ~ l1_orders_2(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52])).

tff(c_205,plain,(
    ! [A_69] :
      ( k6_yellow_1(k1_xboole_0,A_69) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_193])).

tff(c_213,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_205])).

tff(c_62,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_218,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_62])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_40,plain,(
    ! [A_34] : v1_partfun1(k6_partfun1(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_104,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_40])).

tff(c_145,plain,(
    ! [A_54,B_55] :
      ( v1_yellow_1(k2_funcop_1(A_54,B_55))
      | ~ l1_orders_2(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [A_49] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_145])).

tff(c_149,plain,(
    ! [A_49] : ~ l1_orders_2(A_49) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_50,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_50])).

tff(c_153,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_167,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(B_59,A_60)
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    ! [A_60] :
      ( v4_relat_1(k1_xboole_0,A_60)
      | ~ r1_tarski(k1_xboole_0,A_60)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_167])).

tff(c_172,plain,(
    ! [A_60] : v4_relat_1(k1_xboole_0,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4,c_170])).

tff(c_259,plain,(
    ! [A_92] :
      ( k5_yellow_1(k1_xboole_0,A_92) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_92)
      | ~ v1_partfun1(A_92,k1_xboole_0)
      | ~ v1_funct_1(A_92)
      | ~ v4_relat_1(A_92,k1_xboole_0)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_262,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_172,c_259])).

tff(c_265,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_104,c_153,c_262])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_struct_0 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.30/1.28  
% 2.30/1.28  %Foreground sorts:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Background operators:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Foreground operators:
% 2.30/1.28  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.30/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.28  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.30/1.28  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.30/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.28  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.30/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.28  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.30/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.28  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.30/1.28  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.30/1.28  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.30/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.30/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.30/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.30/1.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.30/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.28  
% 2.30/1.29  tff(f_105, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.30/1.29  tff(f_86, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.30/1.29  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.30/1.29  tff(f_88, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.30/1.29  tff(f_80, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.30/1.29  tff(f_64, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 2.30/1.29  tff(f_70, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.30/1.29  tff(f_56, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.30/1.29  tff(f_68, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.30/1.29  tff(f_84, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.30/1.29  tff(f_76, axiom, (?[A]: ((l1_orders_2(A) & v2_struct_0(A)) & v1_orders_2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_orders_2)).
% 2.30/1.29  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.30/1.29  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.30/1.29  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.30/1.29  tff(f_100, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.30/1.29  tff(c_64, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_109, plain, (![A_49]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_49)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.30/1.29  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.29  tff(c_113, plain, (![A_49]: (k2_funcop_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.30/1.29  tff(c_58, plain, (![A_41, B_42]: (k7_funcop_1(A_41, B_42)=k2_funcop_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.30/1.29  tff(c_52, plain, (![A_36, B_37]: (k5_yellow_1(A_36, k7_funcop_1(A_36, B_37))=k6_yellow_1(A_36, B_37) | ~l1_orders_2(B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.30/1.29  tff(c_193, plain, (![A_67, B_68]: (k5_yellow_1(A_67, k2_funcop_1(A_67, B_68))=k6_yellow_1(A_67, B_68) | ~l1_orders_2(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52])).
% 2.30/1.29  tff(c_205, plain, (![A_69]: (k6_yellow_1(k1_xboole_0, A_69)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_69))), inference(superposition, [status(thm), theory('equality')], [c_113, c_193])).
% 2.30/1.29  tff(c_213, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_205])).
% 2.30/1.29  tff(c_62, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_218, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_62])).
% 2.30/1.29  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.30/1.29  tff(c_36, plain, (v1_funct_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.30/1.29  tff(c_86, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.30/1.29  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.29  tff(c_92, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_86, c_30])).
% 2.30/1.29  tff(c_40, plain, (![A_34]: (v1_partfun1(k6_partfun1(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.29  tff(c_104, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_40])).
% 2.30/1.29  tff(c_145, plain, (![A_54, B_55]: (v1_yellow_1(k2_funcop_1(A_54, B_55)) | ~l1_orders_2(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.30/1.29  tff(c_148, plain, (![A_49]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_113, c_145])).
% 2.30/1.29  tff(c_149, plain, (![A_49]: (~l1_orders_2(A_49))), inference(splitLeft, [status(thm)], [c_148])).
% 2.30/1.29  tff(c_50, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.30/1.29  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_50])).
% 2.30/1.29  tff(c_153, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_148])).
% 2.30/1.29  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.29  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.29  tff(c_167, plain, (![B_59, A_60]: (v4_relat_1(B_59, A_60) | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.29  tff(c_170, plain, (![A_60]: (v4_relat_1(k1_xboole_0, A_60) | ~r1_tarski(k1_xboole_0, A_60) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_167])).
% 2.30/1.29  tff(c_172, plain, (![A_60]: (v4_relat_1(k1_xboole_0, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4, c_170])).
% 2.30/1.29  tff(c_259, plain, (![A_92]: (k5_yellow_1(k1_xboole_0, A_92)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_92) | ~v1_partfun1(A_92, k1_xboole_0) | ~v1_funct_1(A_92) | ~v4_relat_1(A_92, k1_xboole_0) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.30/1.29  tff(c_262, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_172, c_259])).
% 2.30/1.29  tff(c_265, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_104, c_153, c_262])).
% 2.30/1.29  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_265])).
% 2.30/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  Inference rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Ref     : 0
% 2.30/1.29  #Sup     : 50
% 2.30/1.29  #Fact    : 0
% 2.30/1.29  #Define  : 0
% 2.30/1.29  #Split   : 1
% 2.30/1.29  #Chain   : 0
% 2.30/1.29  #Close   : 0
% 2.30/1.29  
% 2.30/1.29  Ordering : KBO
% 2.30/1.29  
% 2.30/1.29  Simplification rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Subsume      : 1
% 2.30/1.29  #Demod        : 13
% 2.30/1.29  #Tautology    : 40
% 2.30/1.29  #SimpNegUnit  : 3
% 2.30/1.29  #BackRed      : 4
% 2.30/1.29  
% 2.30/1.29  #Partial instantiations: 0
% 2.30/1.29  #Strategies tried      : 1
% 2.30/1.29  
% 2.30/1.29  Timing (in seconds)
% 2.30/1.29  ----------------------
% 2.30/1.29  Preprocessing        : 0.34
% 2.30/1.29  Parsing              : 0.19
% 2.30/1.29  CNF conversion       : 0.02
% 2.30/1.29  Main loop            : 0.19
% 2.30/1.29  Inferencing          : 0.07
% 2.30/1.29  Reduction            : 0.06
% 2.30/1.29  Demodulation         : 0.04
% 2.30/1.29  BG Simplification    : 0.01
% 2.30/1.29  Subsumption          : 0.02
% 2.30/1.29  Abstraction          : 0.01
% 2.30/1.29  MUC search           : 0.00
% 2.30/1.29  Cooper               : 0.00
% 2.30/1.29  Total                : 0.56
% 2.30/1.29  Index Insertion      : 0.00
% 2.30/1.29  Index Deletion       : 0.00
% 2.30/1.29  Index Matching       : 0.00
% 2.30/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
