%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:41 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 169 expanded)
%              Number of leaves         :   48 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 309 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_yellow_1,type,(
    k6_yellow_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_84,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_78,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_95,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_60,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_36] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_128,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_2'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_137,plain,(
    ! [A_36] : k2_funcop_1(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_54,plain,(
    ! [A_39,B_40] : k7_funcop_1(A_39,B_40) = k2_funcop_1(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( k5_yellow_1(A_34,k7_funcop_1(A_34,B_35)) = k6_yellow_1(A_34,B_35)
      | ~ l1_orders_2(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_213,plain,(
    ! [A_73,B_74] :
      ( k5_yellow_1(A_73,k2_funcop_1(A_73,B_74)) = k6_yellow_1(A_73,B_74)
      | ~ l1_orders_2(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40])).

tff(c_225,plain,(
    ! [A_75] :
      ( k6_yellow_1(k1_xboole_0,A_75) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_213])).

tff(c_229,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_4') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_58,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_230,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_58])).

tff(c_74,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_38,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    ! [A_29] : v1_relat_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_63])).

tff(c_28,plain,(
    ! [A_29] : v1_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_29] : v1_funct_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_93,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_62])).

tff(c_52,plain,(
    ! [A_37] : v1_relat_1('#skF_3'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_37] : v1_partfun1('#skF_3'(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_37] : v4_relat_1('#skF_3'(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_245,plain,(
    ! [B_81,A_82] :
      ( k1_relat_1(B_81) = A_82
      | ~ v1_partfun1(B_81,A_82)
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_3'(A_37)) = A_37
      | ~ v1_partfun1('#skF_3'(A_37),A_37)
      | ~ v1_relat_1('#skF_3'(A_37)) ) ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_251,plain,(
    ! [A_37] : k1_relat_1('#skF_3'(A_37)) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_248])).

tff(c_178,plain,(
    ! [A_65] :
      ( k1_relat_1(A_65) != k1_xboole_0
      | k1_xboole_0 = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_191,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_3'(A_37)) != k1_xboole_0
      | '#skF_3'(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_178])).

tff(c_268,plain,(
    ! [A_84] :
      ( k1_xboole_0 != A_84
      | '#skF_3'(A_84) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_191])).

tff(c_344,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_46])).

tff(c_44,plain,(
    ! [A_37] : v1_yellow_1('#skF_3'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_287,plain,(
    ! [A_84] :
      ( v1_yellow_1(k1_xboole_0)
      | k1_xboole_0 != A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_44])).

tff(c_306,plain,(
    ! [A_84] : k1_xboole_0 != A_84 ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_137])).

tff(c_319,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_283,plain,(
    ! [A_84] :
      ( v4_relat_1(k1_xboole_0,A_84)
      | k1_xboole_0 != A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_50])).

tff(c_356,plain,(
    ! [A_99] :
      ( k5_yellow_1(k1_xboole_0,A_99) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_99)
      | ~ v1_partfun1(A_99,k1_xboole_0)
      | ~ v1_funct_1(A_99)
      | ~ v4_relat_1(A_99,k1_xboole_0)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_359,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_283,c_356])).

tff(c_365,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_93,c_344,c_319,c_359])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:09:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.32  
% 2.61/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.32  %$ v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.61/1.32  
% 2.61/1.32  %Foreground sorts:
% 2.61/1.32  
% 2.61/1.32  
% 2.61/1.32  %Background operators:
% 2.61/1.32  
% 2.61/1.32  
% 2.61/1.32  %Foreground operators:
% 2.61/1.32  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.61/1.32  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.61/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.32  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.61/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.61/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.32  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.61/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.32  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.61/1.32  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.61/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.61/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.61/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.61/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.32  
% 2.61/1.34  tff(f_114, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.61/1.34  tff(f_84, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.61/1.34  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.61/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.61/1.34  tff(f_97, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.61/1.34  tff(f_82, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.61/1.34  tff(f_78, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.61/1.34  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.61/1.34  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.61/1.34  tff(f_95, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_yellow_1)).
% 2.61/1.34  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.61/1.34  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.61/1.34  tff(f_109, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.61/1.34  tff(c_60, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.61/1.34  tff(c_42, plain, (![A_36]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_36)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.61/1.34  tff(c_128, plain, (![A_58]: (r2_hidden('#skF_2'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.34  tff(c_133, plain, (![A_59]: (~v1_xboole_0(A_59) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_128, c_2])).
% 2.61/1.34  tff(c_137, plain, (![A_36]: (k2_funcop_1(k1_xboole_0, A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_133])).
% 2.61/1.34  tff(c_54, plain, (![A_39, B_40]: (k7_funcop_1(A_39, B_40)=k2_funcop_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.34  tff(c_40, plain, (![A_34, B_35]: (k5_yellow_1(A_34, k7_funcop_1(A_34, B_35))=k6_yellow_1(A_34, B_35) | ~l1_orders_2(B_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.34  tff(c_213, plain, (![A_73, B_74]: (k5_yellow_1(A_73, k2_funcop_1(A_73, B_74))=k6_yellow_1(A_73, B_74) | ~l1_orders_2(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40])).
% 2.61/1.34  tff(c_225, plain, (![A_75]: (k6_yellow_1(k1_xboole_0, A_75)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_75))), inference(superposition, [status(thm), theory('equality')], [c_137, c_213])).
% 2.61/1.34  tff(c_229, plain, (k6_yellow_1(k1_xboole_0, '#skF_4')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_225])).
% 2.61/1.34  tff(c_58, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.61/1.34  tff(c_230, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_58])).
% 2.61/1.34  tff(c_74, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.34  tff(c_80, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_24])).
% 2.61/1.34  tff(c_38, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_26, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.34  tff(c_63, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26])).
% 2.61/1.34  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_63])).
% 2.61/1.34  tff(c_28, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.34  tff(c_62, plain, (![A_29]: (v1_funct_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 2.61/1.34  tff(c_93, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_62])).
% 2.61/1.34  tff(c_52, plain, (![A_37]: (v1_relat_1('#skF_3'(A_37)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.61/1.34  tff(c_46, plain, (![A_37]: (v1_partfun1('#skF_3'(A_37), A_37))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.61/1.34  tff(c_50, plain, (![A_37]: (v4_relat_1('#skF_3'(A_37), A_37))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.61/1.34  tff(c_245, plain, (![B_81, A_82]: (k1_relat_1(B_81)=A_82 | ~v1_partfun1(B_81, A_82) | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.34  tff(c_248, plain, (![A_37]: (k1_relat_1('#skF_3'(A_37))=A_37 | ~v1_partfun1('#skF_3'(A_37), A_37) | ~v1_relat_1('#skF_3'(A_37)))), inference(resolution, [status(thm)], [c_50, c_245])).
% 2.61/1.34  tff(c_251, plain, (![A_37]: (k1_relat_1('#skF_3'(A_37))=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_248])).
% 2.61/1.34  tff(c_178, plain, (![A_65]: (k1_relat_1(A_65)!=k1_xboole_0 | k1_xboole_0=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.34  tff(c_191, plain, (![A_37]: (k1_relat_1('#skF_3'(A_37))!=k1_xboole_0 | '#skF_3'(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_178])).
% 2.61/1.34  tff(c_268, plain, (![A_84]: (k1_xboole_0!=A_84 | '#skF_3'(A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_191])).
% 2.61/1.34  tff(c_344, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_268, c_46])).
% 2.61/1.34  tff(c_44, plain, (![A_37]: (v1_yellow_1('#skF_3'(A_37)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.61/1.34  tff(c_287, plain, (![A_84]: (v1_yellow_1(k1_xboole_0) | k1_xboole_0!=A_84)), inference(superposition, [status(thm), theory('equality')], [c_268, c_44])).
% 2.61/1.34  tff(c_306, plain, (![A_84]: (k1_xboole_0!=A_84)), inference(splitLeft, [status(thm)], [c_287])).
% 2.61/1.34  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_137])).
% 2.61/1.34  tff(c_319, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_287])).
% 2.61/1.34  tff(c_283, plain, (![A_84]: (v4_relat_1(k1_xboole_0, A_84) | k1_xboole_0!=A_84)), inference(superposition, [status(thm), theory('equality')], [c_268, c_50])).
% 2.61/1.34  tff(c_356, plain, (![A_99]: (k5_yellow_1(k1_xboole_0, A_99)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_99) | ~v1_partfun1(A_99, k1_xboole_0) | ~v1_funct_1(A_99) | ~v4_relat_1(A_99, k1_xboole_0) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.34  tff(c_359, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_283, c_356])).
% 2.61/1.34  tff(c_365, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_93, c_344, c_319, c_359])).
% 2.61/1.34  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_365])).
% 2.61/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  Inference rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Ref     : 1
% 2.61/1.34  #Sup     : 63
% 2.61/1.34  #Fact    : 0
% 2.61/1.34  #Define  : 0
% 2.61/1.34  #Split   : 1
% 2.61/1.34  #Chain   : 0
% 2.61/1.34  #Close   : 0
% 2.61/1.34  
% 2.61/1.34  Ordering : KBO
% 2.61/1.34  
% 2.61/1.34  Simplification rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Subsume      : 7
% 2.61/1.34  #Demod        : 29
% 2.61/1.34  #Tautology    : 44
% 2.61/1.34  #SimpNegUnit  : 12
% 2.61/1.34  #BackRed      : 8
% 2.61/1.34  
% 2.61/1.34  #Partial instantiations: 0
% 2.61/1.34  #Strategies tried      : 1
% 2.61/1.34  
% 2.61/1.34  Timing (in seconds)
% 2.61/1.34  ----------------------
% 2.61/1.34  Preprocessing        : 0.35
% 2.61/1.34  Parsing              : 0.18
% 2.61/1.34  CNF conversion       : 0.02
% 2.61/1.34  Main loop            : 0.23
% 2.61/1.34  Inferencing          : 0.09
% 2.61/1.34  Reduction            : 0.08
% 2.61/1.34  Demodulation         : 0.05
% 2.61/1.34  BG Simplification    : 0.02
% 2.61/1.34  Subsumption          : 0.03
% 2.61/1.34  Abstraction          : 0.01
% 2.61/1.34  MUC search           : 0.00
% 2.61/1.34  Cooper               : 0.00
% 2.61/1.34  Total                : 0.62
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
