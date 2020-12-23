%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:40 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 123 expanded)
%              Number of leaves         :   53 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 156 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > k1_funct_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_101,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_91,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_85,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_68,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    ! [A_49] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_130,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_137,plain,(
    ! [A_49] : k2_funcop_1(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_130])).

tff(c_62,plain,(
    ! [A_50,B_51] : k7_funcop_1(A_50,B_51) = k2_funcop_1(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [A_45,B_46] :
      ( k5_yellow_1(A_45,k7_funcop_1(A_45,B_46)) = k6_yellow_1(A_45,B_46)
      | ~ l1_orders_2(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_436,plain,(
    ! [A_111,B_112] :
      ( k5_yellow_1(A_111,k2_funcop_1(A_111,B_112)) = k6_yellow_1(A_111,B_112)
      | ~ l1_orders_2(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56])).

tff(c_453,plain,(
    ! [A_115] :
      ( k6_yellow_1(k1_xboole_0,A_115) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_436])).

tff(c_457,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_453])).

tff(c_66,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_458,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [A_58] :
      ( v1_relat_1(A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_87,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_36])).

tff(c_54,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [A_36] : v1_funct_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ! [A_36] : v1_funct_1(k6_partfun1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40])).

tff(c_104,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_70])).

tff(c_126,plain,(
    ! [A_62] : v1_partfun1(k6_partfun1(A_62),A_62) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_129,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_126])).

tff(c_161,plain,(
    ! [A_67,B_68] :
      ( v1_yellow_1(k2_funcop_1(A_67,B_68))
      | ~ l1_orders_2(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_164,plain,(
    ! [A_49] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_161])).

tff(c_165,plain,(
    ! [A_49] : ~ l1_orders_2(A_49) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_68])).

tff(c_177,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_44,plain,(
    ! [A_37] : k1_relat_1('#skF_1'(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ! [A_37] : v1_relat_1('#skF_1'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214,plain,(
    ! [A_77] :
      ( k1_relat_1(A_77) != k1_xboole_0
      | k1_xboole_0 = A_77
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_1'(A_37)) != k1_xboole_0
      | '#skF_1'(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_214])).

tff(c_228,plain,(
    ! [A_37] :
      ( k1_xboole_0 != A_37
      | '#skF_1'(A_37) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_223])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_288,plain,(
    ! [B_87,A_88] :
      ( v4_relat_1(B_87,A_88)
      | ~ r1_tarski(k1_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_299,plain,(
    ! [B_89] :
      ( v4_relat_1(B_89,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_10,c_288])).

tff(c_302,plain,(
    ! [A_37] :
      ( v4_relat_1('#skF_1'(A_37),A_37)
      | ~ v1_relat_1('#skF_1'(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_299])).

tff(c_305,plain,(
    ! [A_90] : v4_relat_1('#skF_1'(A_90),A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_302])).

tff(c_308,plain,(
    ! [A_37] :
      ( v4_relat_1(k1_xboole_0,A_37)
      | k1_xboole_0 != A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_305])).

tff(c_766,plain,(
    ! [A_160] :
      ( k5_yellow_1(k1_xboole_0,A_160) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_160)
      | ~ v1_partfun1(A_160,k1_xboole_0)
      | ~ v1_funct_1(A_160)
      | ~ v4_relat_1(A_160,k1_xboole_0)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_777,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_308,c_766])).

tff(c_788,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_104,c_129,c_177,c_777])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:04:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.50  
% 3.11/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.50  %$ v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > k1_funct_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.11/1.50  
% 3.11/1.50  %Foreground sorts:
% 3.11/1.50  
% 3.11/1.50  
% 3.11/1.50  %Background operators:
% 3.11/1.50  
% 3.11/1.50  
% 3.11/1.50  %Foreground operators:
% 3.11/1.50  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 3.11/1.50  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 3.11/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.50  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 3.11/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.11/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.50  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 3.11/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.50  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 3.11/1.50  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 3.11/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.11/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.11/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.11/1.50  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.11/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.11/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.11/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.50  
% 3.23/1.52  tff(f_120, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 3.23/1.52  tff(f_101, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 3.23/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.52  tff(f_103, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 3.23/1.52  tff(f_95, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 3.23/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.23/1.52  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.23/1.52  tff(f_91, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.23/1.52  tff(f_69, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.23/1.52  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.23/1.52  tff(f_89, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.23/1.52  tff(f_99, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 3.23/1.52  tff(f_85, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_tarski(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 3.23/1.52  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.23/1.52  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.52  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.23/1.52  tff(f_115, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 3.23/1.52  tff(c_68, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_60, plain, (![A_49]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_49)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.52  tff(c_130, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.23/1.52  tff(c_137, plain, (![A_49]: (k2_funcop_1(k1_xboole_0, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_130])).
% 3.23/1.52  tff(c_62, plain, (![A_50, B_51]: (k7_funcop_1(A_50, B_51)=k2_funcop_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.23/1.52  tff(c_56, plain, (![A_45, B_46]: (k5_yellow_1(A_45, k7_funcop_1(A_45, B_46))=k6_yellow_1(A_45, B_46) | ~l1_orders_2(B_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.23/1.52  tff(c_436, plain, (![A_111, B_112]: (k5_yellow_1(A_111, k2_funcop_1(A_111, B_112))=k6_yellow_1(A_111, B_112) | ~l1_orders_2(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56])).
% 3.23/1.52  tff(c_453, plain, (![A_115]: (k6_yellow_1(k1_xboole_0, A_115)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_115))), inference(superposition, [status(thm), theory('equality')], [c_137, c_436])).
% 3.23/1.52  tff(c_457, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_453])).
% 3.23/1.52  tff(c_66, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.52  tff(c_458, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_457, c_66])).
% 3.23/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.23/1.52  tff(c_82, plain, (![A_58]: (v1_relat_1(A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.52  tff(c_86, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 3.23/1.52  tff(c_87, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.23/1.52  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.52  tff(c_93, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_87, c_36])).
% 3.23/1.52  tff(c_54, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.23/1.52  tff(c_40, plain, (![A_36]: (v1_funct_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.52  tff(c_70, plain, (![A_36]: (v1_funct_1(k6_partfun1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40])).
% 3.23/1.52  tff(c_104, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_70])).
% 3.23/1.52  tff(c_126, plain, (![A_62]: (v1_partfun1(k6_partfun1(A_62), A_62))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.23/1.52  tff(c_129, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_126])).
% 3.23/1.52  tff(c_161, plain, (![A_67, B_68]: (v1_yellow_1(k2_funcop_1(A_67, B_68)) | ~l1_orders_2(B_68))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.23/1.52  tff(c_164, plain, (![A_49]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_137, c_161])).
% 3.23/1.52  tff(c_165, plain, (![A_49]: (~l1_orders_2(A_49))), inference(splitLeft, [status(thm)], [c_164])).
% 3.23/1.52  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_68])).
% 3.23/1.52  tff(c_177, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_164])).
% 3.23/1.52  tff(c_44, plain, (![A_37]: (k1_relat_1('#skF_1'(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.52  tff(c_48, plain, (![A_37]: (v1_relat_1('#skF_1'(A_37)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.23/1.52  tff(c_214, plain, (![A_77]: (k1_relat_1(A_77)!=k1_xboole_0 | k1_xboole_0=A_77 | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/1.52  tff(c_223, plain, (![A_37]: (k1_relat_1('#skF_1'(A_37))!=k1_xboole_0 | '#skF_1'(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_214])).
% 3.23/1.52  tff(c_228, plain, (![A_37]: (k1_xboole_0!=A_37 | '#skF_1'(A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_223])).
% 3.23/1.52  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.52  tff(c_288, plain, (![B_87, A_88]: (v4_relat_1(B_87, A_88) | ~r1_tarski(k1_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.52  tff(c_299, plain, (![B_89]: (v4_relat_1(B_89, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_10, c_288])).
% 3.23/1.52  tff(c_302, plain, (![A_37]: (v4_relat_1('#skF_1'(A_37), A_37) | ~v1_relat_1('#skF_1'(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_299])).
% 3.23/1.52  tff(c_305, plain, (![A_90]: (v4_relat_1('#skF_1'(A_90), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_302])).
% 3.23/1.52  tff(c_308, plain, (![A_37]: (v4_relat_1(k1_xboole_0, A_37) | k1_xboole_0!=A_37)), inference(superposition, [status(thm), theory('equality')], [c_228, c_305])).
% 3.23/1.52  tff(c_766, plain, (![A_160]: (k5_yellow_1(k1_xboole_0, A_160)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_160) | ~v1_partfun1(A_160, k1_xboole_0) | ~v1_funct_1(A_160) | ~v4_relat_1(A_160, k1_xboole_0) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.23/1.52  tff(c_777, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_308, c_766])).
% 3.23/1.52  tff(c_788, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_104, c_129, c_177, c_777])).
% 3.23/1.52  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_788])).
% 3.23/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  Inference rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Ref     : 2
% 3.23/1.52  #Sup     : 146
% 3.23/1.52  #Fact    : 0
% 3.23/1.52  #Define  : 0
% 3.23/1.52  #Split   : 1
% 3.23/1.52  #Chain   : 0
% 3.23/1.52  #Close   : 0
% 3.23/1.52  
% 3.23/1.52  Ordering : KBO
% 3.23/1.52  
% 3.23/1.52  Simplification rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Subsume      : 33
% 3.23/1.52  #Demod        : 102
% 3.23/1.52  #Tautology    : 77
% 3.23/1.52  #SimpNegUnit  : 2
% 3.23/1.52  #BackRed      : 4
% 3.23/1.52  
% 3.23/1.52  #Partial instantiations: 0
% 3.23/1.52  #Strategies tried      : 1
% 3.23/1.52  
% 3.23/1.52  Timing (in seconds)
% 3.23/1.52  ----------------------
% 3.23/1.52  Preprocessing        : 0.37
% 3.23/1.52  Parsing              : 0.20
% 3.23/1.52  CNF conversion       : 0.02
% 3.23/1.52  Main loop            : 0.33
% 3.23/1.52  Inferencing          : 0.12
% 3.23/1.52  Reduction            : 0.11
% 3.23/1.52  Demodulation         : 0.08
% 3.23/1.52  BG Simplification    : 0.02
% 3.23/1.52  Subsumption          : 0.05
% 3.23/1.52  Abstraction          : 0.02
% 3.23/1.52  MUC search           : 0.00
% 3.23/1.52  Cooper               : 0.00
% 3.23/1.52  Total                : 0.74
% 3.23/1.52  Index Insertion      : 0.00
% 3.23/1.52  Index Deletion       : 0.00
% 3.23/1.52  Index Matching       : 0.00
% 3.23/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
