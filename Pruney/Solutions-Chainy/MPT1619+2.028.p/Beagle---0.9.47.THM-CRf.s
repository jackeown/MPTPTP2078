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
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 106 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 ( 178 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > v2_relat_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

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

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_60,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v2_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_funcop_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_50,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_37] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_37] : k2_funcop_1(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_42,plain,(
    ! [A_40,B_41] : k7_funcop_1(A_40,B_41) = k2_funcop_1(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( k5_yellow_1(A_33,k7_funcop_1(A_33,B_34)) = k6_yellow_1(A_33,B_34)
      | ~ l1_orders_2(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_65,B_66] :
      ( k5_yellow_1(A_65,k2_funcop_1(A_65,B_66)) = k6_yellow_1(A_65,B_66)
      | ~ l1_orders_2(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_26])).

tff(c_147,plain,(
    ! [A_67] :
      ( k6_yellow_1(k1_xboole_0,A_67) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_135])).

tff(c_151,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_2') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_48,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_161,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_48])).

tff(c_40,plain,(
    ! [A_38] : v1_relat_1('#skF_1'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_38] : v1_funct_1('#skF_1'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_38] : v1_partfun1('#skF_1'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,(
    ! [A_56,B_57] :
      ( v1_yellow_1(k2_funcop_1(A_56,B_57))
      | ~ l1_orders_2(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    ! [A_37] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_100])).

tff(c_104,plain,(
    ! [A_37] : ~ l1_orders_2(A_37) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_50])).

tff(c_107,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_36,plain,(
    ! [A_38] : v4_relat_1('#skF_1'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_166,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_partfun1(A_72,k1_xboole_0)
      | ~ v1_funct_1(A_72)
      | ~ v4_relat_1(A_72,k1_xboole_0)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_170,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_177,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_32,c_170])).

tff(c_224,plain,(
    ! [A_91] :
      ( k5_yellow_1(k1_xboole_0,A_91) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_91)
      | ~ v1_partfun1(A_91,k1_xboole_0)
      | ~ v1_funct_1(A_91)
      | ~ v4_relat_1(A_91,k1_xboole_0)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_227,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,'#skF_1'(k1_xboole_0))
    | ~ v1_yellow_1('#skF_1'(k1_xboole_0))
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_224])).

tff(c_233,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_32,c_107,c_177,c_177,c_227])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > v2_relat_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 2.19/1.32  
% 2.19/1.32  %Foreground sorts:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Background operators:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Foreground operators:
% 2.19/1.32  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.19/1.32  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.19/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.32  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.19/1.32  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.19/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.32  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.19/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.32  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.19/1.32  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.19/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.19/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.32  
% 2.19/1.33  tff(f_100, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.19/1.33  tff(f_60, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.19/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.19/1.33  tff(f_73, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.19/1.33  tff(f_54, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.19/1.33  tff(f_71, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v2_relat_1(B)) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_funcop_1)).
% 2.19/1.33  tff(f_58, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.19/1.33  tff(f_83, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_pboole)).
% 2.19/1.33  tff(f_95, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.19/1.33  tff(c_50, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.19/1.33  tff(c_30, plain, (![A_37]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.33  tff(c_69, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.33  tff(c_73, plain, (![A_37]: (k2_funcop_1(k1_xboole_0, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_69])).
% 2.19/1.33  tff(c_42, plain, (![A_40, B_41]: (k7_funcop_1(A_40, B_41)=k2_funcop_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.19/1.33  tff(c_26, plain, (![A_33, B_34]: (k5_yellow_1(A_33, k7_funcop_1(A_33, B_34))=k6_yellow_1(A_33, B_34) | ~l1_orders_2(B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.33  tff(c_135, plain, (![A_65, B_66]: (k5_yellow_1(A_65, k2_funcop_1(A_65, B_66))=k6_yellow_1(A_65, B_66) | ~l1_orders_2(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_26])).
% 2.19/1.33  tff(c_147, plain, (![A_67]: (k6_yellow_1(k1_xboole_0, A_67)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_67))), inference(superposition, [status(thm), theory('equality')], [c_73, c_135])).
% 2.19/1.33  tff(c_151, plain, (k6_yellow_1(k1_xboole_0, '#skF_2')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_147])).
% 2.19/1.33  tff(c_48, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.19/1.33  tff(c_161, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_48])).
% 2.19/1.33  tff(c_40, plain, (![A_38]: (v1_relat_1('#skF_1'(A_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.33  tff(c_34, plain, (![A_38]: (v1_funct_1('#skF_1'(A_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.33  tff(c_32, plain, (![A_38]: (v1_partfun1('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.33  tff(c_100, plain, (![A_56, B_57]: (v1_yellow_1(k2_funcop_1(A_56, B_57)) | ~l1_orders_2(B_57))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.33  tff(c_103, plain, (![A_37]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_37))), inference(superposition, [status(thm), theory('equality')], [c_73, c_100])).
% 2.19/1.33  tff(c_104, plain, (![A_37]: (~l1_orders_2(A_37))), inference(splitLeft, [status(thm)], [c_103])).
% 2.19/1.33  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_50])).
% 2.19/1.33  tff(c_107, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_103])).
% 2.19/1.33  tff(c_36, plain, (![A_38]: (v4_relat_1('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.33  tff(c_166, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_partfun1(A_72, k1_xboole_0) | ~v1_funct_1(A_72) | ~v4_relat_1(A_72, k1_xboole_0) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.19/1.33  tff(c_170, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_166])).
% 2.19/1.33  tff(c_177, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_32, c_170])).
% 2.19/1.33  tff(c_224, plain, (![A_91]: (k5_yellow_1(k1_xboole_0, A_91)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_91) | ~v1_partfun1(A_91, k1_xboole_0) | ~v1_funct_1(A_91) | ~v4_relat_1(A_91, k1_xboole_0) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.19/1.33  tff(c_227, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, '#skF_1'(k1_xboole_0)) | ~v1_yellow_1('#skF_1'(k1_xboole_0)) | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_224])).
% 2.19/1.33  tff(c_233, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_32, c_107, c_177, c_177, c_227])).
% 2.19/1.33  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_233])).
% 2.19/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  Inference rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Ref     : 0
% 2.19/1.33  #Sup     : 42
% 2.19/1.33  #Fact    : 0
% 2.19/1.33  #Define  : 0
% 2.19/1.33  #Split   : 1
% 2.19/1.33  #Chain   : 0
% 2.19/1.33  #Close   : 0
% 2.19/1.33  
% 2.19/1.33  Ordering : KBO
% 2.19/1.33  
% 2.19/1.33  Simplification rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Subsume      : 1
% 2.19/1.33  #Demod        : 13
% 2.19/1.33  #Tautology    : 31
% 2.19/1.33  #SimpNegUnit  : 2
% 2.19/1.33  #BackRed      : 3
% 2.19/1.33  
% 2.19/1.33  #Partial instantiations: 0
% 2.19/1.33  #Strategies tried      : 1
% 2.19/1.33  
% 2.19/1.33  Timing (in seconds)
% 2.19/1.33  ----------------------
% 2.19/1.33  Preprocessing        : 0.36
% 2.19/1.34  Parsing              : 0.20
% 2.19/1.34  CNF conversion       : 0.02
% 2.19/1.34  Main loop            : 0.17
% 2.19/1.34  Inferencing          : 0.07
% 2.19/1.34  Reduction            : 0.05
% 2.19/1.34  Demodulation         : 0.04
% 2.19/1.34  BG Simplification    : 0.01
% 2.19/1.34  Subsumption          : 0.02
% 2.19/1.34  Abstraction          : 0.01
% 2.19/1.34  MUC search           : 0.00
% 2.19/1.34  Cooper               : 0.00
% 2.19/1.34  Total                : 0.56
% 2.19/1.34  Index Insertion      : 0.00
% 2.19/1.34  Index Deletion       : 0.00
% 2.19/1.34  Index Matching       : 0.00
% 2.19/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
