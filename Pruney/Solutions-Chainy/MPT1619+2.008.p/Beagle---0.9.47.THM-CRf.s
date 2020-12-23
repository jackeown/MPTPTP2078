%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:40 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   44 (  58 expanded)
%              Depth                    :    6
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_71,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_65,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_38] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_100,plain,(
    ! [A_38] : k2_funcop_1(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_42,plain,(
    ! [A_39,B_40] : k7_funcop_1(A_39,B_40) = k2_funcop_1(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( k5_yellow_1(A_34,k7_funcop_1(A_34,B_35)) = k6_yellow_1(A_34,B_35)
      | ~ l1_orders_2(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    ! [A_62,B_63] :
      ( k5_yellow_1(A_62,k2_funcop_1(A_62,B_63)) = k6_yellow_1(A_62,B_63)
      | ~ l1_orders_2(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_182,plain,(
    ! [A_64] :
      ( k6_yellow_1(k1_xboole_0,A_64) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_170])).

tff(c_186,plain,(
    k6_yellow_1(k1_xboole_0,'#skF_1') = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_46,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_187,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_46])).

tff(c_59,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_34,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_31] : v1_relat_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_103,plain,(
    ! [A_49] :
      ( v1_funct_1(A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_81,plain,(
    ! [A_45] : v1_partfun1(k6_partfun1(A_45),A_45) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_81])).

tff(c_131,plain,(
    ! [A_52,B_53] :
      ( v1_yellow_1(k2_funcop_1(A_52,B_53))
      | ~ l1_orders_2(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    ! [A_38] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_131])).

tff(c_135,plain,(
    ! [A_38] : ~ l1_orders_2(A_38) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_48])).

tff(c_138,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_26,plain,(
    ! [A_31] : v4_relat_1(k6_relat_1(A_31),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_46] : v4_relat_1(k6_partfun1(A_46),A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26])).

tff(c_88,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_85])).

tff(c_228,plain,(
    ! [A_87] :
      ( k5_yellow_1(k1_xboole_0,A_87) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_87)
      | ~ v1_partfun1(A_87,k1_xboole_0)
      | ~ v1_funct_1(A_87)
      | ~ v4_relat_1(A_87,k1_xboole_0)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_230,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_88,c_228])).

tff(c_236,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_111,c_84,c_138,c_230])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:38:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.23  
% 2.23/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.23  %$ v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_zfmisc_1 > k2_tarski > k2_funcop_1 > g1_orders_2 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.23/1.23  
% 2.23/1.23  %Foreground sorts:
% 2.23/1.23  
% 2.23/1.23  
% 2.23/1.23  %Background operators:
% 2.23/1.23  
% 2.23/1.23  
% 2.23/1.23  %Foreground operators:
% 2.23/1.23  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 2.23/1.23  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 2.23/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.23  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 2.23/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.23  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 2.23/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.23  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.23/1.23  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 2.23/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.23/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.23/1.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.23  
% 2.23/1.25  tff(f_90, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 2.23/1.25  tff(f_71, axiom, (![A]: v1_xboole_0(k2_funcop_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 2.23/1.25  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.25  tff(f_73, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 2.23/1.25  tff(f_65, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 2.23/1.25  tff(f_61, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.23/1.25  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.23/1.25  tff(f_55, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.23/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.25  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.23/1.25  tff(f_59, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.23/1.25  tff(f_69, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_yellow_1)).
% 2.23/1.25  tff(f_85, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 2.23/1.25  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.25  tff(c_40, plain, (![A_38]: (v1_xboole_0(k2_funcop_1(k1_xboole_0, A_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.25  tff(c_93, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.25  tff(c_100, plain, (![A_38]: (k2_funcop_1(k1_xboole_0, A_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_93])).
% 2.23/1.25  tff(c_42, plain, (![A_39, B_40]: (k7_funcop_1(A_39, B_40)=k2_funcop_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.25  tff(c_36, plain, (![A_34, B_35]: (k5_yellow_1(A_34, k7_funcop_1(A_34, B_35))=k6_yellow_1(A_34, B_35) | ~l1_orders_2(B_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.25  tff(c_170, plain, (![A_62, B_63]: (k5_yellow_1(A_62, k2_funcop_1(A_62, B_63))=k6_yellow_1(A_62, B_63) | ~l1_orders_2(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 2.23/1.25  tff(c_182, plain, (![A_64]: (k6_yellow_1(k1_xboole_0, A_64)=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~l1_orders_2(A_64))), inference(superposition, [status(thm), theory('equality')], [c_100, c_170])).
% 2.23/1.25  tff(c_186, plain, (k6_yellow_1(k1_xboole_0, '#skF_1')=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_182])).
% 2.23/1.25  tff(c_46, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.25  tff(c_187, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_46])).
% 2.23/1.25  tff(c_59, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.25  tff(c_65, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59, c_20])).
% 2.23/1.25  tff(c_34, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_24, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.25  tff(c_52, plain, (![A_31]: (v1_relat_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 2.23/1.25  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_52])).
% 2.23/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.25  tff(c_103, plain, (![A_49]: (v1_funct_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.25  tff(c_111, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_103])).
% 2.23/1.25  tff(c_81, plain, (![A_45]: (v1_partfun1(k6_partfun1(A_45), A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.25  tff(c_84, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_81])).
% 2.23/1.25  tff(c_131, plain, (![A_52, B_53]: (v1_yellow_1(k2_funcop_1(A_52, B_53)) | ~l1_orders_2(B_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.25  tff(c_134, plain, (![A_38]: (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(A_38))), inference(superposition, [status(thm), theory('equality')], [c_100, c_131])).
% 2.23/1.25  tff(c_135, plain, (![A_38]: (~l1_orders_2(A_38))), inference(splitLeft, [status(thm)], [c_134])).
% 2.23/1.25  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_48])).
% 2.23/1.25  tff(c_138, plain, (v1_yellow_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_134])).
% 2.23/1.25  tff(c_26, plain, (![A_31]: (v4_relat_1(k6_relat_1(A_31), A_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.25  tff(c_85, plain, (![A_46]: (v4_relat_1(k6_partfun1(A_46), A_46))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26])).
% 2.23/1.25  tff(c_88, plain, (v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_85])).
% 2.23/1.25  tff(c_228, plain, (![A_87]: (k5_yellow_1(k1_xboole_0, A_87)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_87) | ~v1_partfun1(A_87, k1_xboole_0) | ~v1_funct_1(A_87) | ~v4_relat_1(A_87, k1_xboole_0) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.25  tff(c_230, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_228])).
% 2.23/1.25  tff(c_236, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))=k5_yellow_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_111, c_84, c_138, c_230])).
% 2.23/1.25  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_236])).
% 2.23/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  Inference rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Ref     : 0
% 2.23/1.25  #Sup     : 44
% 2.23/1.25  #Fact    : 0
% 2.23/1.25  #Define  : 0
% 2.23/1.25  #Split   : 1
% 2.23/1.25  #Chain   : 0
% 2.23/1.25  #Close   : 0
% 2.23/1.25  
% 2.23/1.25  Ordering : KBO
% 2.23/1.25  
% 2.23/1.25  Simplification rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Subsume      : 1
% 2.23/1.25  #Demod        : 14
% 2.23/1.25  #Tautology    : 32
% 2.23/1.25  #SimpNegUnit  : 2
% 2.23/1.25  #BackRed      : 3
% 2.23/1.25  
% 2.23/1.25  #Partial instantiations: 0
% 2.23/1.25  #Strategies tried      : 1
% 2.23/1.25  
% 2.23/1.25  Timing (in seconds)
% 2.23/1.25  ----------------------
% 2.23/1.25  Preprocessing        : 0.31
% 2.23/1.25  Parsing              : 0.17
% 2.23/1.25  CNF conversion       : 0.02
% 2.23/1.25  Main loop            : 0.17
% 2.23/1.25  Inferencing          : 0.06
% 2.23/1.25  Reduction            : 0.05
% 2.23/1.25  Demodulation         : 0.04
% 2.23/1.25  BG Simplification    : 0.01
% 2.23/1.25  Subsumption          : 0.02
% 2.23/1.25  Abstraction          : 0.01
% 2.23/1.25  MUC search           : 0.00
% 2.23/1.25  Cooper               : 0.00
% 2.23/1.25  Total                : 0.51
% 2.23/1.25  Index Insertion      : 0.00
% 2.23/1.25  Index Deletion       : 0.00
% 2.23/1.25  Index Matching       : 0.00
% 2.23/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
