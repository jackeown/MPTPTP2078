%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 105 expanded)
%              Number of leaves         :   42 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 126 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_524,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k3_xboole_0(A_130,B_131)) = k4_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_545,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_524])).

tff(c_549,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_545])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_497,plain,(
    ! [A_127,B_128] : k3_xboole_0(k1_tarski(A_127),k2_tarski(A_127,B_128)) = k1_tarski(A_127) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_509,plain,(
    ! [A_129] : k3_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) = k1_tarski(A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_497])).

tff(c_89,plain,(
    ! [A_68,B_69] : k1_setfam_1(k2_tarski(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = k1_setfam_1(k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_515,plain,(
    ! [A_129] : k1_setfam_1(k1_tarski(k1_tarski(A_129))) = k1_tarski(A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_98])).

tff(c_569,plain,(
    ! [A_137] : k5_xboole_0(A_137,k1_setfam_1(k1_tarski(A_137))) = k4_xboole_0(A_137,A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_524])).

tff(c_578,plain,(
    ! [A_129] : k5_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) = k4_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_569])).

tff(c_584,plain,(
    ! [A_129] : k4_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_578])).

tff(c_30,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_586,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_30])).

tff(c_471,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k1_tarski(A_122),B_123)
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_480,plain,(
    ! [A_122] :
      ( k1_tarski(A_122) = k1_xboole_0
      | ~ r2_hidden(A_122,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_471,c_8])).

tff(c_594,plain,(
    ! [A_122] : ~ r2_hidden(A_122,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_480])).

tff(c_54,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_118,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_205,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_60])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_347,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden(k4_tarski(A_102,B_103),C_104)
      | ~ r2_hidden(B_103,k11_relat_1(C_104,A_102))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_53,A_38,D_56] :
      ( r2_hidden(C_53,k1_relat_1(A_38))
      | ~ r2_hidden(k4_tarski(C_53,D_56),A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_375,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(A_110,k1_relat_1(C_111))
      | ~ r2_hidden(B_112,k11_relat_1(C_111,A_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_347,c_38])).

tff(c_384,plain,(
    ! [A_113,C_114] :
      ( r2_hidden(A_113,k1_relat_1(C_114))
      | ~ v1_relat_1(C_114)
      | k11_relat_1(C_114,A_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_375])).

tff(c_395,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_384,c_118])).

tff(c_400,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_395])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_400])).

tff(c_404,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_403,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_686,plain,(
    ! [C_159,A_160] :
      ( r2_hidden(k4_tarski(C_159,'#skF_5'(A_160,k1_relat_1(A_160),C_159)),A_160)
      | ~ r2_hidden(C_159,k1_relat_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [B_58,C_59,A_57] :
      ( r2_hidden(B_58,k11_relat_1(C_59,A_57))
      | ~ r2_hidden(k4_tarski(A_57,B_58),C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1135,plain,(
    ! [A_193,C_194] :
      ( r2_hidden('#skF_5'(A_193,k1_relat_1(A_193),C_194),k11_relat_1(A_193,C_194))
      | ~ v1_relat_1(A_193)
      | ~ r2_hidden(C_194,k1_relat_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_686,c_50])).

tff(c_1155,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_1135])).

tff(c_1160,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_52,c_1155])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_1160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.44  
% 3.15/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.44  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.15/1.44  
% 3.15/1.44  %Foreground sorts:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Background operators:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Foreground operators:
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.44  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.15/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.15/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.15/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.44  
% 3.15/1.46  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.15/1.46  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.15/1.46  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.46  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.15/1.46  tff(f_61, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.15/1.46  tff(f_68, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.15/1.46  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.15/1.46  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.46  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.15/1.46  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.15/1.46  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.15/1.46  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.15/1.46  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.15/1.46  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.46  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.46  tff(c_524, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k3_xboole_0(A_130, B_131))=k4_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.46  tff(c_545, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_524])).
% 3.15/1.46  tff(c_549, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_545])).
% 3.15/1.46  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.46  tff(c_497, plain, (![A_127, B_128]: (k3_xboole_0(k1_tarski(A_127), k2_tarski(A_127, B_128))=k1_tarski(A_127))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.46  tff(c_509, plain, (![A_129]: (k3_xboole_0(k1_tarski(A_129), k1_tarski(A_129))=k1_tarski(A_129))), inference(superposition, [status(thm), theory('equality')], [c_12, c_497])).
% 3.15/1.46  tff(c_89, plain, (![A_68, B_69]: (k1_setfam_1(k2_tarski(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.46  tff(c_98, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=k1_setfam_1(k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 3.15/1.46  tff(c_515, plain, (![A_129]: (k1_setfam_1(k1_tarski(k1_tarski(A_129)))=k1_tarski(A_129))), inference(superposition, [status(thm), theory('equality')], [c_509, c_98])).
% 3.15/1.46  tff(c_569, plain, (![A_137]: (k5_xboole_0(A_137, k1_setfam_1(k1_tarski(A_137)))=k4_xboole_0(A_137, A_137))), inference(superposition, [status(thm), theory('equality')], [c_98, c_524])).
% 3.15/1.46  tff(c_578, plain, (![A_129]: (k5_xboole_0(k1_tarski(A_129), k1_tarski(A_129))=k4_xboole_0(k1_tarski(A_129), k1_tarski(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_515, c_569])).
% 3.15/1.46  tff(c_584, plain, (![A_129]: (k4_xboole_0(k1_tarski(A_129), k1_tarski(A_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_578])).
% 3.15/1.46  tff(c_30, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.46  tff(c_586, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_584, c_30])).
% 3.15/1.46  tff(c_471, plain, (![A_122, B_123]: (r1_tarski(k1_tarski(A_122), B_123) | ~r2_hidden(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.46  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.46  tff(c_480, plain, (![A_122]: (k1_tarski(A_122)=k1_xboole_0 | ~r2_hidden(A_122, k1_xboole_0))), inference(resolution, [status(thm)], [c_471, c_8])).
% 3.15/1.46  tff(c_594, plain, (![A_122]: (~r2_hidden(A_122, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_586, c_480])).
% 3.15/1.46  tff(c_54, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.46  tff(c_118, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.15/1.46  tff(c_60, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.46  tff(c_205, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_118, c_60])).
% 3.15/1.46  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.46  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.46  tff(c_347, plain, (![A_102, B_103, C_104]: (r2_hidden(k4_tarski(A_102, B_103), C_104) | ~r2_hidden(B_103, k11_relat_1(C_104, A_102)) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.46  tff(c_38, plain, (![C_53, A_38, D_56]: (r2_hidden(C_53, k1_relat_1(A_38)) | ~r2_hidden(k4_tarski(C_53, D_56), A_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.46  tff(c_375, plain, (![A_110, C_111, B_112]: (r2_hidden(A_110, k1_relat_1(C_111)) | ~r2_hidden(B_112, k11_relat_1(C_111, A_110)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_347, c_38])).
% 3.15/1.46  tff(c_384, plain, (![A_113, C_114]: (r2_hidden(A_113, k1_relat_1(C_114)) | ~v1_relat_1(C_114) | k11_relat_1(C_114, A_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_375])).
% 3.15/1.46  tff(c_395, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_384, c_118])).
% 3.15/1.46  tff(c_400, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_395])).
% 3.15/1.46  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_400])).
% 3.15/1.46  tff(c_404, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.15/1.46  tff(c_403, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.15/1.46  tff(c_686, plain, (![C_159, A_160]: (r2_hidden(k4_tarski(C_159, '#skF_5'(A_160, k1_relat_1(A_160), C_159)), A_160) | ~r2_hidden(C_159, k1_relat_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.46  tff(c_50, plain, (![B_58, C_59, A_57]: (r2_hidden(B_58, k11_relat_1(C_59, A_57)) | ~r2_hidden(k4_tarski(A_57, B_58), C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.46  tff(c_1135, plain, (![A_193, C_194]: (r2_hidden('#skF_5'(A_193, k1_relat_1(A_193), C_194), k11_relat_1(A_193, C_194)) | ~v1_relat_1(A_193) | ~r2_hidden(C_194, k1_relat_1(A_193)))), inference(resolution, [status(thm)], [c_686, c_50])).
% 3.15/1.46  tff(c_1155, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_1135])).
% 3.15/1.46  tff(c_1160, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_52, c_1155])).
% 3.15/1.46  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_1160])).
% 3.15/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  Inference rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Ref     : 0
% 3.15/1.46  #Sup     : 246
% 3.15/1.46  #Fact    : 0
% 3.15/1.46  #Define  : 0
% 3.15/1.46  #Split   : 3
% 3.15/1.46  #Chain   : 0
% 3.15/1.46  #Close   : 0
% 3.15/1.46  
% 3.15/1.46  Ordering : KBO
% 3.15/1.46  
% 3.15/1.46  Simplification rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Subsume      : 29
% 3.15/1.46  #Demod        : 90
% 3.15/1.46  #Tautology    : 130
% 3.15/1.46  #SimpNegUnit  : 30
% 3.15/1.46  #BackRed      : 5
% 3.15/1.46  
% 3.15/1.46  #Partial instantiations: 0
% 3.15/1.46  #Strategies tried      : 1
% 3.15/1.46  
% 3.15/1.46  Timing (in seconds)
% 3.15/1.46  ----------------------
% 3.15/1.46  Preprocessing        : 0.32
% 3.15/1.46  Parsing              : 0.16
% 3.15/1.46  CNF conversion       : 0.02
% 3.15/1.46  Main loop            : 0.38
% 3.15/1.46  Inferencing          : 0.14
% 3.15/1.46  Reduction            : 0.11
% 3.15/1.46  Demodulation         : 0.08
% 3.15/1.46  BG Simplification    : 0.02
% 3.15/1.46  Subsumption          : 0.06
% 3.15/1.46  Abstraction          : 0.02
% 3.15/1.46  MUC search           : 0.00
% 3.15/1.46  Cooper               : 0.00
% 3.15/1.46  Total                : 0.73
% 3.15/1.46  Index Insertion      : 0.00
% 3.15/1.46  Index Deletion       : 0.00
% 3.15/1.46  Index Matching       : 0.00
% 3.15/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
