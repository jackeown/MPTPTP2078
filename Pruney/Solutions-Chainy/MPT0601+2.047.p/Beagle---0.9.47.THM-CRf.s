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
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (  84 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 105 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_301,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,B_118)) = k4_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_313,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_310])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_323,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_30])).

tff(c_88,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tarski(A_70),B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_70] :
      ( k1_tarski(A_70) = k1_xboole_0
      | ~ r2_hidden(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_88,c_8])).

tff(c_331,plain,(
    ! [A_70] : ~ r2_hidden(A_70,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_93])).

tff(c_54,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_139,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_60])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_212,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden(k4_tarski(A_101,B_102),C_103)
      | ~ r2_hidden(B_102,k11_relat_1(C_103,A_101))
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_58,D_61),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_227,plain,(
    ! [A_104,C_105,B_106] :
      ( r2_hidden(A_104,k1_relat_1(C_105))
      | ~ r2_hidden(B_106,k11_relat_1(C_105,A_104))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_212,c_38])).

tff(c_237,plain,(
    ! [A_109,C_110] :
      ( r2_hidden(A_109,k1_relat_1(C_110))
      | ~ v1_relat_1(C_110)
      | k11_relat_1(C_110,A_109) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_252,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_237,c_106])).

tff(c_258,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_252])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_258])).

tff(c_262,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_261,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_427,plain,(
    ! [C_152,A_153] :
      ( r2_hidden(k4_tarski(C_152,'#skF_5'(A_153,k1_relat_1(A_153),C_152)),A_153)
      | ~ r2_hidden(C_152,k1_relat_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [B_63,C_64,A_62] :
      ( r2_hidden(B_63,k11_relat_1(C_64,A_62))
      | ~ r2_hidden(k4_tarski(A_62,B_63),C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1003,plain,(
    ! [A_197,C_198] :
      ( r2_hidden('#skF_5'(A_197,k1_relat_1(A_197),C_198),k11_relat_1(A_197,C_198))
      | ~ v1_relat_1(A_197)
      | ~ r2_hidden(C_198,k1_relat_1(A_197)) ) ),
    inference(resolution,[status(thm)],[c_427,c_50])).

tff(c_1023,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_1003])).

tff(c_1028,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_52,c_1023])).

tff(c_1030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_1028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.19/1.49  
% 3.19/1.49  %Foreground sorts:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Background operators:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Foreground operators:
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.19/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.19/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.19/1.49  
% 3.19/1.50  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.19/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.19/1.50  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.50  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.19/1.50  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.19/1.50  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.19/1.50  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.19/1.50  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.19/1.50  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.19/1.50  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.19/1.50  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.50  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.50  tff(c_301, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, B_118))=k4_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.50  tff(c_310, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_301])).
% 3.19/1.50  tff(c_313, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_310])).
% 3.19/1.50  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.50  tff(c_323, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_30])).
% 3.19/1.50  tff(c_88, plain, (![A_70, B_71]: (r1_tarski(k1_tarski(A_70), B_71) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.50  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.50  tff(c_93, plain, (![A_70]: (k1_tarski(A_70)=k1_xboole_0 | ~r2_hidden(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_88, c_8])).
% 3.19/1.50  tff(c_331, plain, (![A_70]: (~r2_hidden(A_70, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_323, c_93])).
% 3.19/1.50  tff(c_54, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.50  tff(c_106, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.19/1.50  tff(c_60, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.50  tff(c_139, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_106, c_60])).
% 3.19/1.50  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.50  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.50  tff(c_212, plain, (![A_101, B_102, C_103]: (r2_hidden(k4_tarski(A_101, B_102), C_103) | ~r2_hidden(B_102, k11_relat_1(C_103, A_101)) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.50  tff(c_38, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k1_relat_1(A_43)) | ~r2_hidden(k4_tarski(C_58, D_61), A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.19/1.50  tff(c_227, plain, (![A_104, C_105, B_106]: (r2_hidden(A_104, k1_relat_1(C_105)) | ~r2_hidden(B_106, k11_relat_1(C_105, A_104)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_212, c_38])).
% 3.19/1.50  tff(c_237, plain, (![A_109, C_110]: (r2_hidden(A_109, k1_relat_1(C_110)) | ~v1_relat_1(C_110) | k11_relat_1(C_110, A_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_227])).
% 3.19/1.50  tff(c_252, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_237, c_106])).
% 3.19/1.50  tff(c_258, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_252])).
% 3.19/1.50  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_258])).
% 3.19/1.50  tff(c_262, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.19/1.50  tff(c_261, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.19/1.50  tff(c_427, plain, (![C_152, A_153]: (r2_hidden(k4_tarski(C_152, '#skF_5'(A_153, k1_relat_1(A_153), C_152)), A_153) | ~r2_hidden(C_152, k1_relat_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.19/1.50  tff(c_50, plain, (![B_63, C_64, A_62]: (r2_hidden(B_63, k11_relat_1(C_64, A_62)) | ~r2_hidden(k4_tarski(A_62, B_63), C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.50  tff(c_1003, plain, (![A_197, C_198]: (r2_hidden('#skF_5'(A_197, k1_relat_1(A_197), C_198), k11_relat_1(A_197, C_198)) | ~v1_relat_1(A_197) | ~r2_hidden(C_198, k1_relat_1(A_197)))), inference(resolution, [status(thm)], [c_427, c_50])).
% 3.19/1.50  tff(c_1023, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_1003])).
% 3.19/1.50  tff(c_1028, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_52, c_1023])).
% 3.19/1.50  tff(c_1030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_1028])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 205
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 3
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 35
% 3.19/1.50  #Demod        : 72
% 3.19/1.50  #Tautology    : 81
% 3.19/1.50  #SimpNegUnit  : 36
% 3.19/1.50  #BackRed      : 5
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.50  Preprocessing        : 0.33
% 3.19/1.50  Parsing              : 0.17
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.40
% 3.19/1.50  Inferencing          : 0.16
% 3.19/1.50  Reduction            : 0.11
% 3.19/1.50  Demodulation         : 0.08
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.08
% 3.19/1.50  Abstraction          : 0.03
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.77
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
