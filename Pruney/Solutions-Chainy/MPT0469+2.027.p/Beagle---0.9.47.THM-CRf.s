%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   81 (  97 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 102 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_76,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_60,plain,(
    ! [A_60] :
      ( v1_relat_1(A_60)
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_50,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_6'(A_56,B_57),k2_relat_1(B_57))
      | ~ r2_hidden(A_56,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_286,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(k4_tarski('#skF_5'(A_106,k2_relat_1(A_106),C_107),C_107),A_106)
      | ~ r2_hidden(C_107,k2_relat_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_74,B_75] : k3_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_117])).

tff(c_170,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_170])).

tff(c_188,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_30,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_191,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_30])).

tff(c_77,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_64] :
      ( k1_tarski(A_64) = k1_xboole_0
      | ~ r2_hidden(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_199,plain,(
    ! [A_64] : ~ r2_hidden(A_64,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_82])).

tff(c_296,plain,(
    ! [C_108] : ~ r2_hidden(C_108,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_286,c_199])).

tff(c_304,plain,(
    ! [A_56] :
      ( ~ r2_hidden(A_56,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_296])).

tff(c_331,plain,(
    ! [A_111] : ~ r2_hidden(A_111,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_304])).

tff(c_339,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_331])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_339])).

tff(c_345,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_560,plain,(
    ! [A_154,C_155] :
      ( r2_hidden(k4_tarski('#skF_5'(A_154,k2_relat_1(A_154),C_155),C_155),A_154)
      | ~ r2_hidden(C_155,k2_relat_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_391,plain,(
    ! [A_122,B_123] : k3_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k1_tarski(A_122) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_400,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_391])).

tff(c_444,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k3_xboole_0(A_127,B_128)) = k4_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_453,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_444])).

tff(c_462,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_465,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_30])).

tff(c_351,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(k1_tarski(A_112),B_113)
      | ~ r2_hidden(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_356,plain,(
    ! [A_112] :
      ( k1_tarski(A_112) = k1_xboole_0
      | ~ r2_hidden(A_112,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_351,c_8])).

tff(c_473,plain,(
    ! [A_112] : ~ r2_hidden(A_112,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_356])).

tff(c_570,plain,(
    ! [C_156] : ~ r2_hidden(C_156,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_560,c_473])).

tff(c_582,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_570])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.57/1.33  
% 2.57/1.33  %Foreground sorts:
% 2.57/1.33  
% 2.57/1.33  
% 2.57/1.33  %Background operators:
% 2.57/1.33  
% 2.57/1.33  
% 2.57/1.33  %Foreground operators:
% 2.57/1.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.57/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.57/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.33  
% 2.57/1.35  tff(f_92, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.57/1.35  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.57/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.57/1.35  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.57/1.35  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 2.57/1.35  tff(f_79, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.57/1.35  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.57/1.35  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.57/1.35  tff(f_60, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.57/1.35  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.35  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.57/1.35  tff(f_58, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.57/1.35  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.57/1.35  tff(c_52, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.57/1.35  tff(c_76, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.57/1.35  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.57/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.57/1.35  tff(c_60, plain, (![A_60]: (v1_relat_1(A_60) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.35  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_60])).
% 2.57/1.35  tff(c_50, plain, (![A_56, B_57]: (r2_hidden('#skF_6'(A_56, B_57), k2_relat_1(B_57)) | ~r2_hidden(A_56, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.57/1.35  tff(c_286, plain, (![A_106, C_107]: (r2_hidden(k4_tarski('#skF_5'(A_106, k2_relat_1(A_106), C_107), C_107), A_106) | ~r2_hidden(C_107, k2_relat_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.57/1.35  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.35  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.35  tff(c_117, plain, (![A_74, B_75]: (k3_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75))=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.35  tff(c_126, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_117])).
% 2.57/1.35  tff(c_170, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.57/1.35  tff(c_179, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_170])).
% 2.57/1.35  tff(c_188, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_179])).
% 2.57/1.35  tff(c_30, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.35  tff(c_191, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_30])).
% 2.57/1.35  tff(c_77, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.35  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.35  tff(c_82, plain, (![A_64]: (k1_tarski(A_64)=k1_xboole_0 | ~r2_hidden(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_8])).
% 2.57/1.35  tff(c_199, plain, (![A_64]: (~r2_hidden(A_64, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_191, c_82])).
% 2.57/1.35  tff(c_296, plain, (![C_108]: (~r2_hidden(C_108, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_286, c_199])).
% 2.57/1.35  tff(c_304, plain, (![A_56]: (~r2_hidden(A_56, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_296])).
% 2.57/1.35  tff(c_331, plain, (![A_111]: (~r2_hidden(A_111, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_304])).
% 2.57/1.35  tff(c_339, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_331])).
% 2.57/1.35  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_339])).
% 2.57/1.35  tff(c_345, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.57/1.35  tff(c_560, plain, (![A_154, C_155]: (r2_hidden(k4_tarski('#skF_5'(A_154, k2_relat_1(A_154), C_155), C_155), A_154) | ~r2_hidden(C_155, k2_relat_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.57/1.35  tff(c_391, plain, (![A_122, B_123]: (k3_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k1_tarski(A_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.35  tff(c_400, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_391])).
% 2.57/1.35  tff(c_444, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k3_xboole_0(A_127, B_128))=k4_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.57/1.35  tff(c_453, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_400, c_444])).
% 2.57/1.35  tff(c_462, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 2.57/1.35  tff(c_465, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_462, c_30])).
% 2.57/1.35  tff(c_351, plain, (![A_112, B_113]: (r1_tarski(k1_tarski(A_112), B_113) | ~r2_hidden(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.35  tff(c_356, plain, (![A_112]: (k1_tarski(A_112)=k1_xboole_0 | ~r2_hidden(A_112, k1_xboole_0))), inference(resolution, [status(thm)], [c_351, c_8])).
% 2.57/1.35  tff(c_473, plain, (![A_112]: (~r2_hidden(A_112, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_465, c_356])).
% 2.57/1.35  tff(c_570, plain, (![C_156]: (~r2_hidden(C_156, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_560, c_473])).
% 2.57/1.35  tff(c_582, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_570])).
% 2.57/1.35  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_582])).
% 2.57/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  Inference rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Ref     : 0
% 2.57/1.35  #Sup     : 115
% 2.57/1.35  #Fact    : 0
% 2.57/1.35  #Define  : 0
% 2.57/1.35  #Split   : 1
% 2.57/1.35  #Chain   : 0
% 2.57/1.35  #Close   : 0
% 2.57/1.35  
% 2.57/1.35  Ordering : KBO
% 2.57/1.35  
% 2.57/1.35  Simplification rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Subsume      : 3
% 2.57/1.35  #Demod        : 22
% 2.57/1.35  #Tautology    : 88
% 2.57/1.35  #SimpNegUnit  : 10
% 2.57/1.35  #BackRed      : 5
% 2.57/1.35  
% 2.57/1.35  #Partial instantiations: 0
% 2.57/1.35  #Strategies tried      : 1
% 2.57/1.35  
% 2.57/1.35  Timing (in seconds)
% 2.57/1.35  ----------------------
% 2.57/1.35  Preprocessing        : 0.34
% 2.57/1.35  Parsing              : 0.17
% 2.57/1.35  CNF conversion       : 0.02
% 2.57/1.35  Main loop            : 0.25
% 2.57/1.35  Inferencing          : 0.11
% 2.57/1.35  Reduction            : 0.07
% 2.57/1.35  Demodulation         : 0.05
% 2.57/1.35  BG Simplification    : 0.02
% 2.57/1.35  Subsumption          : 0.03
% 2.57/1.35  Abstraction          : 0.02
% 2.57/1.35  MUC search           : 0.00
% 2.57/1.35  Cooper               : 0.00
% 2.57/1.35  Total                : 0.63
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.36  Index Deletion       : 0.00
% 2.57/1.36  Index Matching       : 0.00
% 2.57/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
