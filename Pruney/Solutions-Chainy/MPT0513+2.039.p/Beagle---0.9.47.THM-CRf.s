%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 147 expanded)
%              Number of leaves         :   40 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 204 expanded)
%              Number of equality atoms :   37 ( 104 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_84,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_relat_1(A_69)) = A_69
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_93,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_84])).

tff(c_97,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_40,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),A_42)
      | v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_137,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tarski(A_79),B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_81] :
      ( k1_tarski(A_81) = k1_xboole_0
      | ~ r2_hidden(A_81,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137,c_6])).

tff(c_147,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_150,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_147])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_157,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_30])).

tff(c_164,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_150,c_157])).

tff(c_10,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_87,B_88] : k3_xboole_0(k1_tarski(A_87),k2_tarski(A_87,B_88)) = k1_tarski(A_87) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [A_87,B_88] : k5_xboole_0(k1_tarski(A_87),k1_tarski(A_87)) = k4_xboole_0(k1_tarski(A_87),k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_225,plain,(
    ! [A_92,B_93] : k4_xboole_0(k1_tarski(A_92),k2_tarski(A_92,B_93)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_239,plain,(
    ! [A_94] : k4_xboole_0(k1_tarski(A_94),k1_tarski(A_94)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_225])).

tff(c_246,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_239])).

tff(c_252,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_246])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_252])).

tff(c_256,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_255,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_459,plain,(
    ! [C_127,A_128,B_129] :
      ( k7_relat_1(k7_relat_1(C_127,A_128),B_129) = k7_relat_1(C_127,A_128)
      | ~ r1_tarski(A_128,B_129)
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_478,plain,(
    ! [B_129] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_129)
      | ~ r1_tarski(k1_xboole_0,B_129)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_459])).

tff(c_490,plain,(
    ! [B_129] : k7_relat_1(k1_xboole_0,B_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_4,c_255,c_478])).

tff(c_50,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.31/1.29  
% 2.31/1.29  %Foreground sorts:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Background operators:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Foreground operators:
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.29  
% 2.31/1.30  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.31/1.30  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.31/1.30  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.31/1.30  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.31/1.30  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.31/1.30  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.30  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.30  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.31/1.30  tff(f_55, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.31/1.30  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.30  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.31/1.30  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.31/1.30  tff(f_88, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.31/1.30  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.30  tff(c_84, plain, (![A_69]: (k7_relat_1(A_69, k1_relat_1(A_69))=A_69 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.31/1.30  tff(c_93, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_84])).
% 2.31/1.30  tff(c_97, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_93])).
% 2.31/1.30  tff(c_40, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), A_42) | v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.31/1.30  tff(c_137, plain, (![A_79, B_80]: (r1_tarski(k1_tarski(A_79), B_80) | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.30  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.30  tff(c_143, plain, (![A_81]: (k1_tarski(A_81)=k1_xboole_0 | ~r2_hidden(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_137, c_6])).
% 2.31/1.30  tff(c_147, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_143])).
% 2.31/1.30  tff(c_150, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_97, c_147])).
% 2.31/1.30  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.31/1.30  tff(c_157, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_150, c_30])).
% 2.31/1.30  tff(c_164, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_150, c_157])).
% 2.31/1.30  tff(c_10, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.30  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.30  tff(c_196, plain, (![A_87, B_88]: (k3_xboole_0(k1_tarski(A_87), k2_tarski(A_87, B_88))=k1_tarski(A_87))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.30  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.30  tff(c_202, plain, (![A_87, B_88]: (k5_xboole_0(k1_tarski(A_87), k1_tarski(A_87))=k4_xboole_0(k1_tarski(A_87), k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2])).
% 2.31/1.30  tff(c_225, plain, (![A_92, B_93]: (k4_xboole_0(k1_tarski(A_92), k2_tarski(A_92, B_93))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_202])).
% 2.31/1.30  tff(c_239, plain, (![A_94]: (k4_xboole_0(k1_tarski(A_94), k1_tarski(A_94))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_225])).
% 2.31/1.30  tff(c_246, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_150, c_239])).
% 2.31/1.30  tff(c_252, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_246])).
% 2.31/1.30  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_252])).
% 2.31/1.30  tff(c_256, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_93])).
% 2.31/1.30  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.30  tff(c_255, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 2.31/1.30  tff(c_459, plain, (![C_127, A_128, B_129]: (k7_relat_1(k7_relat_1(C_127, A_128), B_129)=k7_relat_1(C_127, A_128) | ~r1_tarski(A_128, B_129) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.30  tff(c_478, plain, (![B_129]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_129) | ~r1_tarski(k1_xboole_0, B_129) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_255, c_459])).
% 2.31/1.30  tff(c_490, plain, (![B_129]: (k7_relat_1(k1_xboole_0, B_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_4, c_255, c_478])).
% 2.31/1.30  tff(c_50, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.31/1.30  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_490, c_50])).
% 2.31/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  Inference rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Ref     : 0
% 2.31/1.30  #Sup     : 103
% 2.31/1.30  #Fact    : 0
% 2.31/1.30  #Define  : 0
% 2.31/1.30  #Split   : 1
% 2.31/1.30  #Chain   : 0
% 2.31/1.30  #Close   : 0
% 2.31/1.30  
% 2.31/1.30  Ordering : KBO
% 2.31/1.30  
% 2.31/1.30  Simplification rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Subsume      : 1
% 2.31/1.30  #Demod        : 26
% 2.31/1.30  #Tautology    : 78
% 2.31/1.30  #SimpNegUnit  : 5
% 2.31/1.30  #BackRed      : 4
% 2.31/1.30  
% 2.31/1.30  #Partial instantiations: 0
% 2.31/1.30  #Strategies tried      : 1
% 2.31/1.30  
% 2.31/1.30  Timing (in seconds)
% 2.31/1.30  ----------------------
% 2.31/1.31  Preprocessing        : 0.33
% 2.31/1.31  Parsing              : 0.17
% 2.31/1.31  CNF conversion       : 0.02
% 2.31/1.31  Main loop            : 0.21
% 2.31/1.31  Inferencing          : 0.08
% 2.31/1.31  Reduction            : 0.06
% 2.31/1.31  Demodulation         : 0.04
% 2.31/1.31  BG Simplification    : 0.02
% 2.31/1.31  Subsumption          : 0.02
% 2.31/1.31  Abstraction          : 0.01
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.56
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
