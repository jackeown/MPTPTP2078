%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:27 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 163 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_38] : k1_setfam_1(k1_tarski(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_308,plain,(
    ! [A_104,B_105] : k1_setfam_1(k2_tarski(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_317,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = k1_setfam_1(k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_308])).

tff(c_320,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_317])).

tff(c_366,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_366])).

tff(c_378,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_375])).

tff(c_40,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_71] :
      ( k1_tarski(A_71) = k1_xboole_0
      | ~ r2_hidden(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_93,c_6])).

tff(c_104,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_99])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_106,plain,(
    ! [A_72] :
      ( k8_relat_1(k2_relat_1(A_72),A_72) = A_72
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_106])).

tff(c_119,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_115])).

tff(c_242,plain,(
    ! [B_100,A_101,C_102] :
      ( k8_relat_1(B_100,k8_relat_1(A_101,C_102)) = k8_relat_1(A_101,C_102)
      | ~ r1_tarski(A_101,B_100)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_261,plain,(
    ! [B_100] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_100,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_100)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_242])).

tff(c_273,plain,(
    ! [B_100] : k8_relat_1(B_100,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_4,c_119,c_261])).

tff(c_50,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_50])).

tff(c_279,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_357,plain,(
    ! [B_115] : k4_xboole_0(k1_tarski(B_115),k1_tarski(B_115)) != k1_tarski(B_115) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_360,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_357])).

tff(c_364,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_360])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.33  
% 2.26/1.34  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.26/1.34  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.26/1.34  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.34  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.26/1.34  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.26/1.34  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.26/1.34  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.26/1.34  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.26/1.34  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.26/1.34  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.34  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 2.26/1.34  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.26/1.34  tff(f_88, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 2.26/1.34  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.26/1.34  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_32, plain, (![A_38]: (k1_setfam_1(k1_tarski(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.34  tff(c_10, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.34  tff(c_308, plain, (![A_104, B_105]: (k1_setfam_1(k2_tarski(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.34  tff(c_317, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=k1_setfam_1(k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_308])).
% 2.26/1.34  tff(c_320, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_317])).
% 2.26/1.34  tff(c_366, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.34  tff(c_375, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_320, c_366])).
% 2.26/1.34  tff(c_378, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_375])).
% 2.26/1.34  tff(c_40, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.34  tff(c_93, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.34  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.34  tff(c_99, plain, (![A_71]: (k1_tarski(A_71)=k1_xboole_0 | ~r2_hidden(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_93, c_6])).
% 2.26/1.34  tff(c_104, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_99])).
% 2.26/1.34  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_104])).
% 2.26/1.34  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.34  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.26/1.34  tff(c_106, plain, (![A_72]: (k8_relat_1(k2_relat_1(A_72), A_72)=A_72 | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.26/1.34  tff(c_115, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_106])).
% 2.26/1.34  tff(c_119, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_115])).
% 2.26/1.34  tff(c_242, plain, (![B_100, A_101, C_102]: (k8_relat_1(B_100, k8_relat_1(A_101, C_102))=k8_relat_1(A_101, C_102) | ~r1_tarski(A_101, B_100) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.34  tff(c_261, plain, (![B_100]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_100, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_100) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_242])).
% 2.26/1.34  tff(c_273, plain, (![B_100]: (k8_relat_1(B_100, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_4, c_119, c_261])).
% 2.26/1.34  tff(c_50, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.26/1.34  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_273, c_50])).
% 2.26/1.34  tff(c_279, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_104])).
% 2.26/1.34  tff(c_357, plain, (![B_115]: (k4_xboole_0(k1_tarski(B_115), k1_tarski(B_115))!=k1_tarski(B_115))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.34  tff(c_360, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_279, c_357])).
% 2.26/1.34  tff(c_364, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_360])).
% 2.26/1.34  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_364])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 80
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 1
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 2
% 2.26/1.34  #Demod        : 22
% 2.26/1.34  #Tautology    : 62
% 2.26/1.34  #SimpNegUnit  : 3
% 2.26/1.34  #BackRed      : 5
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.32
% 2.26/1.34  Parsing              : 0.16
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.21
% 2.26/1.34  Inferencing          : 0.08
% 2.26/1.34  Reduction            : 0.07
% 2.26/1.34  Demodulation         : 0.05
% 2.26/1.34  BG Simplification    : 0.02
% 2.62/1.34  Subsumption          : 0.03
% 2.62/1.34  Abstraction          : 0.02
% 2.62/1.34  MUC search           : 0.00
% 2.62/1.34  Cooper               : 0.00
% 2.62/1.34  Total                : 0.56
% 2.62/1.34  Index Insertion      : 0.00
% 2.62/1.34  Index Deletion       : 0.00
% 2.62/1.34  Index Matching       : 0.00
% 2.62/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
