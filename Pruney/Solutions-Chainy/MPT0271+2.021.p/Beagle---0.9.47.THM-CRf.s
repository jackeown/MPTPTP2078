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
% DateTime   : Thu Dec  3 09:53:04 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 161 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 222 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_47,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_12,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_132,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,B_46)
      | ~ r1_tarski(A_45,k3_xboole_0(B_46,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [B_46,C_47] : r1_tarski(k3_xboole_0(B_46,C_47),B_46) ),
    inference(resolution,[status(thm)],[c_53,c_132])).

tff(c_189,plain,(
    ! [A_57,B_58] :
      ( r2_xboole_0(A_57,B_58)
      | B_58 = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_12] : ~ r2_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_189,c_16])).

tff(c_229,plain,(
    ! [C_60] : k3_xboole_0(k1_xboole_0,C_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_207])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [B_48,C_49] : r1_tarski(k3_xboole_0(B_48,C_49),B_48) ),
    inference(resolution,[status(thm)],[c_53,c_132])).

tff(c_151,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_234,plain,(
    ! [C_60] : r1_tarski(k1_xboole_0,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_151])).

tff(c_34,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_322,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_328,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_171])).

tff(c_336,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_328])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( B_24 = A_23
      | ~ r1_tarski(k1_tarski(A_23),k1_tarski(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_355,plain,(
    ! [B_24] :
      ( B_24 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_30])).

tff(c_364,plain,(
    ! [B_24] : B_24 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_355])).

tff(c_366,plain,(
    ! [B_65] : B_65 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_355])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_tarski(A_18,B_19),C_20) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_422,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_24])).

tff(c_591,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_422])).

tff(c_592,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_112,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(k1_tarski(A_43),B_44) = B_44
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_18])).

tff(c_879,plain,(
    ! [A_1235,B_1236,C_1237] :
      ( r1_tarski(k4_xboole_0(A_1235,B_1236),C_1237)
      | ~ r1_tarski(A_1235,k2_xboole_0(B_1236,C_1237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_673,plain,(
    ! [A_1225,B_1226] :
      ( r2_xboole_0(A_1225,B_1226)
      | B_1226 = A_1225
      | ~ r1_tarski(A_1225,B_1226) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_690,plain,(
    ! [A_1225] :
      ( k1_xboole_0 = A_1225
      | ~ r1_tarski(A_1225,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_673,c_16])).

tff(c_883,plain,(
    ! [A_1235,B_1236] :
      ( k4_xboole_0(A_1235,B_1236) = k1_xboole_0
      | ~ r1_tarski(A_1235,k2_xboole_0(B_1236,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_879,c_690])).

tff(c_942,plain,(
    ! [A_1240,B_1241] :
      ( k4_xboole_0(A_1240,B_1241) = k1_xboole_0
      | ~ r1_tarski(A_1240,B_1241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_883])).

tff(c_1372,plain,(
    ! [A_1266,B_1267] :
      ( k4_xboole_0(k1_tarski(A_1266),B_1267) = k1_xboole_0
      | ~ r2_hidden(A_1266,B_1267) ) ),
    inference(resolution,[status(thm)],[c_118,c_942])).

tff(c_593,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_606,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_36])).

tff(c_1395,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_606])).

tff(c_1420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_1395])).

tff(c_1421,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1524,plain,(
    ! [A_1287,B_1288] :
      ( k2_xboole_0(k1_tarski(A_1287),B_1288) = B_1288
      | ~ r2_hidden(A_1287,B_1288) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1530,plain,(
    ! [A_1287,B_1288] :
      ( r1_tarski(k1_tarski(A_1287),B_1288)
      | ~ r2_hidden(A_1287,B_1288) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1524,c_18])).

tff(c_1825,plain,(
    ! [A_1313,B_1314,C_1315] :
      ( r1_tarski(k4_xboole_0(A_1313,B_1314),C_1315)
      | ~ r1_tarski(A_1313,k2_xboole_0(B_1314,C_1315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1622,plain,(
    ! [A_1303,B_1304] :
      ( r2_xboole_0(A_1303,B_1304)
      | B_1304 = A_1303
      | ~ r1_tarski(A_1303,B_1304) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1639,plain,(
    ! [A_1303] :
      ( k1_xboole_0 = A_1303
      | ~ r1_tarski(A_1303,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1622,c_16])).

tff(c_1829,plain,(
    ! [A_1313,B_1314] :
      ( k4_xboole_0(A_1313,B_1314) = k1_xboole_0
      | ~ r1_tarski(A_1313,k2_xboole_0(B_1314,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1825,c_1639])).

tff(c_1887,plain,(
    ! [A_1318,B_1319] :
      ( k4_xboole_0(A_1318,B_1319) = k1_xboole_0
      | ~ r1_tarski(A_1318,B_1319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1829])).

tff(c_2318,plain,(
    ! [A_1344,B_1345] :
      ( k4_xboole_0(k1_tarski(A_1344),B_1345) = k1_xboole_0
      | ~ r2_hidden(A_1344,B_1345) ) ),
    inference(resolution,[status(thm)],[c_1530,c_1887])).

tff(c_1422,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1423,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_1425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1423])).

tff(c_1426,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2341,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_1426])).

tff(c_2363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_2341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.58  %$ r2_xboole_0 > r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.40/1.58  
% 3.40/1.58  %Foreground sorts:
% 3.40/1.58  
% 3.40/1.58  
% 3.40/1.58  %Background operators:
% 3.40/1.58  
% 3.40/1.58  
% 3.40/1.58  %Foreground operators:
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.58  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.58  
% 3.40/1.59  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.40/1.59  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.40/1.59  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.40/1.59  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.40/1.59  tff(f_47, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 3.40/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.40/1.59  tff(f_72, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.40/1.59  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.40/1.59  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.40/1.59  tff(f_58, axiom, (![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.40/1.59  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.40/1.59  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.40/1.59  tff(c_12, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.40/1.59  tff(c_50, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.59  tff(c_53, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_50])).
% 3.40/1.59  tff(c_132, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, B_46) | ~r1_tarski(A_45, k3_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.59  tff(c_143, plain, (![B_46, C_47]: (r1_tarski(k3_xboole_0(B_46, C_47), B_46))), inference(resolution, [status(thm)], [c_53, c_132])).
% 3.40/1.59  tff(c_189, plain, (![A_57, B_58]: (r2_xboole_0(A_57, B_58) | B_58=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.59  tff(c_16, plain, (![A_12]: (~r2_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.59  tff(c_207, plain, (![A_59]: (k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_189, c_16])).
% 3.40/1.59  tff(c_229, plain, (![C_60]: (k3_xboole_0(k1_xboole_0, C_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_207])).
% 3.40/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.59  tff(c_144, plain, (![B_48, C_49]: (r1_tarski(k3_xboole_0(B_48, C_49), B_48))), inference(resolution, [status(thm)], [c_53, c_132])).
% 3.40/1.59  tff(c_151, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 3.40/1.59  tff(c_234, plain, (![C_60]: (r1_tarski(k1_xboole_0, C_60))), inference(superposition, [status(thm), theory('equality')], [c_229, c_151])).
% 3.40/1.59  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_55, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 3.40/1.59  tff(c_322, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.40/1.59  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_171, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.40/1.59  tff(c_328, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_322, c_171])).
% 3.40/1.59  tff(c_336, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_55, c_328])).
% 3.40/1.59  tff(c_30, plain, (![B_24, A_23]: (B_24=A_23 | ~r1_tarski(k1_tarski(A_23), k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.59  tff(c_355, plain, (![B_24]: (B_24='#skF_3' | ~r1_tarski(k1_xboole_0, k1_tarski(B_24)))), inference(superposition, [status(thm), theory('equality')], [c_336, c_30])).
% 3.40/1.59  tff(c_364, plain, (![B_24]: (B_24='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_355])).
% 3.40/1.59  tff(c_366, plain, (![B_65]: (B_65='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_355])).
% 3.40/1.59  tff(c_24, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_tarski(A_18, B_19), C_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.40/1.59  tff(c_422, plain, (k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_366, c_24])).
% 3.40/1.59  tff(c_591, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_364, c_422])).
% 3.40/1.59  tff(c_592, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.40/1.59  tff(c_112, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)=B_44 | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.59  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.59  tff(c_118, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_112, c_18])).
% 3.40/1.59  tff(c_879, plain, (![A_1235, B_1236, C_1237]: (r1_tarski(k4_xboole_0(A_1235, B_1236), C_1237) | ~r1_tarski(A_1235, k2_xboole_0(B_1236, C_1237)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.59  tff(c_673, plain, (![A_1225, B_1226]: (r2_xboole_0(A_1225, B_1226) | B_1226=A_1225 | ~r1_tarski(A_1225, B_1226))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.59  tff(c_690, plain, (![A_1225]: (k1_xboole_0=A_1225 | ~r1_tarski(A_1225, k1_xboole_0))), inference(resolution, [status(thm)], [c_673, c_16])).
% 3.40/1.59  tff(c_883, plain, (![A_1235, B_1236]: (k4_xboole_0(A_1235, B_1236)=k1_xboole_0 | ~r1_tarski(A_1235, k2_xboole_0(B_1236, k1_xboole_0)))), inference(resolution, [status(thm)], [c_879, c_690])).
% 3.40/1.59  tff(c_942, plain, (![A_1240, B_1241]: (k4_xboole_0(A_1240, B_1241)=k1_xboole_0 | ~r1_tarski(A_1240, B_1241))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_883])).
% 3.40/1.59  tff(c_1372, plain, (![A_1266, B_1267]: (k4_xboole_0(k1_tarski(A_1266), B_1267)=k1_xboole_0 | ~r2_hidden(A_1266, B_1267))), inference(resolution, [status(thm)], [c_118, c_942])).
% 3.40/1.59  tff(c_593, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.40/1.59  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_606, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_593, c_36])).
% 3.40/1.59  tff(c_1395, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1372, c_606])).
% 3.40/1.59  tff(c_1420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_592, c_1395])).
% 3.40/1.59  tff(c_1421, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 3.40/1.59  tff(c_1524, plain, (![A_1287, B_1288]: (k2_xboole_0(k1_tarski(A_1287), B_1288)=B_1288 | ~r2_hidden(A_1287, B_1288))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.59  tff(c_1530, plain, (![A_1287, B_1288]: (r1_tarski(k1_tarski(A_1287), B_1288) | ~r2_hidden(A_1287, B_1288))), inference(superposition, [status(thm), theory('equality')], [c_1524, c_18])).
% 3.40/1.59  tff(c_1825, plain, (![A_1313, B_1314, C_1315]: (r1_tarski(k4_xboole_0(A_1313, B_1314), C_1315) | ~r1_tarski(A_1313, k2_xboole_0(B_1314, C_1315)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.59  tff(c_1622, plain, (![A_1303, B_1304]: (r2_xboole_0(A_1303, B_1304) | B_1304=A_1303 | ~r1_tarski(A_1303, B_1304))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.59  tff(c_1639, plain, (![A_1303]: (k1_xboole_0=A_1303 | ~r1_tarski(A_1303, k1_xboole_0))), inference(resolution, [status(thm)], [c_1622, c_16])).
% 3.40/1.59  tff(c_1829, plain, (![A_1313, B_1314]: (k4_xboole_0(A_1313, B_1314)=k1_xboole_0 | ~r1_tarski(A_1313, k2_xboole_0(B_1314, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1825, c_1639])).
% 3.40/1.59  tff(c_1887, plain, (![A_1318, B_1319]: (k4_xboole_0(A_1318, B_1319)=k1_xboole_0 | ~r1_tarski(A_1318, B_1319))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1829])).
% 3.40/1.59  tff(c_2318, plain, (![A_1344, B_1345]: (k4_xboole_0(k1_tarski(A_1344), B_1345)=k1_xboole_0 | ~r2_hidden(A_1344, B_1345))), inference(resolution, [status(thm)], [c_1530, c_1887])).
% 3.40/1.59  tff(c_1422, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 3.40/1.59  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.59  tff(c_1423, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 3.40/1.59  tff(c_1425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1422, c_1423])).
% 3.40/1.59  tff(c_1426, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.40/1.59  tff(c_2341, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2318, c_1426])).
% 3.40/1.59  tff(c_2363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1421, c_2341])).
% 3.40/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.59  
% 3.40/1.59  Inference rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Ref     : 0
% 3.40/1.59  #Sup     : 573
% 3.40/1.59  #Fact    : 0
% 3.40/1.59  #Define  : 0
% 3.40/1.59  #Split   : 3
% 3.40/1.59  #Chain   : 0
% 3.40/1.59  #Close   : 0
% 3.40/1.59  
% 3.40/1.59  Ordering : KBO
% 3.40/1.59  
% 3.40/1.59  Simplification rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Subsume      : 60
% 3.40/1.59  #Demod        : 228
% 3.40/1.59  #Tautology    : 284
% 3.40/1.59  #SimpNegUnit  : 4
% 3.40/1.59  #BackRed      : 1
% 3.40/1.59  
% 3.40/1.59  #Partial instantiations: 93
% 3.40/1.59  #Strategies tried      : 1
% 3.40/1.59  
% 3.40/1.59  Timing (in seconds)
% 3.40/1.59  ----------------------
% 3.40/1.59  Preprocessing        : 0.31
% 3.40/1.59  Parsing              : 0.16
% 3.40/1.59  CNF conversion       : 0.02
% 3.40/1.59  Main loop            : 0.52
% 3.40/1.59  Inferencing          : 0.20
% 3.40/1.59  Reduction            : 0.17
% 3.40/1.59  Demodulation         : 0.13
% 3.40/1.60  BG Simplification    : 0.02
% 3.40/1.60  Subsumption          : 0.08
% 3.40/1.60  Abstraction          : 0.02
% 3.40/1.60  MUC search           : 0.00
% 3.40/1.60  Cooper               : 0.00
% 3.40/1.60  Total                : 0.86
% 3.40/1.60  Index Insertion      : 0.00
% 3.40/1.60  Index Deletion       : 0.00
% 3.40/1.60  Index Matching       : 0.00
% 3.40/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
