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
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 162 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 270 expanded)
%              Number of equality atoms :   46 ( 101 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_65,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),B_48) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_47] : k1_tarski(A_47) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_92])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_tarski(A_12),B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    ! [A_50,B_51] :
      ( v1_relat_1(k3_xboole_0(A_50,B_51))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_101,plain,(
    ! [A_11] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_102,plain,(
    ! [A_11] : ~ v1_relat_1(A_11) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_58])).

tff(c_107,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_50,plain,(
    ! [A_37] : k9_relat_1(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1360,plain,(
    ! [B_179,A_180] :
      ( k9_relat_1(B_179,A_180) != k1_xboole_0
      | ~ r1_tarski(A_180,k1_relat_1(B_179))
      | k1_xboole_0 = A_180
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1373,plain,(
    ! [B_181] :
      ( k9_relat_1(B_181,k1_relat_1(B_181)) != k1_xboole_0
      | k1_relat_1(B_181) = k1_xboole_0
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_26,c_1360])).

tff(c_1377,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1373])).

tff(c_1380,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1377])).

tff(c_52,plain,(
    ! [B_39,A_38] :
      ( k9_relat_1(B_39,A_38) != k1_xboole_0
      | ~ r1_tarski(A_38,k1_relat_1(B_39))
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1387,plain,(
    ! [A_38] :
      ( k9_relat_1(k1_xboole_0,A_38) != k1_xboole_0
      | ~ r1_tarski(A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_52])).

tff(c_1395,plain,(
    ! [A_182] :
      ( ~ r1_tarski(A_182,k1_xboole_0)
      | k1_xboole_0 = A_182 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_50,c_1387])).

tff(c_1399,plain,(
    ! [A_12] :
      ( k1_tarski(A_12) = k1_xboole_0
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_1395])).

tff(c_1406,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1399])).

tff(c_60,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_130,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_211,plain,(
    ! [B_83,A_84] :
      ( k9_relat_1(B_83,A_84) != k1_xboole_0
      | ~ r1_tarski(A_84,k1_relat_1(B_83))
      | k1_xboole_0 = A_84
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_224,plain,(
    ! [B_85] :
      ( k9_relat_1(B_85,k1_relat_1(B_85)) != k1_xboole_0
      | k1_relat_1(B_85) = k1_xboole_0
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_26,c_211])).

tff(c_228,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_224])).

tff(c_231,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_228])).

tff(c_1089,plain,(
    ! [A_154,B_155] :
      ( r2_hidden(k4_tarski('#skF_3'(A_154,B_155),'#skF_4'(A_154,B_155)),A_154)
      | r2_hidden('#skF_5'(A_154,B_155),B_155)
      | k1_relat_1(A_154) = B_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_238,plain,(
    ! [A_38] :
      ( k9_relat_1(k1_xboole_0,A_38) != k1_xboole_0
      | ~ r1_tarski(A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_52])).

tff(c_246,plain,(
    ! [A_86] :
      ( ~ r1_tarski(A_86,k1_xboole_0)
      | k1_xboole_0 = A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_50,c_238])).

tff(c_250,plain,(
    ! [A_12] :
      ( k1_tarski(A_12) = k1_xboole_0
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_246])).

tff(c_257,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_250])).

tff(c_1114,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_155),B_155)
      | k1_relat_1(k1_xboole_0) = B_155 ) ),
    inference(resolution,[status(thm)],[c_1089,c_257])).

tff(c_1137,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_156),B_156)
      | k1_xboole_0 = B_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_1114])).

tff(c_190,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k4_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,k11_relat_1(C_82,A_80))
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_205,plain,(
    ! [A_80,C_82,B_81] :
      ( r2_hidden(A_80,k1_relat_1(C_82))
      | ~ r2_hidden(B_81,k11_relat_1(C_82,A_80))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_190,c_38])).

tff(c_1219,plain,(
    ! [A_159,C_160] :
      ( r2_hidden(A_159,k1_relat_1(C_160))
      | ~ v1_relat_1(C_160)
      | k11_relat_1(C_160,A_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1137,c_205])).

tff(c_1252,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1219,c_129])).

tff(c_1266,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1252])).

tff(c_1268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1266])).

tff(c_1269,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1269])).

tff(c_1273,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1272,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1473,plain,(
    ! [C_191,A_192] :
      ( r2_hidden(k4_tarski(C_191,'#skF_6'(A_192,k1_relat_1(A_192),C_191)),A_192)
      | ~ r2_hidden(C_191,k1_relat_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [B_41,C_42,A_40] :
      ( r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3374,plain,(
    ! [A_309,C_310] :
      ( r2_hidden('#skF_6'(A_309,k1_relat_1(A_309),C_310),k11_relat_1(A_309,C_310))
      | ~ v1_relat_1(A_309)
      | ~ r2_hidden(C_310,k1_relat_1(A_309)) ) ),
    inference(resolution,[status(thm)],[c_1473,c_56])).

tff(c_3388,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_3374])).

tff(c_3397,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_58,c_3388])).

tff(c_3399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1406,c_3397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.91  
% 4.80/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.91  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5 > #skF_4
% 4.80/1.91  
% 4.80/1.91  %Foreground sorts:
% 4.80/1.91  
% 4.80/1.91  
% 4.80/1.91  %Background operators:
% 4.80/1.91  
% 4.80/1.91  
% 4.80/1.91  %Foreground operators:
% 4.80/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.91  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.80/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.80/1.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.80/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.80/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.80/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.91  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.80/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.80/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.80/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.80/1.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.80/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.80/1.91  
% 4.80/1.93  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.80/1.93  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.80/1.93  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.80/1.93  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.80/1.93  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.80/1.93  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.80/1.93  tff(f_65, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 4.80/1.93  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.80/1.93  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 4.80/1.93  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.80/1.93  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.80/1.93  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.80/1.93  tff(c_92, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.93  tff(c_96, plain, (![A_47]: (k1_tarski(A_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_92])).
% 4.80/1.93  tff(c_32, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.80/1.93  tff(c_28, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.80/1.93  tff(c_98, plain, (![A_50, B_51]: (v1_relat_1(k3_xboole_0(A_50, B_51)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.80/1.93  tff(c_101, plain, (![A_11]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_28, c_98])).
% 4.80/1.93  tff(c_102, plain, (![A_11]: (~v1_relat_1(A_11))), inference(splitLeft, [status(thm)], [c_101])).
% 4.80/1.93  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.93  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_58])).
% 4.80/1.93  tff(c_107, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_101])).
% 4.80/1.93  tff(c_50, plain, (![A_37]: (k9_relat_1(k1_xboole_0, A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.80/1.93  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.93  tff(c_1360, plain, (![B_179, A_180]: (k9_relat_1(B_179, A_180)!=k1_xboole_0 | ~r1_tarski(A_180, k1_relat_1(B_179)) | k1_xboole_0=A_180 | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.93  tff(c_1373, plain, (![B_181]: (k9_relat_1(B_181, k1_relat_1(B_181))!=k1_xboole_0 | k1_relat_1(B_181)=k1_xboole_0 | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_26, c_1360])).
% 4.80/1.93  tff(c_1377, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1373])).
% 4.80/1.93  tff(c_1380, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1377])).
% 4.80/1.93  tff(c_52, plain, (![B_39, A_38]: (k9_relat_1(B_39, A_38)!=k1_xboole_0 | ~r1_tarski(A_38, k1_relat_1(B_39)) | k1_xboole_0=A_38 | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.93  tff(c_1387, plain, (![A_38]: (k9_relat_1(k1_xboole_0, A_38)!=k1_xboole_0 | ~r1_tarski(A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1380, c_52])).
% 4.80/1.93  tff(c_1395, plain, (![A_182]: (~r1_tarski(A_182, k1_xboole_0) | k1_xboole_0=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_50, c_1387])).
% 4.80/1.93  tff(c_1399, plain, (![A_12]: (k1_tarski(A_12)=k1_xboole_0 | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_1395])).
% 4.80/1.93  tff(c_1406, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_96, c_1399])).
% 4.80/1.93  tff(c_60, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.93  tff(c_129, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.80/1.93  tff(c_66, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.93  tff(c_130, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 4.80/1.93  tff(c_211, plain, (![B_83, A_84]: (k9_relat_1(B_83, A_84)!=k1_xboole_0 | ~r1_tarski(A_84, k1_relat_1(B_83)) | k1_xboole_0=A_84 | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.93  tff(c_224, plain, (![B_85]: (k9_relat_1(B_85, k1_relat_1(B_85))!=k1_xboole_0 | k1_relat_1(B_85)=k1_xboole_0 | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_26, c_211])).
% 4.80/1.93  tff(c_228, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_224])).
% 4.80/1.93  tff(c_231, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_228])).
% 4.80/1.93  tff(c_1089, plain, (![A_154, B_155]: (r2_hidden(k4_tarski('#skF_3'(A_154, B_155), '#skF_4'(A_154, B_155)), A_154) | r2_hidden('#skF_5'(A_154, B_155), B_155) | k1_relat_1(A_154)=B_155)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.80/1.93  tff(c_238, plain, (![A_38]: (k9_relat_1(k1_xboole_0, A_38)!=k1_xboole_0 | ~r1_tarski(A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_231, c_52])).
% 4.80/1.93  tff(c_246, plain, (![A_86]: (~r1_tarski(A_86, k1_xboole_0) | k1_xboole_0=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_50, c_238])).
% 4.80/1.93  tff(c_250, plain, (![A_12]: (k1_tarski(A_12)=k1_xboole_0 | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_246])).
% 4.80/1.93  tff(c_257, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_96, c_250])).
% 4.80/1.93  tff(c_1114, plain, (![B_155]: (r2_hidden('#skF_5'(k1_xboole_0, B_155), B_155) | k1_relat_1(k1_xboole_0)=B_155)), inference(resolution, [status(thm)], [c_1089, c_257])).
% 4.80/1.93  tff(c_1137, plain, (![B_156]: (r2_hidden('#skF_5'(k1_xboole_0, B_156), B_156) | k1_xboole_0=B_156)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_1114])).
% 4.80/1.93  tff(c_190, plain, (![A_80, B_81, C_82]: (r2_hidden(k4_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, k11_relat_1(C_82, A_80)) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.80/1.93  tff(c_38, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.80/1.93  tff(c_205, plain, (![A_80, C_82, B_81]: (r2_hidden(A_80, k1_relat_1(C_82)) | ~r2_hidden(B_81, k11_relat_1(C_82, A_80)) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_190, c_38])).
% 4.80/1.93  tff(c_1219, plain, (![A_159, C_160]: (r2_hidden(A_159, k1_relat_1(C_160)) | ~v1_relat_1(C_160) | k11_relat_1(C_160, A_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1137, c_205])).
% 4.80/1.93  tff(c_1252, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1219, c_129])).
% 4.80/1.93  tff(c_1266, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1252])).
% 4.80/1.93  tff(c_1268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1266])).
% 4.80/1.93  tff(c_1269, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 4.80/1.93  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_1269])).
% 4.80/1.93  tff(c_1273, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_60])).
% 4.80/1.93  tff(c_1272, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 4.80/1.93  tff(c_1473, plain, (![C_191, A_192]: (r2_hidden(k4_tarski(C_191, '#skF_6'(A_192, k1_relat_1(A_192), C_191)), A_192) | ~r2_hidden(C_191, k1_relat_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.80/1.93  tff(c_56, plain, (![B_41, C_42, A_40]: (r2_hidden(B_41, k11_relat_1(C_42, A_40)) | ~r2_hidden(k4_tarski(A_40, B_41), C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.80/1.93  tff(c_3374, plain, (![A_309, C_310]: (r2_hidden('#skF_6'(A_309, k1_relat_1(A_309), C_310), k11_relat_1(A_309, C_310)) | ~v1_relat_1(A_309) | ~r2_hidden(C_310, k1_relat_1(A_309)))), inference(resolution, [status(thm)], [c_1473, c_56])).
% 4.80/1.93  tff(c_3388, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1272, c_3374])).
% 4.80/1.93  tff(c_3397, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_58, c_3388])).
% 4.80/1.93  tff(c_3399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1406, c_3397])).
% 4.80/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.93  
% 4.80/1.93  Inference rules
% 4.80/1.93  ----------------------
% 4.80/1.93  #Ref     : 0
% 4.80/1.93  #Sup     : 664
% 4.80/1.93  #Fact    : 0
% 4.80/1.93  #Define  : 0
% 4.80/1.93  #Split   : 4
% 4.80/1.93  #Chain   : 0
% 4.80/1.93  #Close   : 0
% 4.80/1.93  
% 4.80/1.93  Ordering : KBO
% 4.80/1.93  
% 4.80/1.93  Simplification rules
% 4.80/1.93  ----------------------
% 4.80/1.93  #Subsume      : 106
% 4.80/1.93  #Demod        : 344
% 4.80/1.93  #Tautology    : 133
% 4.80/1.93  #SimpNegUnit  : 58
% 4.80/1.93  #BackRed      : 22
% 4.80/1.93  
% 4.80/1.93  #Partial instantiations: 0
% 4.80/1.93  #Strategies tried      : 1
% 4.80/1.93  
% 4.80/1.93  Timing (in seconds)
% 4.80/1.93  ----------------------
% 5.15/1.94  Preprocessing        : 0.31
% 5.15/1.94  Parsing              : 0.16
% 5.15/1.94  CNF conversion       : 0.03
% 5.15/1.94  Main loop            : 0.86
% 5.15/1.94  Inferencing          : 0.31
% 5.15/1.94  Reduction            : 0.25
% 5.15/1.94  Demodulation         : 0.17
% 5.15/1.94  BG Simplification    : 0.04
% 5.15/1.94  Subsumption          : 0.18
% 5.15/1.94  Abstraction          : 0.04
% 5.15/1.94  MUC search           : 0.00
% 5.15/1.94  Cooper               : 0.00
% 5.15/1.94  Total                : 1.21
% 5.15/1.94  Index Insertion      : 0.00
% 5.15/1.94  Index Deletion       : 0.00
% 5.15/1.94  Index Matching       : 0.00
% 5.15/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
