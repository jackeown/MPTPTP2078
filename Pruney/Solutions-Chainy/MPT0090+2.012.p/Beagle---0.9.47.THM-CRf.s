%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 203 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 246 expanded)
%              Number of equality atoms :   57 ( 140 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_35,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_40,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | k3_xboole_0(A_30,B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_6])).

tff(c_115,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_35])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_12])).

tff(c_571,plain,(
    ! [A_48,B_49] : k3_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [B_17,A_18] :
      ( r1_xboole_0(B_17,A_18)
      | ~ r1_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_36])).

tff(c_53,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_13,A_12] : k3_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_53])).

tff(c_590,plain,(
    ! [B_49] : k4_xboole_0(B_49,B_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_63])).

tff(c_620,plain,(
    ! [B_50] : k4_xboole_0(B_50,B_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_63])).

tff(c_932,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = k3_xboole_0(B_58,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_12])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),k4_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_973,plain,(
    ! [B_58] : k2_xboole_0(k4_xboole_0(B_58,k1_xboole_0),k4_xboole_0(B_58,B_58)) = B_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_14])).

tff(c_1013,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_590,c_973])).

tff(c_643,plain,(
    ! [B_50] : k4_xboole_0(B_50,k1_xboole_0) = k3_xboole_0(B_50,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_12])).

tff(c_1023,plain,(
    ! [B_50] : k3_xboole_0(B_50,B_50) = B_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_643])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_146,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_146])).

tff(c_931,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_179])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_1090,plain,(
    k3_xboole_0('#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_116])).

tff(c_1130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1090])).

tff(c_1131,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1136,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_63])).

tff(c_1149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1136])).

tff(c_1150,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1162,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_16])).

tff(c_1166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_1162])).

tff(c_1168,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1184,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1168,c_18])).

tff(c_1169,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | ~ r1_xboole_0(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1178,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_1169])).

tff(c_1194,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1213,plain,(
    ! [B_13,A_12] : k3_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1178,c_1194])).

tff(c_1322,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1331,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,k3_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_12])).

tff(c_1777,plain,(
    ! [A_84,B_85] : k3_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1331])).

tff(c_1825,plain,(
    ! [B_13,A_12] : k3_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = k3_xboole_0(B_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1777])).

tff(c_1856,plain,(
    ! [B_13] : k3_xboole_0(B_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_1825])).

tff(c_1167,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1217,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1167,c_1194])).

tff(c_1361,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_1322])).

tff(c_1266,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1287,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1266])).

tff(c_1952,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1287])).

tff(c_1450,plain,(
    ! [A_80,B_81] : k2_xboole_0(k3_xboole_0(A_80,B_81),k4_xboole_0(A_80,B_81)) = A_80 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1468,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,k4_xboole_0(A_8,B_9)),k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1450])).

tff(c_2225,plain,(
    ! [A_95,B_96] : k2_xboole_0(k4_xboole_0(A_95,B_96),k3_xboole_0(A_95,B_96)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1468])).

tff(c_2261,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k3_xboole_0('#skF_3',k1_xboole_0)) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_2225])).

tff(c_2295,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1856,c_2261])).

tff(c_2297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1184,c_2295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.65  
% 3.33/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.65  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.65  
% 3.33/1.65  %Foreground sorts:
% 3.33/1.65  
% 3.33/1.65  
% 3.33/1.65  %Background operators:
% 3.33/1.65  
% 3.33/1.65  
% 3.33/1.65  %Foreground operators:
% 3.33/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.65  
% 3.33/1.67  tff(f_48, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.33/1.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.33/1.67  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.33/1.67  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.33/1.67  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.33/1.67  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.33/1.67  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.33/1.67  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.33/1.67  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.67  tff(c_35, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 3.33/1.67  tff(c_40, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.67  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.67  tff(c_104, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | k3_xboole_0(A_30, B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_6])).
% 3.33/1.67  tff(c_115, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_35])).
% 3.33/1.67  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.67  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.67  tff(c_182, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.67  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.67  tff(c_185, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k3_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_12])).
% 3.33/1.67  tff(c_571, plain, (![A_48, B_49]: (k3_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_185])).
% 3.33/1.67  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.67  tff(c_36, plain, (![B_17, A_18]: (r1_xboole_0(B_17, A_18) | ~r1_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.67  tff(c_39, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_16, c_36])).
% 3.33/1.67  tff(c_53, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.67  tff(c_63, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k4_xboole_0(A_12, B_13))=k1_xboole_0)), inference(resolution, [status(thm)], [c_39, c_53])).
% 3.33/1.67  tff(c_590, plain, (![B_49]: (k4_xboole_0(B_49, B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_571, c_63])).
% 3.33/1.67  tff(c_620, plain, (![B_50]: (k4_xboole_0(B_50, B_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_571, c_63])).
% 3.33/1.67  tff(c_932, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=k3_xboole_0(B_58, B_58))), inference(superposition, [status(thm), theory('equality')], [c_620, c_12])).
% 3.33/1.67  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k4_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.67  tff(c_973, plain, (![B_58]: (k2_xboole_0(k4_xboole_0(B_58, k1_xboole_0), k4_xboole_0(B_58, B_58))=B_58)), inference(superposition, [status(thm), theory('equality')], [c_932, c_14])).
% 3.33/1.67  tff(c_1013, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_590, c_973])).
% 3.33/1.67  tff(c_643, plain, (![B_50]: (k4_xboole_0(B_50, k1_xboole_0)=k3_xboole_0(B_50, B_50))), inference(superposition, [status(thm), theory('equality')], [c_620, c_12])).
% 3.33/1.67  tff(c_1023, plain, (![B_50]: (k3_xboole_0(B_50, B_50)=B_50)), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_643])).
% 3.33/1.67  tff(c_24, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.67  tff(c_66, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 3.33/1.67  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.67  tff(c_72, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_2])).
% 3.33/1.67  tff(c_146, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.67  tff(c_179, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_146])).
% 3.33/1.67  tff(c_931, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_179])).
% 3.33/1.67  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.67  tff(c_116, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 3.33/1.67  tff(c_1090, plain, (k3_xboole_0('#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_931, c_116])).
% 3.33/1.67  tff(c_1130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1090])).
% 3.33/1.67  tff(c_1131, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 3.33/1.67  tff(c_1136, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1131, c_63])).
% 3.33/1.67  tff(c_1149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_1136])).
% 3.33/1.67  tff(c_1150, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 3.33/1.67  tff(c_1162, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1150, c_16])).
% 3.33/1.67  tff(c_1166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_1162])).
% 3.33/1.67  tff(c_1168, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 3.33/1.67  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.67  tff(c_1184, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1168, c_18])).
% 3.33/1.67  tff(c_1169, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | ~r1_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.67  tff(c_1178, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_16, c_1169])).
% 3.33/1.67  tff(c_1194, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.67  tff(c_1213, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k4_xboole_0(A_12, B_13))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1178, c_1194])).
% 3.33/1.67  tff(c_1322, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.67  tff(c_1331, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, k3_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_12])).
% 3.33/1.67  tff(c_1777, plain, (![A_84, B_85]: (k3_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1331])).
% 3.33/1.67  tff(c_1825, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k4_xboole_0(A_12, B_13))=k3_xboole_0(B_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1777])).
% 3.33/1.67  tff(c_1856, plain, (![B_13]: (k3_xboole_0(B_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_1825])).
% 3.33/1.67  tff(c_1167, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 3.33/1.67  tff(c_1217, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1167, c_1194])).
% 3.33/1.67  tff(c_1361, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1217, c_1322])).
% 3.33/1.67  tff(c_1266, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.67  tff(c_1287, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1266])).
% 3.33/1.67  tff(c_1952, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1287])).
% 3.33/1.67  tff(c_1450, plain, (![A_80, B_81]: (k2_xboole_0(k3_xboole_0(A_80, B_81), k4_xboole_0(A_80, B_81))=A_80)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.67  tff(c_1468, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)), k3_xboole_0(A_8, B_9))=A_8)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1450])).
% 3.33/1.67  tff(c_2225, plain, (![A_95, B_96]: (k2_xboole_0(k4_xboole_0(A_95, B_96), k3_xboole_0(A_95, B_96))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1468])).
% 3.33/1.67  tff(c_2261, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', k1_xboole_0))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1361, c_2225])).
% 3.33/1.67  tff(c_2295, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1856, c_2261])).
% 3.33/1.67  tff(c_2297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1184, c_2295])).
% 3.33/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.67  
% 3.33/1.67  Inference rules
% 3.33/1.67  ----------------------
% 3.33/1.67  #Ref     : 0
% 3.33/1.67  #Sup     : 613
% 3.33/1.67  #Fact    : 0
% 3.33/1.67  #Define  : 0
% 3.33/1.67  #Split   : 3
% 3.33/1.67  #Chain   : 0
% 3.33/1.67  #Close   : 0
% 3.33/1.67  
% 3.33/1.67  Ordering : KBO
% 3.33/1.67  
% 3.33/1.67  Simplification rules
% 3.33/1.67  ----------------------
% 3.33/1.67  #Subsume      : 4
% 3.33/1.67  #Demod        : 399
% 3.33/1.67  #Tautology    : 414
% 3.33/1.67  #SimpNegUnit  : 3
% 3.33/1.67  #BackRed      : 7
% 3.33/1.67  
% 3.33/1.67  #Partial instantiations: 0
% 3.33/1.67  #Strategies tried      : 1
% 3.33/1.67  
% 3.33/1.67  Timing (in seconds)
% 3.33/1.67  ----------------------
% 3.33/1.67  Preprocessing        : 0.29
% 3.33/1.67  Parsing              : 0.16
% 3.33/1.67  CNF conversion       : 0.02
% 3.33/1.67  Main loop            : 0.56
% 3.33/1.67  Inferencing          : 0.20
% 3.33/1.67  Reduction            : 0.21
% 3.33/1.67  Demodulation         : 0.16
% 3.33/1.67  BG Simplification    : 0.02
% 3.33/1.67  Subsumption          : 0.08
% 3.33/1.67  Abstraction          : 0.02
% 3.33/1.67  MUC search           : 0.00
% 3.33/1.67  Cooper               : 0.00
% 3.33/1.67  Total                : 0.89
% 3.33/1.67  Index Insertion      : 0.00
% 3.33/1.67  Index Deletion       : 0.00
% 3.33/1.67  Index Matching       : 0.00
% 3.33/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
