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
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 382 expanded)
%              Number of leaves         :   27 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 426 expanded)
%              Number of equality atoms :   59 ( 373 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_28,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_392,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_122,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_140,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_411,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,k4_xboole_0(A_60,B_61))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_140])).

tff(c_458,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k2_xboole_0(B_64,A_63)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_411])).

tff(c_507,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_458])).

tff(c_890,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(B_79,k1_xboole_0)) = k4_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_20])).

tff(c_1307,plain,(
    ! [B_86] : k4_xboole_0(k2_xboole_0(B_86,k1_xboole_0),B_86) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_890])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | k4_xboole_0(B_14,A_13) != k4_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1326,plain,(
    ! [B_86] :
      ( k2_xboole_0(B_86,k1_xboole_0) = B_86
      | k4_xboole_0(B_86,k2_xboole_0(B_86,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_16])).

tff(c_1367,plain,(
    ! [B_86] : k2_xboole_0(B_86,k1_xboole_0) = B_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_1326])).

tff(c_452,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,A_60)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_411])).

tff(c_2378,plain,(
    ! [C_109,A_110,B_111] : k2_xboole_0(C_109,k4_xboole_0(A_110,k2_xboole_0(B_111,C_109))) = k2_xboole_0(C_109,k4_xboole_0(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_18])).

tff(c_2471,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k2_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_2378])).

tff(c_2511,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1367,c_2471])).

tff(c_30,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_213,plain,(
    ! [A_48,B_49] :
      ( ~ r1_xboole_0(A_48,B_49)
      | v1_xboole_0(k3_xboole_0(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_90,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_229,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_213,c_93])).

tff(c_236,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_229])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_238,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_250,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(k4_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_238])).

tff(c_2168,plain,(
    ! [A_107,B_108] : k2_xboole_0(k4_xboole_0(A_107,B_108),k3_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,k4_xboole_0(A_107,B_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_250])).

tff(c_2258,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5','#skF_4'),k1_xboole_0) = k2_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2168])).

tff(c_2301,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_4')) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1367,c_2258])).

tff(c_3227,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2301])).

tff(c_34,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_35,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_34])).

tff(c_501,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_458])).

tff(c_2465,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_2378])).

tff(c_2509,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1367,c_2465])).

tff(c_3228,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3227,c_2509])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_237,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_229])).

tff(c_2255,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2168])).

tff(c_2300,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1367,c_2255])).

tff(c_2514,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2300])).

tff(c_2683,plain,(
    ! [A_114] : k2_xboole_0('#skF_5',k4_xboole_0(A_114,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_5',k4_xboole_0(A_114,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_2378])).

tff(c_2743,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_2683])).

tff(c_2763,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2514,c_1367,c_2743])).

tff(c_3269,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3228,c_2763])).

tff(c_3271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:34:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.95/1.70  
% 3.95/1.70  %Foreground sorts:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Background operators:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Foreground operators:
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.95/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.95/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.70  
% 3.95/1.72  tff(f_79, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.95/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.95/1.72  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.95/1.72  tff(f_60, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.95/1.72  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.95/1.72  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.95/1.72  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.95/1.72  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 3.95/1.72  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.95/1.72  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.95/1.72  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.72  tff(f_70, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.95/1.72  tff(c_28, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.72  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.72  tff(c_392, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.95/1.72  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.95/1.72  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.95/1.72  tff(c_122, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.72  tff(c_137, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_122])).
% 3.95/1.72  tff(c_140, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_137])).
% 3.95/1.72  tff(c_411, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, k4_xboole_0(A_60, B_61)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_392, c_140])).
% 3.95/1.72  tff(c_458, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k2_xboole_0(B_64, A_63))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_411])).
% 3.95/1.72  tff(c_507, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_458])).
% 3.95/1.72  tff(c_890, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(B_79, k1_xboole_0))=k4_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_392, c_20])).
% 3.95/1.72  tff(c_1307, plain, (![B_86]: (k4_xboole_0(k2_xboole_0(B_86, k1_xboole_0), B_86)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_890])).
% 3.95/1.72  tff(c_16, plain, (![B_14, A_13]: (B_14=A_13 | k4_xboole_0(B_14, A_13)!=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.95/1.72  tff(c_1326, plain, (![B_86]: (k2_xboole_0(B_86, k1_xboole_0)=B_86 | k4_xboole_0(B_86, k2_xboole_0(B_86, k1_xboole_0))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1307, c_16])).
% 3.95/1.72  tff(c_1367, plain, (![B_86]: (k2_xboole_0(B_86, k1_xboole_0)=B_86)), inference(demodulation, [status(thm), theory('equality')], [c_507, c_1326])).
% 3.95/1.72  tff(c_452, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, A_60))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_411])).
% 3.95/1.72  tff(c_2378, plain, (![C_109, A_110, B_111]: (k2_xboole_0(C_109, k4_xboole_0(A_110, k2_xboole_0(B_111, C_109)))=k2_xboole_0(C_109, k4_xboole_0(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_18])).
% 3.95/1.72  tff(c_2471, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k2_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_452, c_2378])).
% 3.95/1.72  tff(c_2511, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(A_60, B_61))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_1367, c_2471])).
% 3.95/1.72  tff(c_30, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.72  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.72  tff(c_105, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.95/1.72  tff(c_213, plain, (![A_48, B_49]: (~r1_xboole_0(A_48, B_49) | v1_xboole_0(k3_xboole_0(A_48, B_49)))), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.95/1.72  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.95/1.72  tff(c_90, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.72  tff(c_93, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_8, c_90])).
% 3.95/1.72  tff(c_229, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(resolution, [status(thm)], [c_213, c_93])).
% 3.95/1.72  tff(c_236, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_229])).
% 3.95/1.72  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.72  tff(c_238, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.72  tff(c_250, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(k4_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_238])).
% 3.95/1.72  tff(c_2168, plain, (![A_107, B_108]: (k2_xboole_0(k4_xboole_0(A_107, B_108), k3_xboole_0(A_107, B_108))=k2_xboole_0(A_107, k4_xboole_0(A_107, B_108)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_250])).
% 3.95/1.72  tff(c_2258, plain, (k2_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), k1_xboole_0)=k2_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_2168])).
% 3.95/1.72  tff(c_2301, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_4'))=k4_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1367, c_2258])).
% 3.95/1.72  tff(c_3227, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2301])).
% 3.95/1.72  tff(c_34, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.72  tff(c_35, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_34])).
% 3.95/1.72  tff(c_501, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35, c_458])).
% 3.95/1.72  tff(c_2465, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_501, c_2378])).
% 3.95/1.72  tff(c_2509, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1367, c_2465])).
% 3.95/1.72  tff(c_3228, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3227, c_2509])).
% 3.95/1.72  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.72  tff(c_237, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_229])).
% 3.95/1.72  tff(c_2255, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_2168])).
% 3.95/1.72  tff(c_2300, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1367, c_2255])).
% 3.95/1.72  tff(c_2514, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2300])).
% 3.95/1.72  tff(c_2683, plain, (![A_114]: (k2_xboole_0('#skF_5', k4_xboole_0(A_114, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_5', k4_xboole_0(A_114, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_35, c_2378])).
% 3.95/1.72  tff(c_2743, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_452, c_2683])).
% 3.95/1.72  tff(c_2763, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2514, c_1367, c_2743])).
% 3.95/1.72  tff(c_3269, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3228, c_2763])).
% 3.95/1.72  tff(c_3271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_3269])).
% 3.95/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  Inference rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Ref     : 1
% 3.95/1.72  #Sup     : 806
% 3.95/1.72  #Fact    : 0
% 3.95/1.72  #Define  : 0
% 3.95/1.72  #Split   : 3
% 3.95/1.72  #Chain   : 0
% 3.95/1.72  #Close   : 0
% 3.95/1.72  
% 3.95/1.72  Ordering : KBO
% 3.95/1.72  
% 3.95/1.72  Simplification rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Subsume      : 71
% 3.95/1.72  #Demod        : 632
% 3.95/1.72  #Tautology    : 495
% 3.95/1.72  #SimpNegUnit  : 21
% 3.95/1.72  #BackRed      : 13
% 3.95/1.72  
% 3.95/1.72  #Partial instantiations: 0
% 3.95/1.72  #Strategies tried      : 1
% 3.95/1.72  
% 3.95/1.72  Timing (in seconds)
% 3.95/1.72  ----------------------
% 3.95/1.72  Preprocessing        : 0.29
% 3.95/1.72  Parsing              : 0.16
% 3.95/1.72  CNF conversion       : 0.02
% 3.95/1.72  Main loop            : 0.65
% 3.95/1.72  Inferencing          : 0.21
% 3.95/1.72  Reduction            : 0.28
% 3.95/1.72  Demodulation         : 0.23
% 3.95/1.72  BG Simplification    : 0.03
% 3.95/1.72  Subsumption          : 0.09
% 3.95/1.72  Abstraction          : 0.03
% 3.95/1.72  MUC search           : 0.00
% 3.95/1.72  Cooper               : 0.00
% 3.95/1.72  Total                : 0.99
% 3.95/1.72  Index Insertion      : 0.00
% 3.95/1.72  Index Deletion       : 0.00
% 3.95/1.72  Index Matching       : 0.00
% 3.95/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
