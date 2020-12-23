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
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 205 expanded)
%              Number of leaves         :   41 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 358 expanded)
%              Number of equality atoms :   41 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [B_76,A_77] :
      ( r1_xboole_0(B_76,A_77)
      | ~ r1_xboole_0(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    ! [A_12] : r1_xboole_0(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_20,c_175])).

tff(c_578,plain,(
    ! [B_108,A_109] :
      ( ~ r1_xboole_0(B_108,A_109)
      | ~ r1_tarski(B_108,A_109)
      | v1_xboole_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_600,plain,(
    ! [A_12] :
      ( ~ r1_tarski(k1_xboole_0,A_12)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_180,c_578])).

tff(c_612,plain,(
    ! [A_12] : ~ r1_tarski(k1_xboole_0,A_12) ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_xboole_0(k1_xboole_0,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ r2_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,(
    ! [A_11] :
      ( r1_tarski(k1_xboole_0,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_615,plain,(
    ! [A_112] : k1_xboole_0 = A_112 ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_173])).

tff(c_345,plain,(
    ! [A_96] :
      ( k1_relat_1(A_96) = k1_xboole_0
      | k2_relat_1(A_96) != k1_xboole_0
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_359,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_345])).

tff(c_360,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_557,plain,(
    ! [A_107] :
      ( k2_relat_1(A_107) = k1_xboole_0
      | k1_relat_1(A_107) != k1_xboole_0
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_569,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_557])).

tff(c_577,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_569])).

tff(c_770,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_577])).

tff(c_771,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_788,plain,(
    ! [A_2182,B_2183] :
      ( v1_xboole_0(k7_relat_1(A_2182,B_2183))
      | ~ v1_xboole_0(B_2183)
      | ~ v1_relat_1(A_2182) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_860,plain,(
    ! [A_2190,B_2191] :
      ( k7_relat_1(A_2190,B_2191) = k1_xboole_0
      | ~ v1_xboole_0(B_2191)
      | ~ v1_relat_1(A_2190) ) ),
    inference(resolution,[status(thm)],[c_788,c_24])).

tff(c_870,plain,(
    ! [A_2192] :
      ( k7_relat_1(A_2192,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_2192) ) ),
    inference(resolution,[status(thm)],[c_771,c_860])).

tff(c_886,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_870])).

tff(c_74,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_201,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = k1_xboole_0
      | ~ r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_201])).

tff(c_1083,plain,(
    ! [C_2211,A_2212,B_2213] :
      ( k7_relat_1(k7_relat_1(C_2211,A_2212),B_2213) = k7_relat_1(C_2211,k3_xboole_0(A_2212,B_2213))
      | ~ v1_relat_1(C_2211) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1105,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_72])).

tff(c_1131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_886,c_221,c_1105])).

tff(c_1133,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_58,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(k2_relat_1(A_56))
      | ~ v1_relat_1(A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1141,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_58])).

tff(c_1145,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1141])).

tff(c_1147,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1145])).

tff(c_1271,plain,(
    ! [B_2220,A_2221] :
      ( ~ r1_xboole_0(B_2220,A_2221)
      | ~ r1_tarski(B_2220,A_2221)
      | v1_xboole_0(B_2220) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1283,plain,(
    ! [A_12] :
      ( ~ r1_tarski(k1_xboole_0,A_12)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_180,c_1271])).

tff(c_1295,plain,(
    ! [A_12] : ~ r1_tarski(k1_xboole_0,A_12) ),
    inference(negUnitSimplification,[status(thm)],[c_1147,c_1283])).

tff(c_1300,plain,(
    ! [A_2223] : k1_xboole_0 = A_2223 ),
    inference(negUnitSimplification,[status(thm)],[c_1295,c_173])).

tff(c_1398,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_72])).

tff(c_1399,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1145])).

tff(c_1753,plain,(
    ! [A_3795,B_3796] :
      ( v1_xboole_0(k7_relat_1(A_3795,B_3796))
      | ~ v1_xboole_0(B_3796)
      | ~ v1_relat_1(A_3795) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1404,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1399,c_24])).

tff(c_1425,plain,(
    ! [A_15] :
      ( A_15 = '#skF_3'
      | ~ v1_xboole_0(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_24])).

tff(c_2010,plain,(
    ! [A_3824,B_3825] :
      ( k7_relat_1(A_3824,B_3825) = '#skF_3'
      | ~ v1_xboole_0(B_3825)
      | ~ v1_relat_1(A_3824) ) ),
    inference(resolution,[status(thm)],[c_1753,c_1425])).

tff(c_2020,plain,(
    ! [A_3826] :
      ( k7_relat_1(A_3826,'#skF_3') = '#skF_3'
      | ~ v1_relat_1(A_3826) ) ),
    inference(resolution,[status(thm)],[c_1399,c_2010])).

tff(c_2032,plain,(
    k7_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_2020])).

tff(c_1417,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_221])).

tff(c_2146,plain,(
    ! [C_3836,A_3837,B_3838] :
      ( k7_relat_1(k7_relat_1(C_3836,A_3837),B_3838) = k7_relat_1(C_3836,k3_xboole_0(A_3837,B_3838))
      | ~ v1_relat_1(C_3836) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1426,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_72])).

tff(c_2169,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2146,c_1426])).

tff(c_2202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2032,c_1417,c_2169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.65  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.87/1.65  
% 3.87/1.65  %Foreground sorts:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Background operators:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Foreground operators:
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.87/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.87/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.87/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.87/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.65  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.87/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.87/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.87/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.87/1.65  
% 3.87/1.66  tff(f_129, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 3.87/1.66  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.87/1.66  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.87/1.66  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.87/1.66  tff(f_49, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 3.87/1.66  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.87/1.66  tff(f_121, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.87/1.66  tff(f_100, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 3.87/1.66  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 3.87/1.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.87/1.66  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.87/1.66  tff(f_108, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.87/1.66  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.87/1.66  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.66  tff(c_175, plain, (![B_76, A_77]: (r1_xboole_0(B_76, A_77) | ~r1_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.87/1.66  tff(c_180, plain, (![A_12]: (r1_xboole_0(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_20, c_175])).
% 3.87/1.66  tff(c_578, plain, (![B_108, A_109]: (~r1_xboole_0(B_108, A_109) | ~r1_tarski(B_108, A_109) | v1_xboole_0(B_108))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.66  tff(c_600, plain, (![A_12]: (~r1_tarski(k1_xboole_0, A_12) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_578])).
% 3.87/1.66  tff(c_612, plain, (![A_12]: (~r1_tarski(k1_xboole_0, A_12))), inference(splitLeft, [status(thm)], [c_600])).
% 3.87/1.66  tff(c_18, plain, (![A_11]: (r2_xboole_0(k1_xboole_0, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.87/1.66  tff(c_169, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~r2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.87/1.66  tff(c_173, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_18, c_169])).
% 3.87/1.66  tff(c_615, plain, (![A_112]: (k1_xboole_0=A_112)), inference(negUnitSimplification, [status(thm)], [c_612, c_173])).
% 3.87/1.66  tff(c_345, plain, (![A_96]: (k1_relat_1(A_96)=k1_xboole_0 | k2_relat_1(A_96)!=k1_xboole_0 | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.66  tff(c_359, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_345])).
% 3.87/1.66  tff(c_360, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_359])).
% 3.87/1.66  tff(c_557, plain, (![A_107]: (k2_relat_1(A_107)=k1_xboole_0 | k1_relat_1(A_107)!=k1_xboole_0 | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.66  tff(c_569, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_557])).
% 3.87/1.66  tff(c_577, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_360, c_569])).
% 3.87/1.66  tff(c_770, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_615, c_577])).
% 3.87/1.66  tff(c_771, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_600])).
% 3.87/1.66  tff(c_788, plain, (![A_2182, B_2183]: (v1_xboole_0(k7_relat_1(A_2182, B_2183)) | ~v1_xboole_0(B_2183) | ~v1_relat_1(A_2182))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.87/1.66  tff(c_24, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.66  tff(c_860, plain, (![A_2190, B_2191]: (k7_relat_1(A_2190, B_2191)=k1_xboole_0 | ~v1_xboole_0(B_2191) | ~v1_relat_1(A_2190))), inference(resolution, [status(thm)], [c_788, c_24])).
% 3.87/1.66  tff(c_870, plain, (![A_2192]: (k7_relat_1(A_2192, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_2192))), inference(resolution, [status(thm)], [c_771, c_860])).
% 3.87/1.66  tff(c_886, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_870])).
% 3.87/1.66  tff(c_74, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.87/1.66  tff(c_201, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=k1_xboole_0 | ~r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.66  tff(c_221, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_201])).
% 3.87/1.66  tff(c_1083, plain, (![C_2211, A_2212, B_2213]: (k7_relat_1(k7_relat_1(C_2211, A_2212), B_2213)=k7_relat_1(C_2211, k3_xboole_0(A_2212, B_2213)) | ~v1_relat_1(C_2211))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.87/1.66  tff(c_72, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.87/1.66  tff(c_1105, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1083, c_72])).
% 3.87/1.66  tff(c_1131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_886, c_221, c_1105])).
% 3.87/1.66  tff(c_1133, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_359])).
% 3.87/1.66  tff(c_58, plain, (![A_56]: (~v1_xboole_0(k2_relat_1(A_56)) | ~v1_relat_1(A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.87/1.66  tff(c_1141, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1133, c_58])).
% 3.87/1.66  tff(c_1145, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1141])).
% 3.87/1.66  tff(c_1147, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1145])).
% 3.87/1.66  tff(c_1271, plain, (![B_2220, A_2221]: (~r1_xboole_0(B_2220, A_2221) | ~r1_tarski(B_2220, A_2221) | v1_xboole_0(B_2220))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.66  tff(c_1283, plain, (![A_12]: (~r1_tarski(k1_xboole_0, A_12) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_1271])).
% 3.87/1.66  tff(c_1295, plain, (![A_12]: (~r1_tarski(k1_xboole_0, A_12))), inference(negUnitSimplification, [status(thm)], [c_1147, c_1283])).
% 3.87/1.66  tff(c_1300, plain, (![A_2223]: (k1_xboole_0=A_2223)), inference(negUnitSimplification, [status(thm)], [c_1295, c_173])).
% 3.87/1.66  tff(c_1398, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1300, c_72])).
% 3.87/1.66  tff(c_1399, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1145])).
% 3.87/1.66  tff(c_1753, plain, (![A_3795, B_3796]: (v1_xboole_0(k7_relat_1(A_3795, B_3796)) | ~v1_xboole_0(B_3796) | ~v1_relat_1(A_3795))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.87/1.66  tff(c_1404, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1399, c_24])).
% 3.87/1.66  tff(c_1425, plain, (![A_15]: (A_15='#skF_3' | ~v1_xboole_0(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_24])).
% 3.87/1.66  tff(c_2010, plain, (![A_3824, B_3825]: (k7_relat_1(A_3824, B_3825)='#skF_3' | ~v1_xboole_0(B_3825) | ~v1_relat_1(A_3824))), inference(resolution, [status(thm)], [c_1753, c_1425])).
% 3.87/1.66  tff(c_2020, plain, (![A_3826]: (k7_relat_1(A_3826, '#skF_3')='#skF_3' | ~v1_relat_1(A_3826))), inference(resolution, [status(thm)], [c_1399, c_2010])).
% 3.87/1.66  tff(c_2032, plain, (k7_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_76, c_2020])).
% 3.87/1.66  tff(c_1417, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_221])).
% 3.87/1.66  tff(c_2146, plain, (![C_3836, A_3837, B_3838]: (k7_relat_1(k7_relat_1(C_3836, A_3837), B_3838)=k7_relat_1(C_3836, k3_xboole_0(A_3837, B_3838)) | ~v1_relat_1(C_3836))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.87/1.66  tff(c_1426, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_72])).
% 3.87/1.66  tff(c_2169, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2146, c_1426])).
% 3.87/1.66  tff(c_2202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2032, c_1417, c_2169])).
% 3.87/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.66  
% 3.87/1.66  Inference rules
% 3.87/1.66  ----------------------
% 3.87/1.66  #Ref     : 0
% 3.87/1.66  #Sup     : 549
% 3.87/1.66  #Fact    : 0
% 3.87/1.66  #Define  : 0
% 3.87/1.66  #Split   : 7
% 3.87/1.66  #Chain   : 0
% 3.87/1.66  #Close   : 0
% 3.87/1.66  
% 3.87/1.66  Ordering : KBO
% 3.87/1.66  
% 3.87/1.66  Simplification rules
% 3.87/1.66  ----------------------
% 3.87/1.66  #Subsume      : 54
% 3.87/1.66  #Demod        : 274
% 3.87/1.66  #Tautology    : 335
% 3.87/1.66  #SimpNegUnit  : 8
% 3.87/1.66  #BackRed      : 27
% 3.87/1.66  
% 3.87/1.66  #Partial instantiations: 213
% 3.87/1.66  #Strategies tried      : 1
% 3.87/1.66  
% 3.87/1.66  Timing (in seconds)
% 3.87/1.66  ----------------------
% 3.87/1.67  Preprocessing        : 0.34
% 3.87/1.67  Parsing              : 0.18
% 3.98/1.67  CNF conversion       : 0.02
% 3.98/1.67  Main loop            : 0.53
% 3.98/1.67  Inferencing          : 0.23
% 3.98/1.67  Reduction            : 0.17
% 3.98/1.67  Demodulation         : 0.12
% 3.98/1.67  BG Simplification    : 0.02
% 3.98/1.67  Subsumption          : 0.08
% 3.98/1.67  Abstraction          : 0.03
% 3.98/1.67  MUC search           : 0.00
% 3.98/1.67  Cooper               : 0.00
% 3.98/1.67  Total                : 0.91
% 3.98/1.67  Index Insertion      : 0.00
% 3.98/1.67  Index Deletion       : 0.00
% 3.98/1.67  Index Matching       : 0.00
% 3.98/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
