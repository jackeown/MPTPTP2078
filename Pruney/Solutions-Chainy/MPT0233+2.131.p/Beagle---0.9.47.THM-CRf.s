%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 227 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 467 expanded)
%              Number of equality atoms :   83 ( 322 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_58,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_319,plain,(
    ! [B_104,C_105,A_106] :
      ( k2_tarski(B_104,C_105) = A_106
      | k1_tarski(C_105) = A_106
      | k1_tarski(B_104) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k2_tarski(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_341,plain,
    ( k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_319])).

tff(c_377,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_48,plain,(
    ! [A_22,B_23] : r1_tarski(k1_tarski(A_22),k2_tarski(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | k4_xboole_0(A_70,B_69) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_165])).

tff(c_220,plain,(
    ! [A_22,B_23] :
      ( k2_tarski(A_22,B_23) = k1_tarski(A_22)
      | k4_xboole_0(k2_tarski(A_22,B_23),k1_tarski(A_22)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_198])).

tff(c_396,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3')
    | k4_xboole_0(k1_xboole_0,k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_220])).

tff(c_448,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_377,c_396])).

tff(c_231,plain,(
    ! [C_73,A_74,B_75] :
      ( C_73 = A_74
      | B_75 = A_74
      | ~ r1_tarski(k1_tarski(A_74),k2_tarski(B_75,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_241,plain,(
    ! [C_73,A_74,B_75] :
      ( C_73 = A_74
      | B_75 = A_74
      | k4_xboole_0(k1_tarski(A_74),k2_tarski(B_75,C_73)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_513,plain,(
    ! [C_73,B_75] :
      ( C_73 = '#skF_3'
      | B_75 = '#skF_3'
      | k4_xboole_0(k1_xboole_0,k2_tarski(B_75,C_73)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_241])).

tff(c_538,plain,(
    ! [C_73,B_75] :
      ( C_73 = '#skF_3'
      | B_75 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_513])).

tff(c_1284,plain,(
    ! [B_1226] : B_1226 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_1427,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_56])).

tff(c_1429,plain,(
    ! [C_2352] : C_2352 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_1572,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_56])).

tff(c_1573,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_1575,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1573])).

tff(c_179,plain,
    ( k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4')
    | ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_288,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_292,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_288])).

tff(c_1576,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1575,c_292])).

tff(c_1582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1576])).

tff(c_1583,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1573])).

tff(c_2459,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1583])).

tff(c_52,plain,(
    ! [B_28,A_27,C_29] :
      ( B_28 = A_27
      | k2_tarski(B_28,C_29) != k1_tarski(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2510,plain,(
    ! [A_27] :
      ( A_27 = '#skF_3'
      | k1_tarski(A_27) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_52])).

tff(c_3544,plain,(
    '#skF_5' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2510])).

tff(c_3546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3544])).

tff(c_3547,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1583])).

tff(c_3605,plain,(
    ! [A_27] :
      ( A_27 = '#skF_3'
      | k1_tarski(A_27) != k1_tarski('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3547,c_52])).

tff(c_4628,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3605])).

tff(c_4630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4628])).

tff(c_4631,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_20,plain,(
    ! [D_13,B_9] : r2_hidden(D_13,k2_tarski(D_13,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4668,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4631,c_20])).

tff(c_16,plain,(
    ! [D_13,B_9,A_8] :
      ( D_13 = B_9
      | D_13 = A_8
      | ~ r2_hidden(D_13,k2_tarski(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4681,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4668,c_16])).

tff(c_4684,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4681])).

tff(c_4687,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4684,c_58])).

tff(c_18,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4671,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4631,c_18])).

tff(c_4695,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4671,c_16])).

tff(c_4698,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4695])).

tff(c_4686,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4684,c_4631])).

tff(c_4721,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4698,c_4686])).

tff(c_4754,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4721,c_20])).

tff(c_4772,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4754,c_16])).

tff(c_4776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4687,c_4687,c_4772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.89  
% 4.87/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.89  %$ r2_hidden > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.87/1.89  
% 4.87/1.89  %Foreground sorts:
% 4.87/1.89  
% 4.87/1.89  
% 4.87/1.89  %Background operators:
% 4.87/1.89  
% 4.87/1.89  
% 4.87/1.89  %Foreground operators:
% 4.87/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.87/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.87/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.87/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.87/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.87/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.87/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.87/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.87/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.87/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.87/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.87/1.89  
% 4.87/1.90  tff(f_96, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.87/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.87/1.90  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.87/1.90  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.87/1.90  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.87/1.90  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 4.87/1.90  tff(f_78, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.87/1.90  tff(f_82, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 4.87/1.90  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.87/1.90  tff(c_58, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.87/1.90  tff(c_56, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.87/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.90  tff(c_77, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.87/1.90  tff(c_98, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_77])).
% 4.87/1.90  tff(c_14, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.87/1.90  tff(c_60, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.87/1.90  tff(c_319, plain, (![B_104, C_105, A_106]: (k2_tarski(B_104, C_105)=A_106 | k1_tarski(C_105)=A_106 | k1_tarski(B_104)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k2_tarski(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/1.90  tff(c_341, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_319])).
% 4.87/1.90  tff(c_377, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_341])).
% 4.87/1.90  tff(c_48, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), k2_tarski(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.87/1.90  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.87/1.90  tff(c_165, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.90  tff(c_198, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | k4_xboole_0(A_70, B_69)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_165])).
% 4.87/1.90  tff(c_220, plain, (![A_22, B_23]: (k2_tarski(A_22, B_23)=k1_tarski(A_22) | k4_xboole_0(k2_tarski(A_22, B_23), k1_tarski(A_22))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_198])).
% 4.87/1.90  tff(c_396, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3') | k4_xboole_0(k1_xboole_0, k1_tarski('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_377, c_220])).
% 4.87/1.90  tff(c_448, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_377, c_396])).
% 4.87/1.90  tff(c_231, plain, (![C_73, A_74, B_75]: (C_73=A_74 | B_75=A_74 | ~r1_tarski(k1_tarski(A_74), k2_tarski(B_75, C_73)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/1.90  tff(c_241, plain, (![C_73, A_74, B_75]: (C_73=A_74 | B_75=A_74 | k4_xboole_0(k1_tarski(A_74), k2_tarski(B_75, C_73))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_231])).
% 4.87/1.90  tff(c_513, plain, (![C_73, B_75]: (C_73='#skF_3' | B_75='#skF_3' | k4_xboole_0(k1_xboole_0, k2_tarski(B_75, C_73))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_448, c_241])).
% 4.87/1.90  tff(c_538, plain, (![C_73, B_75]: (C_73='#skF_3' | B_75='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_513])).
% 4.87/1.90  tff(c_1284, plain, (![B_1226]: (B_1226='#skF_3')), inference(splitLeft, [status(thm)], [c_538])).
% 4.87/1.90  tff(c_1427, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1284, c_56])).
% 4.87/1.90  tff(c_1429, plain, (![C_2352]: (C_2352='#skF_3')), inference(splitRight, [status(thm)], [c_538])).
% 4.87/1.90  tff(c_1572, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1429, c_56])).
% 4.87/1.90  tff(c_1573, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_341])).
% 4.87/1.90  tff(c_1575, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1573])).
% 4.87/1.90  tff(c_179, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4') | ~r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_165])).
% 4.87/1.90  tff(c_288, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_179])).
% 4.87/1.90  tff(c_292, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_288])).
% 4.87/1.90  tff(c_1576, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1575, c_292])).
% 4.87/1.90  tff(c_1582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_1576])).
% 4.87/1.90  tff(c_1583, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_1573])).
% 4.87/1.90  tff(c_2459, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_1583])).
% 4.87/1.90  tff(c_52, plain, (![B_28, A_27, C_29]: (B_28=A_27 | k2_tarski(B_28, C_29)!=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.87/1.90  tff(c_2510, plain, (![A_27]: (A_27='#skF_3' | k1_tarski(A_27)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2459, c_52])).
% 4.87/1.90  tff(c_3544, plain, ('#skF_5'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_2510])).
% 4.87/1.90  tff(c_3546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3544])).
% 4.87/1.90  tff(c_3547, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1583])).
% 4.87/1.90  tff(c_3605, plain, (![A_27]: (A_27='#skF_3' | k1_tarski(A_27)!=k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3547, c_52])).
% 4.87/1.90  tff(c_4628, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_3605])).
% 4.87/1.90  tff(c_4630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_4628])).
% 4.87/1.90  tff(c_4631, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 4.87/1.90  tff(c_20, plain, (![D_13, B_9]: (r2_hidden(D_13, k2_tarski(D_13, B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.87/1.90  tff(c_4668, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4631, c_20])).
% 4.87/1.90  tff(c_16, plain, (![D_13, B_9, A_8]: (D_13=B_9 | D_13=A_8 | ~r2_hidden(D_13, k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.87/1.90  tff(c_4681, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_4668, c_16])).
% 4.87/1.90  tff(c_4684, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_4681])).
% 4.87/1.90  tff(c_4687, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4684, c_58])).
% 4.87/1.90  tff(c_18, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.87/1.90  tff(c_4671, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4631, c_18])).
% 4.87/1.90  tff(c_4695, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_4671, c_16])).
% 4.87/1.90  tff(c_4698, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_4695])).
% 4.87/1.90  tff(c_4686, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4684, c_4631])).
% 4.87/1.90  tff(c_4721, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4698, c_4686])).
% 4.87/1.90  tff(c_4754, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4721, c_20])).
% 4.87/1.90  tff(c_4772, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4754, c_16])).
% 4.87/1.90  tff(c_4776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4687, c_4687, c_4772])).
% 4.87/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.90  
% 4.87/1.90  Inference rules
% 4.87/1.90  ----------------------
% 4.87/1.90  #Ref     : 2
% 4.87/1.90  #Sup     : 738
% 4.87/1.90  #Fact    : 8
% 4.87/1.90  #Define  : 0
% 4.87/1.90  #Split   : 10
% 4.87/1.90  #Chain   : 0
% 4.87/1.90  #Close   : 0
% 4.87/1.90  
% 4.87/1.90  Ordering : KBO
% 4.87/1.90  
% 4.87/1.90  Simplification rules
% 4.87/1.90  ----------------------
% 4.87/1.90  #Subsume      : 72
% 4.87/1.90  #Demod        : 128
% 4.87/1.90  #Tautology    : 132
% 4.87/1.90  #SimpNegUnit  : 12
% 4.87/1.90  #BackRed      : 29
% 4.87/1.90  
% 4.87/1.90  #Partial instantiations: 3308
% 4.87/1.90  #Strategies tried      : 1
% 4.87/1.90  
% 4.87/1.90  Timing (in seconds)
% 4.87/1.90  ----------------------
% 4.87/1.91  Preprocessing        : 0.31
% 4.87/1.91  Parsing              : 0.16
% 4.87/1.91  CNF conversion       : 0.02
% 4.87/1.91  Main loop            : 0.82
% 4.87/1.91  Inferencing          : 0.40
% 4.87/1.91  Reduction            : 0.18
% 4.87/1.91  Demodulation         : 0.13
% 4.87/1.91  BG Simplification    : 0.04
% 4.87/1.91  Subsumption          : 0.15
% 4.87/1.91  Abstraction          : 0.04
% 4.87/1.91  MUC search           : 0.00
% 4.87/1.91  Cooper               : 0.00
% 4.87/1.91  Total                : 1.16
% 4.87/1.91  Index Insertion      : 0.00
% 4.87/1.91  Index Deletion       : 0.00
% 4.87/1.91  Index Matching       : 0.00
% 4.87/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
