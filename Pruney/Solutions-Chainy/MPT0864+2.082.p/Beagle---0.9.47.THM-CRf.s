%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 222 expanded)
%              Number of leaves         :   29 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 306 expanded)
%              Number of equality atoms :   72 ( 252 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_430,plain,(
    ! [A_86,B_87] : k3_xboole_0(k1_tarski(A_86),k2_tarski(A_86,B_87)) = k1_tarski(A_86) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_436,plain,(
    ! [A_86,B_87] : k5_xboole_0(k1_tarski(A_86),k1_tarski(A_86)) = k4_xboole_0(k1_tarski(A_86),k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_2])).

tff(c_446,plain,(
    ! [A_88,B_89] : k4_xboole_0(k1_tarski(A_88),k2_tarski(A_88,B_89)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_436])).

tff(c_453,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_446])).

tff(c_14,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_456,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_14])).

tff(c_30,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_540,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(k1_tarski(A_102),k1_tarski(B_103)) = k1_tarski(A_102)
      | B_103 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [C_16,B_15] : ~ r2_hidden(C_16,k4_xboole_0(B_15,k1_tarski(C_16))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_566,plain,(
    ! [B_104,A_105] :
      ( ~ r2_hidden(B_104,k1_tarski(A_105))
      | B_104 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_20])).

tff(c_570,plain,(
    ! [A_105] :
      ( '#skF_1'(k1_tarski(A_105)) = A_105
      | k1_tarski(A_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_566])).

tff(c_573,plain,(
    ! [A_105] : '#skF_1'(k1_tarski(A_105)) = A_105 ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_570])).

tff(c_578,plain,(
    ! [A_109] : '#skF_1'(k1_tarski(A_109)) = A_109 ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_570])).

tff(c_584,plain,(
    ! [A_109] :
      ( r2_hidden(A_109,k1_tarski(A_109))
      | k1_tarski(A_109) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_30])).

tff(c_591,plain,(
    ! [A_110] : r2_hidden(A_110,k1_tarski(A_110)) ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_584])).

tff(c_32,plain,(
    ! [D_30,A_21,C_29] :
      ( ~ r2_hidden(D_30,A_21)
      | k4_tarski(C_29,D_30) != '#skF_1'(A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_593,plain,(
    ! [C_29,A_110] :
      ( k4_tarski(C_29,A_110) != '#skF_1'(k1_tarski(A_110))
      | k1_tarski(A_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_591,c_32])).

tff(c_598,plain,(
    ! [C_29,A_110] :
      ( k4_tarski(C_29,A_110) != A_110
      | k1_tarski(A_110) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_593])).

tff(c_599,plain,(
    ! [C_29,A_110] : k4_tarski(C_29,A_110) != A_110 ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_598])).

tff(c_173,plain,(
    ! [A_50,B_51] : k3_xboole_0(k1_tarski(A_50),k2_tarski(A_50,B_51)) = k1_tarski(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [A_50,B_51] : k5_xboole_0(k1_tarski(A_50),k1_tarski(A_50)) = k4_xboole_0(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_2])).

tff(c_189,plain,(
    ! [A_52,B_53] : k4_xboole_0(k1_tarski(A_52),k2_tarski(A_52,B_53)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_196,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_189])).

tff(c_199,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_14])).

tff(c_283,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k1_tarski(A_66),k1_tarski(B_67)) = k1_tarski(A_66)
      | B_67 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_309,plain,(
    ! [B_68,A_69] :
      ( ~ r2_hidden(B_68,k1_tarski(A_69))
      | B_68 = A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_20])).

tff(c_313,plain,(
    ! [A_69] :
      ( '#skF_1'(k1_tarski(A_69)) = A_69
      | k1_tarski(A_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_309])).

tff(c_316,plain,(
    ! [A_69] : '#skF_1'(k1_tarski(A_69)) = A_69 ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_313])).

tff(c_317,plain,(
    ! [A_70] : '#skF_1'(k1_tarski(A_70)) = A_70 ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_313])).

tff(c_323,plain,(
    ! [A_70] :
      ( r2_hidden(A_70,k1_tarski(A_70))
      | k1_tarski(A_70) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_30])).

tff(c_334,plain,(
    ! [A_74] : r2_hidden(A_74,k1_tarski(A_74)) ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_323])).

tff(c_34,plain,(
    ! [C_29,A_21,D_30] :
      ( ~ r2_hidden(C_29,A_21)
      | k4_tarski(C_29,D_30) != '#skF_1'(A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_336,plain,(
    ! [A_74,D_30] :
      ( k4_tarski(A_74,D_30) != '#skF_1'(k1_tarski(A_74))
      | k1_tarski(A_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_334,c_34])).

tff(c_341,plain,(
    ! [A_74,D_30] :
      ( k4_tarski(A_74,D_30) != A_74
      | k1_tarski(A_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_336])).

tff(c_342,plain,(
    ! [A_74,D_30] : k4_tarski(A_74,D_30) != A_74 ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_341])).

tff(c_38,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_75])).

tff(c_59,plain,(
    ! [A_35,B_36] : k2_mcart_1(k4_tarski(A_35,B_36)) = B_36 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_36,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_91,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_68,c_36])).

tff(c_92,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_95,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_95])).

tff(c_347,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_351,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_38])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.16/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.16/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.31  
% 2.56/1.33  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.33  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.56/1.33  tff(f_37, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.56/1.33  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/1.33  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.56/1.33  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.56/1.33  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.56/1.33  tff(f_81, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.56/1.33  tff(f_55, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.56/1.33  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.33  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.33  tff(c_430, plain, (![A_86, B_87]: (k3_xboole_0(k1_tarski(A_86), k2_tarski(A_86, B_87))=k1_tarski(A_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.33  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.33  tff(c_436, plain, (![A_86, B_87]: (k5_xboole_0(k1_tarski(A_86), k1_tarski(A_86))=k4_xboole_0(k1_tarski(A_86), k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_430, c_2])).
% 2.56/1.33  tff(c_446, plain, (![A_88, B_89]: (k4_xboole_0(k1_tarski(A_88), k2_tarski(A_88, B_89))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_436])).
% 2.56/1.33  tff(c_453, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_446])).
% 2.56/1.33  tff(c_14, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.33  tff(c_456, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_453, c_14])).
% 2.56/1.33  tff(c_30, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.33  tff(c_540, plain, (![A_102, B_103]: (k4_xboole_0(k1_tarski(A_102), k1_tarski(B_103))=k1_tarski(A_102) | B_103=A_102)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.33  tff(c_20, plain, (![C_16, B_15]: (~r2_hidden(C_16, k4_xboole_0(B_15, k1_tarski(C_16))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.33  tff(c_566, plain, (![B_104, A_105]: (~r2_hidden(B_104, k1_tarski(A_105)) | B_104=A_105)), inference(superposition, [status(thm), theory('equality')], [c_540, c_20])).
% 2.56/1.33  tff(c_570, plain, (![A_105]: ('#skF_1'(k1_tarski(A_105))=A_105 | k1_tarski(A_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_566])).
% 2.56/1.33  tff(c_573, plain, (![A_105]: ('#skF_1'(k1_tarski(A_105))=A_105)), inference(negUnitSimplification, [status(thm)], [c_456, c_570])).
% 2.56/1.33  tff(c_578, plain, (![A_109]: ('#skF_1'(k1_tarski(A_109))=A_109)), inference(negUnitSimplification, [status(thm)], [c_456, c_570])).
% 2.56/1.33  tff(c_584, plain, (![A_109]: (r2_hidden(A_109, k1_tarski(A_109)) | k1_tarski(A_109)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_578, c_30])).
% 2.56/1.33  tff(c_591, plain, (![A_110]: (r2_hidden(A_110, k1_tarski(A_110)))), inference(negUnitSimplification, [status(thm)], [c_456, c_584])).
% 2.56/1.33  tff(c_32, plain, (![D_30, A_21, C_29]: (~r2_hidden(D_30, A_21) | k4_tarski(C_29, D_30)!='#skF_1'(A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.33  tff(c_593, plain, (![C_29, A_110]: (k4_tarski(C_29, A_110)!='#skF_1'(k1_tarski(A_110)) | k1_tarski(A_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_591, c_32])).
% 2.56/1.33  tff(c_598, plain, (![C_29, A_110]: (k4_tarski(C_29, A_110)!=A_110 | k1_tarski(A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_573, c_593])).
% 2.56/1.33  tff(c_599, plain, (![C_29, A_110]: (k4_tarski(C_29, A_110)!=A_110)), inference(negUnitSimplification, [status(thm)], [c_456, c_598])).
% 2.56/1.33  tff(c_173, plain, (![A_50, B_51]: (k3_xboole_0(k1_tarski(A_50), k2_tarski(A_50, B_51))=k1_tarski(A_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.33  tff(c_179, plain, (![A_50, B_51]: (k5_xboole_0(k1_tarski(A_50), k1_tarski(A_50))=k4_xboole_0(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_2])).
% 2.56/1.33  tff(c_189, plain, (![A_52, B_53]: (k4_xboole_0(k1_tarski(A_52), k2_tarski(A_52, B_53))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 2.56/1.33  tff(c_196, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_189])).
% 2.56/1.33  tff(c_199, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_14])).
% 2.56/1.33  tff(c_283, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), k1_tarski(B_67))=k1_tarski(A_66) | B_67=A_66)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.33  tff(c_309, plain, (![B_68, A_69]: (~r2_hidden(B_68, k1_tarski(A_69)) | B_68=A_69)), inference(superposition, [status(thm), theory('equality')], [c_283, c_20])).
% 2.56/1.33  tff(c_313, plain, (![A_69]: ('#skF_1'(k1_tarski(A_69))=A_69 | k1_tarski(A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_309])).
% 2.56/1.33  tff(c_316, plain, (![A_69]: ('#skF_1'(k1_tarski(A_69))=A_69)), inference(negUnitSimplification, [status(thm)], [c_199, c_313])).
% 2.56/1.33  tff(c_317, plain, (![A_70]: ('#skF_1'(k1_tarski(A_70))=A_70)), inference(negUnitSimplification, [status(thm)], [c_199, c_313])).
% 2.56/1.33  tff(c_323, plain, (![A_70]: (r2_hidden(A_70, k1_tarski(A_70)) | k1_tarski(A_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_317, c_30])).
% 2.56/1.33  tff(c_334, plain, (![A_74]: (r2_hidden(A_74, k1_tarski(A_74)))), inference(negUnitSimplification, [status(thm)], [c_199, c_323])).
% 2.56/1.33  tff(c_34, plain, (![C_29, A_21, D_30]: (~r2_hidden(C_29, A_21) | k4_tarski(C_29, D_30)!='#skF_1'(A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.33  tff(c_336, plain, (![A_74, D_30]: (k4_tarski(A_74, D_30)!='#skF_1'(k1_tarski(A_74)) | k1_tarski(A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_334, c_34])).
% 2.56/1.33  tff(c_341, plain, (![A_74, D_30]: (k4_tarski(A_74, D_30)!=A_74 | k1_tarski(A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_316, c_336])).
% 2.56/1.33  tff(c_342, plain, (![A_74, D_30]: (k4_tarski(A_74, D_30)!=A_74)), inference(negUnitSimplification, [status(thm)], [c_199, c_341])).
% 2.56/1.33  tff(c_38, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_75, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.33  tff(c_84, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_38, c_75])).
% 2.56/1.33  tff(c_59, plain, (![A_35, B_36]: (k2_mcart_1(k4_tarski(A_35, B_36))=B_36)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.56/1.33  tff(c_68, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_38, c_59])).
% 2.56/1.33  tff(c_36, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_91, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_68, c_36])).
% 2.56/1.33  tff(c_92, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_91])).
% 2.56/1.33  tff(c_95, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38])).
% 2.56/1.33  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_95])).
% 2.56/1.33  tff(c_347, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_91])).
% 2.56/1.33  tff(c_351, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_38])).
% 2.56/1.33  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_599, c_351])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 138
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 1
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 2
% 2.56/1.33  #Demod        : 31
% 2.56/1.33  #Tautology    : 108
% 2.56/1.33  #SimpNegUnit  : 12
% 2.56/1.33  #BackRed      : 10
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.31
% 2.56/1.33  Parsing              : 0.17
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.26
% 2.56/1.33  Inferencing          : 0.11
% 2.56/1.33  Reduction            : 0.08
% 2.56/1.33  Demodulation         : 0.06
% 2.56/1.33  BG Simplification    : 0.02
% 2.56/1.33  Subsumption          : 0.03
% 2.56/1.33  Abstraction          : 0.02
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.61
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
