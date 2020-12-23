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
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 170 expanded)
%              Number of leaves         :   38 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 208 expanded)
%              Number of equality atoms :   70 ( 182 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_586,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k3_xboole_0(A_127,B_128)) = k4_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_601,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_586])).

tff(c_605,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_601])).

tff(c_20,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_606,plain,(
    ! [A_129,B_130] : k3_xboole_0(k1_tarski(A_129),k2_tarski(A_129,B_130)) = k1_tarski(A_129) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_629,plain,(
    ! [A_132] : k3_xboole_0(k1_tarski(A_132),k1_tarski(A_132)) = k1_tarski(A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_606])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_635,plain,(
    ! [A_132] : k5_xboole_0(k1_tarski(A_132),k1_tarski(A_132)) = k4_xboole_0(k1_tarski(A_132),k1_tarski(A_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_2])).

tff(c_646,plain,(
    ! [A_132] : k4_xboole_0(k1_tarski(A_132),k1_tarski(A_132)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_635])).

tff(c_38,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(B_45),k1_tarski(B_45)) != k1_tarski(B_45) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_648,plain,(
    ! [B_45] : k1_tarski(B_45) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_38])).

tff(c_109,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_3'(A_70),A_70)
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [A_7] :
      ( '#skF_3'(k1_tarski(A_7)) = A_7
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_656,plain,(
    ! [A_7] : '#skF_3'(k1_tarski(A_7)) = A_7 ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_114])).

tff(c_10,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_742,plain,(
    ! [D_148,A_149,C_150] :
      ( ~ r2_hidden(D_148,A_149)
      | k4_tarski(C_150,D_148) != '#skF_3'(A_149)
      | k1_xboole_0 = A_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_746,plain,(
    ! [C_150,C_11] :
      ( k4_tarski(C_150,C_11) != '#skF_3'(k1_tarski(C_11))
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_742])).

tff(c_749,plain,(
    ! [C_150,C_11] :
      ( k4_tarski(C_150,C_11) != C_11
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_746])).

tff(c_750,plain,(
    ! [C_150,C_11] : k4_tarski(C_150,C_11) != C_11 ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_749])).

tff(c_279,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_297,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_279])).

tff(c_301,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_297])).

tff(c_267,plain,(
    ! [A_87,B_88] : k3_xboole_0(k1_tarski(A_87),k2_tarski(A_87,B_88)) = k1_tarski(A_87) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_310,plain,(
    ! [A_92] : k3_xboole_0(k1_tarski(A_92),k1_tarski(A_92)) = k1_tarski(A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_267])).

tff(c_316,plain,(
    ! [A_92] : k5_xboole_0(k1_tarski(A_92),k1_tarski(A_92)) = k4_xboole_0(k1_tarski(A_92),k1_tarski(A_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_2])).

tff(c_327,plain,(
    ! [A_92] : k4_xboole_0(k1_tarski(A_92),k1_tarski(A_92)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_316])).

tff(c_338,plain,(
    ! [B_45] : k1_tarski(B_45) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_38])).

tff(c_346,plain,(
    ! [A_7] : '#skF_3'(k1_tarski(A_7)) = A_7 ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_114])).

tff(c_423,plain,(
    ! [C_108,A_109,D_110] :
      ( ~ r2_hidden(C_108,A_109)
      | k4_tarski(C_108,D_110) != '#skF_3'(A_109)
      | k1_xboole_0 = A_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_427,plain,(
    ! [C_11,D_110] :
      ( k4_tarski(C_11,D_110) != '#skF_3'(k1_tarski(C_11))
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_423])).

tff(c_430,plain,(
    ! [C_11,D_110] :
      ( k4_tarski(C_11,D_110) != C_11
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_427])).

tff(c_431,plain,(
    ! [C_11,D_110] : k4_tarski(C_11,D_110) != C_11 ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_430])).

tff(c_56,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_87,plain,(
    ! [A_66,B_67] : k1_mcart_1(k4_tarski(A_66,B_67)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_87])).

tff(c_71,plain,(
    ! [A_64,B_65] : k2_mcart_1(k4_tarski(A_64,B_65)) = B_65 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_71])).

tff(c_54,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_115,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80,c_54])).

tff(c_116,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_118,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_118])).

tff(c_434,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_437,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_56])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_750,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.58/1.34  
% 2.58/1.34  %Foreground sorts:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Background operators:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Foreground operators:
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.58/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.58/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.58/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.34  
% 2.58/1.35  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.58/1.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.58/1.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.58/1.35  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.58/1.35  tff(f_56, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.58/1.35  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.58/1.35  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.58/1.35  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.58/1.35  tff(f_93, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.58/1.35  tff(f_67, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.58/1.35  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.35  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.35  tff(c_586, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k3_xboole_0(A_127, B_128))=k4_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.35  tff(c_601, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_586])).
% 2.58/1.35  tff(c_605, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_601])).
% 2.58/1.35  tff(c_20, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.35  tff(c_606, plain, (![A_129, B_130]: (k3_xboole_0(k1_tarski(A_129), k2_tarski(A_129, B_130))=k1_tarski(A_129))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.35  tff(c_629, plain, (![A_132]: (k3_xboole_0(k1_tarski(A_132), k1_tarski(A_132))=k1_tarski(A_132))), inference(superposition, [status(thm), theory('equality')], [c_20, c_606])).
% 2.58/1.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.35  tff(c_635, plain, (![A_132]: (k5_xboole_0(k1_tarski(A_132), k1_tarski(A_132))=k4_xboole_0(k1_tarski(A_132), k1_tarski(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_629, c_2])).
% 2.58/1.35  tff(c_646, plain, (![A_132]: (k4_xboole_0(k1_tarski(A_132), k1_tarski(A_132))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_605, c_635])).
% 2.58/1.35  tff(c_38, plain, (![B_45]: (k4_xboole_0(k1_tarski(B_45), k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.35  tff(c_648, plain, (![B_45]: (k1_tarski(B_45)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_38])).
% 2.58/1.35  tff(c_109, plain, (![A_70]: (r2_hidden('#skF_3'(A_70), A_70) | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.58/1.35  tff(c_8, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.35  tff(c_114, plain, (![A_7]: ('#skF_3'(k1_tarski(A_7))=A_7 | k1_tarski(A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_8])).
% 2.58/1.35  tff(c_656, plain, (![A_7]: ('#skF_3'(k1_tarski(A_7))=A_7)), inference(negUnitSimplification, [status(thm)], [c_648, c_114])).
% 2.58/1.35  tff(c_10, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.35  tff(c_742, plain, (![D_148, A_149, C_150]: (~r2_hidden(D_148, A_149) | k4_tarski(C_150, D_148)!='#skF_3'(A_149) | k1_xboole_0=A_149)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.58/1.35  tff(c_746, plain, (![C_150, C_11]: (k4_tarski(C_150, C_11)!='#skF_3'(k1_tarski(C_11)) | k1_tarski(C_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_742])).
% 2.58/1.35  tff(c_749, plain, (![C_150, C_11]: (k4_tarski(C_150, C_11)!=C_11 | k1_tarski(C_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_656, c_746])).
% 2.58/1.35  tff(c_750, plain, (![C_150, C_11]: (k4_tarski(C_150, C_11)!=C_11)), inference(negUnitSimplification, [status(thm)], [c_648, c_749])).
% 2.58/1.35  tff(c_279, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.35  tff(c_297, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_279])).
% 2.58/1.35  tff(c_301, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_297])).
% 2.58/1.35  tff(c_267, plain, (![A_87, B_88]: (k3_xboole_0(k1_tarski(A_87), k2_tarski(A_87, B_88))=k1_tarski(A_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.35  tff(c_310, plain, (![A_92]: (k3_xboole_0(k1_tarski(A_92), k1_tarski(A_92))=k1_tarski(A_92))), inference(superposition, [status(thm), theory('equality')], [c_20, c_267])).
% 2.58/1.35  tff(c_316, plain, (![A_92]: (k5_xboole_0(k1_tarski(A_92), k1_tarski(A_92))=k4_xboole_0(k1_tarski(A_92), k1_tarski(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_2])).
% 2.58/1.35  tff(c_327, plain, (![A_92]: (k4_xboole_0(k1_tarski(A_92), k1_tarski(A_92))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_316])).
% 2.58/1.35  tff(c_338, plain, (![B_45]: (k1_tarski(B_45)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_38])).
% 2.58/1.35  tff(c_346, plain, (![A_7]: ('#skF_3'(k1_tarski(A_7))=A_7)), inference(negUnitSimplification, [status(thm)], [c_338, c_114])).
% 2.58/1.35  tff(c_423, plain, (![C_108, A_109, D_110]: (~r2_hidden(C_108, A_109) | k4_tarski(C_108, D_110)!='#skF_3'(A_109) | k1_xboole_0=A_109)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.58/1.35  tff(c_427, plain, (![C_11, D_110]: (k4_tarski(C_11, D_110)!='#skF_3'(k1_tarski(C_11)) | k1_tarski(C_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_423])).
% 2.58/1.35  tff(c_430, plain, (![C_11, D_110]: (k4_tarski(C_11, D_110)!=C_11 | k1_tarski(C_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_427])).
% 2.58/1.35  tff(c_431, plain, (![C_11, D_110]: (k4_tarski(C_11, D_110)!=C_11)), inference(negUnitSimplification, [status(thm)], [c_338, c_430])).
% 2.58/1.35  tff(c_56, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.35  tff(c_87, plain, (![A_66, B_67]: (k1_mcart_1(k4_tarski(A_66, B_67))=A_66)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.35  tff(c_96, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_56, c_87])).
% 2.58/1.35  tff(c_71, plain, (![A_64, B_65]: (k2_mcart_1(k4_tarski(A_64, B_65))=B_65)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.35  tff(c_80, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_56, c_71])).
% 2.58/1.35  tff(c_54, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.35  tff(c_115, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_80, c_54])).
% 2.58/1.35  tff(c_116, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_115])).
% 2.58/1.35  tff(c_118, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_56])).
% 2.58/1.35  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_118])).
% 2.58/1.35  tff(c_434, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 2.58/1.35  tff(c_437, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_56])).
% 2.58/1.35  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_750, c_437])).
% 2.58/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  Inference rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Ref     : 0
% 2.58/1.35  #Sup     : 170
% 2.58/1.35  #Fact    : 0
% 2.58/1.35  #Define  : 0
% 2.58/1.35  #Split   : 1
% 2.58/1.35  #Chain   : 0
% 2.58/1.35  #Close   : 0
% 2.58/1.35  
% 2.58/1.35  Ordering : KBO
% 2.58/1.35  
% 2.58/1.35  Simplification rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Subsume      : 3
% 2.58/1.35  #Demod        : 40
% 2.58/1.35  #Tautology    : 137
% 2.58/1.35  #SimpNegUnit  : 14
% 2.58/1.35  #BackRed      : 10
% 2.58/1.35  
% 2.58/1.35  #Partial instantiations: 0
% 2.58/1.35  #Strategies tried      : 1
% 2.58/1.35  
% 2.58/1.35  Timing (in seconds)
% 2.58/1.35  ----------------------
% 2.58/1.36  Preprocessing        : 0.33
% 2.58/1.36  Parsing              : 0.18
% 2.58/1.36  CNF conversion       : 0.02
% 2.58/1.36  Main loop            : 0.27
% 2.58/1.36  Inferencing          : 0.11
% 2.58/1.36  Reduction            : 0.09
% 2.58/1.36  Demodulation         : 0.06
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.03
% 2.58/1.36  Abstraction          : 0.02
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.63
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
