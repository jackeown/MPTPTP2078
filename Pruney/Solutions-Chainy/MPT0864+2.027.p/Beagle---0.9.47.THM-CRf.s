%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 181 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 374 expanded)
%              Number of equality atoms :   60 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_85,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_66,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_7'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_600,plain,(
    ! [D_110,A_111,B_112] :
      ( r2_hidden(D_110,A_111)
      | ~ r2_hidden(D_110,k4_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_605,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_111,B_112)),A_111)
      | k4_xboole_0(A_111,B_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_600])).

tff(c_631,plain,(
    ! [D_120,B_121,A_122] :
      ( ~ r2_hidden(D_120,B_121)
      | ~ r2_hidden(D_120,k4_xboole_0(A_122,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_840,plain,(
    ! [A_155,B_156] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_155,B_156)),B_156)
      | k4_xboole_0(A_155,B_156) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_631])).

tff(c_862,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_605,c_840])).

tff(c_54,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_tarski(B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_866,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_54])).

tff(c_122,plain,(
    ! [C_47,A_48] :
      ( C_47 = A_48
      | ~ r2_hidden(C_47,k1_tarski(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    ! [A_48] :
      ( '#skF_7'(k1_tarski(A_48)) = A_48
      | k1_tarski(A_48) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_921,plain,(
    ! [A_48] : '#skF_7'(k1_tarski(A_48)) = A_48 ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_130])).

tff(c_923,plain,(
    ! [A_161] : '#skF_7'(k1_tarski(A_161)) = A_161 ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_130])).

tff(c_729,plain,(
    ! [D_135,A_136,C_137] :
      ( ~ r2_hidden(D_135,A_136)
      | k4_tarski(C_137,D_135) != '#skF_7'(A_136)
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_740,plain,(
    ! [C_137,A_28] :
      ( k4_tarski(C_137,'#skF_7'(A_28)) != '#skF_7'(A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_66,c_729])).

tff(c_929,plain,(
    ! [C_137,A_161] :
      ( k4_tarski(C_137,A_161) != '#skF_7'(k1_tarski(A_161))
      | k1_tarski(A_161) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_923,c_740])).

tff(c_940,plain,(
    ! [C_137,A_161] :
      ( k4_tarski(C_137,A_161) != A_161
      | k1_tarski(A_161) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_929])).

tff(c_941,plain,(
    ! [C_137,A_161] : k4_tarski(C_137,A_161) != A_161 ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_940])).

tff(c_200,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,A_60)
      | ~ r2_hidden(D_59,k4_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_387,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_96,B_97)),A_96)
      | k4_xboole_0(A_96,B_97) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_200])).

tff(c_176,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,(
    ! [A_56,B_55] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_56,B_55)),B_55)
      | k4_xboole_0(A_56,B_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_176])).

tff(c_428,plain,(
    ! [A_96] : k4_xboole_0(A_96,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_387,c_181])).

tff(c_438,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_54])).

tff(c_493,plain,(
    ! [A_48] : '#skF_7'(k1_tarski(A_48)) = A_48 ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_130])).

tff(c_495,plain,(
    ! [A_102] : '#skF_7'(k1_tarski(A_102)) = A_102 ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_130])).

tff(c_284,plain,(
    ! [C_71,A_72,D_73] :
      ( ~ r2_hidden(C_71,A_72)
      | k4_tarski(C_71,D_73) != '#skF_7'(A_72)
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_295,plain,(
    ! [A_28,D_73] :
      ( k4_tarski('#skF_7'(A_28),D_73) != '#skF_7'(A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_66,c_284])).

tff(c_504,plain,(
    ! [A_102,D_73] :
      ( k4_tarski(A_102,D_73) != '#skF_7'(k1_tarski(A_102))
      | k1_tarski(A_102) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_295])).

tff(c_514,plain,(
    ! [A_102,D_73] :
      ( k4_tarski(A_102,D_73) != A_102
      | k1_tarski(A_102) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_504])).

tff(c_515,plain,(
    ! [A_102,D_73] : k4_tarski(A_102,D_73) != A_102 ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_514])).

tff(c_74,plain,(
    k4_tarski('#skF_9','#skF_10') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_105,plain,(
    ! [A_44,B_45] : k1_mcart_1(k4_tarski(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    k1_mcart_1('#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_105])).

tff(c_89,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_98,plain,(
    k2_mcart_1('#skF_8') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_72,plain,
    ( k2_mcart_1('#skF_8') = '#skF_8'
    | k1_mcart_1('#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_133,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_98,c_72])).

tff(c_134,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_136,plain,(
    k4_tarski('#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_136])).

tff(c_561,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_564,plain,(
    k4_tarski('#skF_9','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_74])).

tff(c_948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:14:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.67/1.40  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.67/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.67/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.67/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.67/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.67/1.40  
% 2.67/1.41  tff(f_85, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.67/1.41  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.67/1.41  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.67/1.41  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.67/1.41  tff(f_95, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.67/1.41  tff(f_69, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.67/1.41  tff(c_66, plain, (![A_28]: (r2_hidden('#skF_7'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.67/1.41  tff(c_600, plain, (![D_110, A_111, B_112]: (r2_hidden(D_110, A_111) | ~r2_hidden(D_110, k4_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.41  tff(c_605, plain, (![A_111, B_112]: (r2_hidden('#skF_7'(k4_xboole_0(A_111, B_112)), A_111) | k4_xboole_0(A_111, B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_600])).
% 2.67/1.41  tff(c_631, plain, (![D_120, B_121, A_122]: (~r2_hidden(D_120, B_121) | ~r2_hidden(D_120, k4_xboole_0(A_122, B_121)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.41  tff(c_840, plain, (![A_155, B_156]: (~r2_hidden('#skF_7'(k4_xboole_0(A_155, B_156)), B_156) | k4_xboole_0(A_155, B_156)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_631])).
% 2.67/1.41  tff(c_862, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_605, c_840])).
% 2.67/1.41  tff(c_54, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_tarski(B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.41  tff(c_866, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_862, c_54])).
% 2.67/1.41  tff(c_122, plain, (![C_47, A_48]: (C_47=A_48 | ~r2_hidden(C_47, k1_tarski(A_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.41  tff(c_130, plain, (![A_48]: ('#skF_7'(k1_tarski(A_48))=A_48 | k1_tarski(A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_122])).
% 2.67/1.41  tff(c_921, plain, (![A_48]: ('#skF_7'(k1_tarski(A_48))=A_48)), inference(negUnitSimplification, [status(thm)], [c_866, c_130])).
% 2.67/1.41  tff(c_923, plain, (![A_161]: ('#skF_7'(k1_tarski(A_161))=A_161)), inference(negUnitSimplification, [status(thm)], [c_866, c_130])).
% 2.67/1.41  tff(c_729, plain, (![D_135, A_136, C_137]: (~r2_hidden(D_135, A_136) | k4_tarski(C_137, D_135)!='#skF_7'(A_136) | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.67/1.41  tff(c_740, plain, (![C_137, A_28]: (k4_tarski(C_137, '#skF_7'(A_28))!='#skF_7'(A_28) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_66, c_729])).
% 2.67/1.41  tff(c_929, plain, (![C_137, A_161]: (k4_tarski(C_137, A_161)!='#skF_7'(k1_tarski(A_161)) | k1_tarski(A_161)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_923, c_740])).
% 2.67/1.41  tff(c_940, plain, (![C_137, A_161]: (k4_tarski(C_137, A_161)!=A_161 | k1_tarski(A_161)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_921, c_929])).
% 2.67/1.41  tff(c_941, plain, (![C_137, A_161]: (k4_tarski(C_137, A_161)!=A_161)), inference(negUnitSimplification, [status(thm)], [c_866, c_940])).
% 2.67/1.41  tff(c_200, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, A_60) | ~r2_hidden(D_59, k4_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.41  tff(c_387, plain, (![A_96, B_97]: (r2_hidden('#skF_7'(k4_xboole_0(A_96, B_97)), A_96) | k4_xboole_0(A_96, B_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_200])).
% 2.67/1.41  tff(c_176, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k4_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.41  tff(c_181, plain, (![A_56, B_55]: (~r2_hidden('#skF_7'(k4_xboole_0(A_56, B_55)), B_55) | k4_xboole_0(A_56, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_176])).
% 2.67/1.41  tff(c_428, plain, (![A_96]: (k4_xboole_0(A_96, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_387, c_181])).
% 2.67/1.41  tff(c_438, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_428, c_54])).
% 2.67/1.41  tff(c_493, plain, (![A_48]: ('#skF_7'(k1_tarski(A_48))=A_48)), inference(negUnitSimplification, [status(thm)], [c_438, c_130])).
% 2.67/1.41  tff(c_495, plain, (![A_102]: ('#skF_7'(k1_tarski(A_102))=A_102)), inference(negUnitSimplification, [status(thm)], [c_438, c_130])).
% 2.67/1.41  tff(c_284, plain, (![C_71, A_72, D_73]: (~r2_hidden(C_71, A_72) | k4_tarski(C_71, D_73)!='#skF_7'(A_72) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.67/1.41  tff(c_295, plain, (![A_28, D_73]: (k4_tarski('#skF_7'(A_28), D_73)!='#skF_7'(A_28) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_66, c_284])).
% 2.67/1.41  tff(c_504, plain, (![A_102, D_73]: (k4_tarski(A_102, D_73)!='#skF_7'(k1_tarski(A_102)) | k1_tarski(A_102)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_495, c_295])).
% 2.67/1.41  tff(c_514, plain, (![A_102, D_73]: (k4_tarski(A_102, D_73)!=A_102 | k1_tarski(A_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_493, c_504])).
% 2.67/1.41  tff(c_515, plain, (![A_102, D_73]: (k4_tarski(A_102, D_73)!=A_102)), inference(negUnitSimplification, [status(thm)], [c_438, c_514])).
% 2.67/1.41  tff(c_74, plain, (k4_tarski('#skF_9', '#skF_10')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.41  tff(c_105, plain, (![A_44, B_45]: (k1_mcart_1(k4_tarski(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.41  tff(c_114, plain, (k1_mcart_1('#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_74, c_105])).
% 2.67/1.41  tff(c_89, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.41  tff(c_98, plain, (k2_mcart_1('#skF_8')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 2.67/1.41  tff(c_72, plain, (k2_mcart_1('#skF_8')='#skF_8' | k1_mcart_1('#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.41  tff(c_133, plain, ('#skF_10'='#skF_8' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_98, c_72])).
% 2.67/1.41  tff(c_134, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_133])).
% 2.67/1.41  tff(c_136, plain, (k4_tarski('#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74])).
% 2.67/1.41  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_136])).
% 2.67/1.41  tff(c_561, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_133])).
% 2.67/1.41  tff(c_564, plain, (k4_tarski('#skF_9', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_561, c_74])).
% 2.67/1.41  tff(c_948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_564])).
% 2.67/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  Inference rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Ref     : 0
% 2.67/1.41  #Sup     : 213
% 2.67/1.41  #Fact    : 0
% 2.67/1.41  #Define  : 0
% 2.67/1.41  #Split   : 1
% 2.67/1.41  #Chain   : 0
% 2.67/1.41  #Close   : 0
% 2.67/1.41  
% 2.67/1.41  Ordering : KBO
% 2.67/1.41  
% 2.67/1.41  Simplification rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Subsume      : 18
% 2.67/1.41  #Demod        : 38
% 2.67/1.41  #Tautology    : 100
% 2.67/1.41  #SimpNegUnit  : 14
% 2.67/1.41  #BackRed      : 14
% 2.67/1.41  
% 2.67/1.41  #Partial instantiations: 0
% 2.67/1.41  #Strategies tried      : 1
% 2.67/1.41  
% 2.67/1.41  Timing (in seconds)
% 2.67/1.41  ----------------------
% 2.90/1.42  Preprocessing        : 0.31
% 2.90/1.42  Parsing              : 0.16
% 2.90/1.42  CNF conversion       : 0.03
% 2.90/1.42  Main loop            : 0.34
% 2.90/1.42  Inferencing          : 0.12
% 2.90/1.42  Reduction            : 0.10
% 2.90/1.42  Demodulation         : 0.07
% 2.90/1.42  BG Simplification    : 0.02
% 2.90/1.42  Subsumption          : 0.07
% 2.90/1.42  Abstraction          : 0.02
% 2.90/1.42  MUC search           : 0.00
% 2.90/1.42  Cooper               : 0.00
% 2.90/1.42  Total                : 0.68
% 2.90/1.42  Index Insertion      : 0.00
% 2.90/1.42  Index Deletion       : 0.00
% 2.90/1.42  Index Matching       : 0.00
% 2.90/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
