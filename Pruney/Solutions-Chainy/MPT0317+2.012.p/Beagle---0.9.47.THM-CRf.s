%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 155 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 272 expanded)
%              Number of equality atoms :   31 (  96 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(c_46,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_167,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_174,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( r2_hidden(B_55,D_56)
      | ~ r2_hidden(k4_tarski(A_57,B_55),k2_zfmisc_1(C_58,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_178,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_167,c_174])).

tff(c_139,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(k1_tarski(A_51),k1_tarski(B_52)) = k1_tarski(A_51)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( ~ r2_hidden(B_25,A_24)
      | k4_xboole_0(A_24,k1_tarski(B_25)) != A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_161,plain,(
    ! [B_52,A_51] :
      ( ~ r2_hidden(B_52,k1_tarski(A_51))
      | B_52 = A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_40])).

tff(c_182,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_178,c_161])).

tff(c_184,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_167])).

tff(c_24,plain,(
    ! [A_9,C_11,B_10,D_12] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_193,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_184,c_24])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_193])).

tff(c_202,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_213,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_213])).

tff(c_215,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [B_30,C_31] : r1_tarski(k1_tarski(B_30),k2_tarski(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_88,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | ~ r1_tarski(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_99,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(resolution,[status(thm)],[c_71,c_88])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12))
      | ~ r2_hidden(B_10,D_12)
      | ~ r2_hidden(A_9,C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_201,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_233,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_50])).

tff(c_234,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_233])).

tff(c_237,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_99,c_237])).

tff(c_243,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_242,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_244,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_318,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_325,plain,(
    ! [B_96,D_97,A_98,C_99] :
      ( r2_hidden(B_96,D_97)
      | ~ r2_hidden(k4_tarski(A_98,B_96),k2_zfmisc_1(C_99,D_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_329,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_318,c_325])).

tff(c_284,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k1_tarski(A_88),k1_tarski(B_89)) = k1_tarski(A_88)
      | B_89 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_306,plain,(
    ! [B_89,A_88] :
      ( ~ r2_hidden(B_89,k1_tarski(A_88))
      | B_89 = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_40])).

tff(c_332,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_329,c_306])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_332])).

tff(c_338,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_343,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_54])).

tff(c_337,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_574,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_50])).

tff(c_575,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_574])).

tff(c_578,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_99,c_578])).

tff(c_584,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_48,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_630,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_584,c_48])).

tff(c_824,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( r2_hidden(k4_tarski(A_192,B_193),k2_zfmisc_1(C_194,D_195))
      | ~ r2_hidden(B_193,D_195)
      | ~ r2_hidden(A_192,C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_583,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_760,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_584,c_583,c_44])).

tff(c_827,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_824,c_760])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_99,c_827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.19/1.52  
% 3.19/1.52  %Foreground sorts:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Background operators:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Foreground operators:
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.52  
% 3.40/1.55  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.40/1.55  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 3.40/1.55  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.40/1.55  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.40/1.55  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.55  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.40/1.55  tff(f_73, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.40/1.55  tff(c_46, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_101, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 3.40/1.55  tff(c_52, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_167, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_174, plain, (![B_55, D_56, A_57, C_58]: (r2_hidden(B_55, D_56) | ~r2_hidden(k4_tarski(A_57, B_55), k2_zfmisc_1(C_58, D_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.55  tff(c_178, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_167, c_174])).
% 3.40/1.55  tff(c_139, plain, (![A_51, B_52]: (k4_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k1_tarski(A_51) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.55  tff(c_40, plain, (![B_25, A_24]: (~r2_hidden(B_25, A_24) | k4_xboole_0(A_24, k1_tarski(B_25))!=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.55  tff(c_161, plain, (![B_52, A_51]: (~r2_hidden(B_52, k1_tarski(A_51)) | B_52=A_51)), inference(superposition, [status(thm), theory('equality')], [c_139, c_40])).
% 3.40/1.55  tff(c_182, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_178, c_161])).
% 3.40/1.55  tff(c_184, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_167])).
% 3.40/1.55  tff(c_24, plain, (![A_9, C_11, B_10, D_12]: (r2_hidden(A_9, C_11) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.55  tff(c_193, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_184, c_24])).
% 3.40/1.55  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_193])).
% 3.40/1.55  tff(c_202, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_54, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_213, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_54])).
% 3.40/1.55  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_213])).
% 3.40/1.55  tff(c_215, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 3.40/1.55  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.55  tff(c_68, plain, (![B_30, C_31]: (r1_tarski(k1_tarski(B_30), k2_tarski(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.55  tff(c_71, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 3.40/1.55  tff(c_88, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | ~r1_tarski(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.55  tff(c_99, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_71, c_88])).
% 3.40/1.55  tff(c_20, plain, (![A_9, B_10, C_11, D_12]: (r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)) | ~r2_hidden(B_10, D_12) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.55  tff(c_201, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_50, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_233, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_50])).
% 3.40/1.55  tff(c_234, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_202, c_233])).
% 3.40/1.55  tff(c_237, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_234])).
% 3.40/1.55  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_99, c_237])).
% 3.40/1.55  tff(c_243, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 3.40/1.55  tff(c_242, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 3.40/1.55  tff(c_244, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_242])).
% 3.40/1.55  tff(c_318, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_325, plain, (![B_96, D_97, A_98, C_99]: (r2_hidden(B_96, D_97) | ~r2_hidden(k4_tarski(A_98, B_96), k2_zfmisc_1(C_99, D_97)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.55  tff(c_329, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_318, c_325])).
% 3.40/1.55  tff(c_284, plain, (![A_88, B_89]: (k4_xboole_0(k1_tarski(A_88), k1_tarski(B_89))=k1_tarski(A_88) | B_89=A_88)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.55  tff(c_306, plain, (![B_89, A_88]: (~r2_hidden(B_89, k1_tarski(A_88)) | B_89=A_88)), inference(superposition, [status(thm), theory('equality')], [c_284, c_40])).
% 3.40/1.55  tff(c_332, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_329, c_306])).
% 3.40/1.55  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_332])).
% 3.40/1.55  tff(c_338, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_343, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_338, c_54])).
% 3.40/1.55  tff(c_337, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 3.40/1.55  tff(c_574, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_50])).
% 3.40/1.55  tff(c_575, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_338, c_574])).
% 3.40/1.55  tff(c_578, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_575])).
% 3.40/1.55  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_99, c_578])).
% 3.40/1.55  tff(c_584, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_242])).
% 3.40/1.55  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_630, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_584, c_48])).
% 3.40/1.55  tff(c_824, plain, (![A_192, B_193, C_194, D_195]: (r2_hidden(k4_tarski(A_192, B_193), k2_zfmisc_1(C_194, D_195)) | ~r2_hidden(B_193, D_195) | ~r2_hidden(A_192, C_194))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.55  tff(c_583, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_242])).
% 3.40/1.55  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.55  tff(c_760, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_584, c_583, c_44])).
% 3.40/1.55  tff(c_827, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_824, c_760])).
% 3.40/1.55  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_630, c_99, c_827])).
% 3.40/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  Inference rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Ref     : 0
% 3.40/1.55  #Sup     : 176
% 3.40/1.55  #Fact    : 0
% 3.40/1.55  #Define  : 0
% 3.40/1.55  #Split   : 5
% 3.40/1.55  #Chain   : 0
% 3.40/1.55  #Close   : 0
% 3.40/1.55  
% 3.40/1.55  Ordering : KBO
% 3.40/1.55  
% 3.40/1.55  Simplification rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Subsume      : 9
% 3.40/1.55  #Demod        : 94
% 3.40/1.55  #Tautology    : 112
% 3.40/1.55  #SimpNegUnit  : 6
% 3.40/1.55  #BackRed      : 4
% 3.40/1.55  
% 3.40/1.55  #Partial instantiations: 0
% 3.40/1.55  #Strategies tried      : 1
% 3.40/1.55  
% 3.40/1.55  Timing (in seconds)
% 3.40/1.55  ----------------------
% 3.40/1.55  Preprocessing        : 0.33
% 3.40/1.55  Parsing              : 0.17
% 3.40/1.55  CNF conversion       : 0.02
% 3.40/1.55  Main loop            : 0.41
% 3.40/1.55  Inferencing          : 0.16
% 3.40/1.55  Reduction            : 0.14
% 3.40/1.55  Demodulation         : 0.10
% 3.40/1.55  BG Simplification    : 0.02
% 3.40/1.55  Subsumption          : 0.07
% 3.40/1.55  Abstraction          : 0.02
% 3.40/1.55  MUC search           : 0.00
% 3.40/1.56  Cooper               : 0.00
% 3.40/1.56  Total                : 0.81
% 3.40/1.56  Index Insertion      : 0.00
% 3.40/1.56  Index Deletion       : 0.00
% 3.40/1.56  Index Matching       : 0.00
% 3.40/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
