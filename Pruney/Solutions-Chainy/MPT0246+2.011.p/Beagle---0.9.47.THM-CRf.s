%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 142 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  107 ( 284 expanded)
%              Number of equality atoms :   43 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_47,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_2'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ! [C_21] :
      ( C_21 = '#skF_4'
      | ~ r2_hidden(C_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,
    ( '#skF_2'('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_47,c_30])).

tff(c_54,plain,(
    '#skF_2'('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_51])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_61,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_58])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(k1_tarski(A_18),B_19) = k1_xboole_0
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [B_39] :
      ( '#skF_1'('#skF_3',B_39) = '#skF_4'
      | r1_tarski('#skF_3',B_39) ) ),
    inference(resolution,[status(thm)],[c_111,c_30])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_224,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | k4_xboole_0(A_56,B_55) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_94])).

tff(c_311,plain,(
    ! [B_62] :
      ( B_62 = '#skF_3'
      | k4_xboole_0(B_62,'#skF_3') != k1_xboole_0
      | '#skF_1'('#skF_3',B_62) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_116,c_224])).

tff(c_326,plain,(
    ! [A_18] :
      ( k1_tarski(A_18) = '#skF_3'
      | '#skF_1'('#skF_3',k1_tarski(A_18)) = '#skF_4'
      | ~ r2_hidden(A_18,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_311])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_104,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | k4_xboole_0(k1_tarski(A_35),B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_104])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_379,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_393,plain,(
    ! [A_72,B_73] :
      ( '#skF_1'(A_72,B_73) = '#skF_4'
      | ~ r1_tarski(A_72,'#skF_3')
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_379,c_30])).

tff(c_430,plain,(
    ! [A_77,B_78] :
      ( '#skF_1'(A_77,B_78) = '#skF_4'
      | r1_tarski(A_77,B_78)
      | k4_xboole_0(A_77,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_393])).

tff(c_188,plain,(
    ! [A_35,B_47] :
      ( r2_hidden(A_35,B_47)
      | ~ r1_tarski(k1_tarski(A_35),B_47) ) ),
    inference(resolution,[status(thm)],[c_109,c_178])).

tff(c_1103,plain,(
    ! [A_131,B_132] :
      ( r2_hidden(A_131,B_132)
      | '#skF_1'(k1_tarski(A_131),B_132) = '#skF_4'
      | k4_xboole_0(k1_tarski(A_131),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_430,c_188])).

tff(c_1112,plain,(
    ! [A_133,B_134] :
      ( r2_hidden(A_133,B_134)
      | '#skF_1'(k1_tarski(A_133),B_134) = '#skF_4'
      | ~ r2_hidden(A_133,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1103])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1401,plain,(
    ! [B_151,A_152] :
      ( ~ r2_hidden('#skF_4',B_151)
      | r1_tarski(k1_tarski(A_152),B_151)
      | r2_hidden(A_152,B_151)
      | ~ r2_hidden(A_152,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_4])).

tff(c_1510,plain,(
    ! [B_155,A_156] :
      ( ~ r2_hidden('#skF_4',B_155)
      | r2_hidden(A_156,B_155)
      | ~ r2_hidden(A_156,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1401,c_188])).

tff(c_1530,plain,(
    ! [A_157] :
      ( r2_hidden(A_157,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_157,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_109,c_1510])).

tff(c_1639,plain,(
    ! [A_162] :
      ( r1_tarski(A_162,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_162,k1_tarski('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1530,c_4])).

tff(c_1659,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_1639])).

tff(c_1674,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_61,c_1659])).

tff(c_1675,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1674])).

tff(c_99,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_94])).

tff(c_1717,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1675,c_99])).

tff(c_1744,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1717])).

tff(c_1770,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1744])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:59:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.61  
% 3.48/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.61  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.48/1.61  
% 3.48/1.61  %Foreground sorts:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Background operators:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Foreground operators:
% 3.48/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.61  
% 3.48/1.62  tff(f_75, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.48/1.62  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.48/1.62  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.48/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.48/1.62  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.48/1.62  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.62  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.48/1.62  tff(c_47, plain, (![A_25]: (r2_hidden('#skF_2'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.62  tff(c_30, plain, (![C_21]: (C_21='#skF_4' | ~r2_hidden(C_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.48/1.62  tff(c_51, plain, ('#skF_2'('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_47, c_30])).
% 3.48/1.62  tff(c_54, plain, ('#skF_2'('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_32, c_51])).
% 3.48/1.62  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.62  tff(c_58, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 3.48/1.62  tff(c_61, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_58])).
% 3.48/1.62  tff(c_28, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), B_19)=k1_xboole_0 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.48/1.62  tff(c_34, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.48/1.62  tff(c_111, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.62  tff(c_116, plain, (![B_39]: ('#skF_1'('#skF_3', B_39)='#skF_4' | r1_tarski('#skF_3', B_39))), inference(resolution, [status(thm)], [c_111, c_30])).
% 3.48/1.62  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.62  tff(c_94, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.62  tff(c_224, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | k4_xboole_0(A_56, B_55)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_94])).
% 3.48/1.62  tff(c_311, plain, (![B_62]: (B_62='#skF_3' | k4_xboole_0(B_62, '#skF_3')!=k1_xboole_0 | '#skF_1'('#skF_3', B_62)='#skF_4')), inference(resolution, [status(thm)], [c_116, c_224])).
% 3.48/1.62  tff(c_326, plain, (![A_18]: (k1_tarski(A_18)='#skF_3' | '#skF_1'('#skF_3', k1_tarski(A_18))='#skF_4' | ~r2_hidden(A_18, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_311])).
% 3.48/1.62  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.62  tff(c_69, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.62  tff(c_77, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_69])).
% 3.48/1.62  tff(c_104, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | k4_xboole_0(k1_tarski(A_35), B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.48/1.62  tff(c_109, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_104])).
% 3.48/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.62  tff(c_178, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.62  tff(c_379, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_178])).
% 3.48/1.62  tff(c_393, plain, (![A_72, B_73]: ('#skF_1'(A_72, B_73)='#skF_4' | ~r1_tarski(A_72, '#skF_3') | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_379, c_30])).
% 3.48/1.62  tff(c_430, plain, (![A_77, B_78]: ('#skF_1'(A_77, B_78)='#skF_4' | r1_tarski(A_77, B_78) | k4_xboole_0(A_77, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_393])).
% 3.48/1.62  tff(c_188, plain, (![A_35, B_47]: (r2_hidden(A_35, B_47) | ~r1_tarski(k1_tarski(A_35), B_47))), inference(resolution, [status(thm)], [c_109, c_178])).
% 3.48/1.62  tff(c_1103, plain, (![A_131, B_132]: (r2_hidden(A_131, B_132) | '#skF_1'(k1_tarski(A_131), B_132)='#skF_4' | k4_xboole_0(k1_tarski(A_131), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_430, c_188])).
% 3.48/1.62  tff(c_1112, plain, (![A_133, B_134]: (r2_hidden(A_133, B_134) | '#skF_1'(k1_tarski(A_133), B_134)='#skF_4' | ~r2_hidden(A_133, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1103])).
% 3.48/1.62  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.62  tff(c_1401, plain, (![B_151, A_152]: (~r2_hidden('#skF_4', B_151) | r1_tarski(k1_tarski(A_152), B_151) | r2_hidden(A_152, B_151) | ~r2_hidden(A_152, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_4])).
% 3.48/1.62  tff(c_1510, plain, (![B_155, A_156]: (~r2_hidden('#skF_4', B_155) | r2_hidden(A_156, B_155) | ~r2_hidden(A_156, '#skF_3'))), inference(resolution, [status(thm)], [c_1401, c_188])).
% 3.48/1.62  tff(c_1530, plain, (![A_157]: (r2_hidden(A_157, k1_tarski('#skF_4')) | ~r2_hidden(A_157, '#skF_3'))), inference(resolution, [status(thm)], [c_109, c_1510])).
% 3.48/1.62  tff(c_1639, plain, (![A_162]: (r1_tarski(A_162, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_162, k1_tarski('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_1530, c_4])).
% 3.48/1.62  tff(c_1659, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', '#skF_3') | k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_1639])).
% 3.48/1.62  tff(c_1674, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_61, c_1659])).
% 3.48/1.62  tff(c_1675, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_1674])).
% 3.48/1.62  tff(c_99, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_94])).
% 3.48/1.62  tff(c_1717, plain, (k1_tarski('#skF_4')='#skF_3' | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1675, c_99])).
% 3.48/1.62  tff(c_1744, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_1717])).
% 3.48/1.62  tff(c_1770, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1744])).
% 3.48/1.62  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_1770])).
% 3.48/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.62  
% 3.48/1.62  Inference rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Ref     : 0
% 3.48/1.62  #Sup     : 400
% 3.48/1.62  #Fact    : 0
% 3.48/1.62  #Define  : 0
% 3.48/1.62  #Split   : 0
% 3.48/1.62  #Chain   : 0
% 3.48/1.62  #Close   : 0
% 3.48/1.62  
% 3.48/1.62  Ordering : KBO
% 3.48/1.62  
% 3.48/1.62  Simplification rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Subsume      : 122
% 3.48/1.62  #Demod        : 57
% 3.48/1.62  #Tautology    : 91
% 3.48/1.62  #SimpNegUnit  : 19
% 3.48/1.62  #BackRed      : 0
% 3.48/1.62  
% 3.48/1.62  #Partial instantiations: 0
% 3.48/1.62  #Strategies tried      : 1
% 3.48/1.62  
% 3.48/1.62  Timing (in seconds)
% 3.48/1.62  ----------------------
% 3.48/1.62  Preprocessing        : 0.29
% 3.48/1.62  Parsing              : 0.15
% 3.48/1.62  CNF conversion       : 0.02
% 3.48/1.62  Main loop            : 0.54
% 3.48/1.62  Inferencing          : 0.18
% 3.48/1.62  Reduction            : 0.14
% 3.48/1.62  Demodulation         : 0.09
% 3.48/1.62  BG Simplification    : 0.02
% 3.48/1.62  Subsumption          : 0.16
% 3.48/1.62  Abstraction          : 0.03
% 3.48/1.62  MUC search           : 0.00
% 3.48/1.62  Cooper               : 0.00
% 3.48/1.62  Total                : 0.86
% 3.48/1.62  Index Insertion      : 0.00
% 3.48/1.62  Index Deletion       : 0.00
% 3.48/1.62  Index Matching       : 0.00
% 3.48/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
