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

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 110 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 224 expanded)
%              Number of equality atoms :   27 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_69,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [C_16] :
      ( C_16 = '#skF_4'
      | ~ r2_hidden(C_16,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_45,plain,
    ( '#skF_2'('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41,c_24])).

tff(c_48,plain,(
    '#skF_2'('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_45])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_55,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_52])).

tff(c_93,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [B_31] :
      ( '#skF_1'('#skF_3',B_31) = '#skF_4'
      | r1_tarski('#skF_3',B_31) ) ),
    inference(resolution,[status(thm)],[c_93,c_24])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_208,plain,(
    ! [A_46,B_47] :
      ( k1_tarski(A_46) = B_47
      | ~ r1_tarski(B_47,k1_tarski(A_46))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_221,plain,(
    ! [A_46] :
      ( k1_tarski(A_46) = '#skF_3'
      | ~ r2_hidden(A_46,'#skF_3')
      | '#skF_1'('#skF_3',k1_tarski(A_46)) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_98,c_208])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | ~ r1_tarski(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_242,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_256,plain,(
    ! [A_52,B_53] :
      ( '#skF_1'(A_52,B_53) = '#skF_4'
      | ~ r1_tarski(A_52,'#skF_3')
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_242,c_24])).

tff(c_406,plain,(
    ! [A_67,B_68] :
      ( '#skF_1'(k1_tarski(A_67),B_68) = '#skF_4'
      | r1_tarski(k1_tarski(A_67),B_68)
      | ~ r2_hidden(A_67,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_256])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_442,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | '#skF_1'(k1_tarski(A_69),B_70) = '#skF_4'
      | ~ r2_hidden(A_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_406,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_590,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden('#skF_4',B_80)
      | r1_tarski(k1_tarski(A_81),B_80)
      | r2_hidden(A_81,B_80)
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_4])).

tff(c_636,plain,(
    ! [B_82,A_83] :
      ( ~ r2_hidden('#skF_4',B_82)
      | r2_hidden(A_83,B_82)
      | ~ r2_hidden(A_83,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_590,c_20])).

tff(c_666,plain,(
    ! [A_88] :
      ( r2_hidden(A_88,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_88,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_636])).

tff(c_807,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_98,k1_tarski('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_666,c_4])).

tff(c_819,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_807])).

tff(c_832,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_819])).

tff(c_833,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_832])).

tff(c_88,plain,(
    ! [A_13,B_14] :
      ( k1_tarski(A_13) = B_14
      | ~ r1_tarski(B_14,k1_tarski(A_13))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_848,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_833,c_88])).

tff(c_863,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_848])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:20:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.44  
% 2.62/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.44  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.62/1.44  
% 2.62/1.44  %Foreground sorts:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Background operators:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Foreground operators:
% 2.62/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.44  
% 2.97/1.45  tff(f_69, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.97/1.45  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.97/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.97/1.45  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.97/1.45  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.97/1.45  tff(c_28, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.45  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.45  tff(c_41, plain, (![A_20]: (r2_hidden('#skF_2'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.45  tff(c_24, plain, (![C_16]: (C_16='#skF_4' | ~r2_hidden(C_16, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.45  tff(c_45, plain, ('#skF_2'('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_41, c_24])).
% 2.97/1.45  tff(c_48, plain, ('#skF_2'('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_45])).
% 2.97/1.45  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.45  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48, c_8])).
% 2.97/1.45  tff(c_55, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_52])).
% 2.97/1.45  tff(c_93, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.45  tff(c_98, plain, (![B_31]: ('#skF_1'('#skF_3', B_31)='#skF_4' | r1_tarski('#skF_3', B_31))), inference(resolution, [status(thm)], [c_93, c_24])).
% 2.97/1.45  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.45  tff(c_83, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.97/1.45  tff(c_208, plain, (![A_46, B_47]: (k1_tarski(A_46)=B_47 | ~r1_tarski(B_47, k1_tarski(A_46)) | ~r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_22, c_83])).
% 2.97/1.45  tff(c_221, plain, (![A_46]: (k1_tarski(A_46)='#skF_3' | ~r2_hidden(A_46, '#skF_3') | '#skF_1'('#skF_3', k1_tarski(A_46))='#skF_4')), inference(resolution, [status(thm)], [c_98, c_208])).
% 2.97/1.45  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.97/1.45  tff(c_72, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | ~r1_tarski(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.45  tff(c_81, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(resolution, [status(thm)], [c_14, c_72])).
% 2.97/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.45  tff(c_110, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.45  tff(c_242, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.97/1.45  tff(c_256, plain, (![A_52, B_53]: ('#skF_1'(A_52, B_53)='#skF_4' | ~r1_tarski(A_52, '#skF_3') | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_242, c_24])).
% 2.97/1.45  tff(c_406, plain, (![A_67, B_68]: ('#skF_1'(k1_tarski(A_67), B_68)='#skF_4' | r1_tarski(k1_tarski(A_67), B_68) | ~r2_hidden(A_67, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_256])).
% 2.97/1.45  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.45  tff(c_442, plain, (![A_69, B_70]: (r2_hidden(A_69, B_70) | '#skF_1'(k1_tarski(A_69), B_70)='#skF_4' | ~r2_hidden(A_69, '#skF_3'))), inference(resolution, [status(thm)], [c_406, c_20])).
% 2.97/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.45  tff(c_590, plain, (![B_80, A_81]: (~r2_hidden('#skF_4', B_80) | r1_tarski(k1_tarski(A_81), B_80) | r2_hidden(A_81, B_80) | ~r2_hidden(A_81, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_4])).
% 2.97/1.45  tff(c_636, plain, (![B_82, A_83]: (~r2_hidden('#skF_4', B_82) | r2_hidden(A_83, B_82) | ~r2_hidden(A_83, '#skF_3'))), inference(resolution, [status(thm)], [c_590, c_20])).
% 2.97/1.45  tff(c_666, plain, (![A_88]: (r2_hidden(A_88, k1_tarski('#skF_4')) | ~r2_hidden(A_88, '#skF_3'))), inference(resolution, [status(thm)], [c_81, c_636])).
% 2.97/1.45  tff(c_807, plain, (![A_98]: (r1_tarski(A_98, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_98, k1_tarski('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_666, c_4])).
% 2.97/1.45  tff(c_819, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', '#skF_3') | k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_221, c_807])).
% 2.97/1.45  tff(c_832, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_819])).
% 2.97/1.45  tff(c_833, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_28, c_832])).
% 2.97/1.45  tff(c_88, plain, (![A_13, B_14]: (k1_tarski(A_13)=B_14 | ~r1_tarski(B_14, k1_tarski(A_13)) | ~r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_22, c_83])).
% 2.97/1.45  tff(c_848, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_833, c_88])).
% 2.97/1.45  tff(c_863, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_848])).
% 2.97/1.45  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_863])).
% 2.97/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  Inference rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Ref     : 0
% 2.97/1.45  #Sup     : 191
% 2.97/1.45  #Fact    : 0
% 2.97/1.45  #Define  : 0
% 2.97/1.45  #Split   : 0
% 2.97/1.45  #Chain   : 0
% 2.97/1.45  #Close   : 0
% 2.97/1.45  
% 2.97/1.45  Ordering : KBO
% 2.97/1.45  
% 2.97/1.45  Simplification rules
% 2.97/1.45  ----------------------
% 2.97/1.45  #Subsume      : 49
% 2.97/1.45  #Demod        : 32
% 2.97/1.45  #Tautology    : 45
% 2.97/1.45  #SimpNegUnit  : 12
% 2.97/1.45  #BackRed      : 0
% 2.97/1.45  
% 2.97/1.45  #Partial instantiations: 0
% 2.97/1.45  #Strategies tried      : 1
% 2.97/1.45  
% 2.97/1.45  Timing (in seconds)
% 2.97/1.45  ----------------------
% 2.97/1.46  Preprocessing        : 0.30
% 2.97/1.46  Parsing              : 0.16
% 2.97/1.46  CNF conversion       : 0.02
% 2.97/1.46  Main loop            : 0.37
% 2.97/1.46  Inferencing          : 0.13
% 2.97/1.46  Reduction            : 0.10
% 2.97/1.46  Demodulation         : 0.06
% 2.97/1.46  BG Simplification    : 0.02
% 2.97/1.46  Subsumption          : 0.10
% 2.97/1.46  Abstraction          : 0.02
% 2.97/1.46  MUC search           : 0.00
% 2.97/1.46  Cooper               : 0.00
% 2.97/1.46  Total                : 0.70
% 2.97/1.46  Index Insertion      : 0.00
% 2.97/1.46  Index Deletion       : 0.00
% 2.97/1.46  Index Matching       : 0.00
% 2.97/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
