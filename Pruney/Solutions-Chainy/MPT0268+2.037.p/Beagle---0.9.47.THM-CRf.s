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
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 35.47s
% Output     : CNFRefutation 35.47s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 137 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_214,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2613,plain,(
    ! [A_3625,B_3626,C_3627] :
      ( r2_hidden('#skF_1'(A_3625,B_3626,C_3627),A_3625)
      | r2_hidden('#skF_2'(A_3625,B_3626,C_3627),C_3627)
      | k4_xboole_0(A_3625,B_3626) = C_3627 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2679,plain,(
    ! [A_3625,B_3626] :
      ( r2_hidden('#skF_2'(A_3625,B_3626,A_3625),A_3625)
      | k4_xboole_0(A_3625,B_3626) = A_3625 ) ),
    inference(resolution,[status(thm)],[c_2613,c_16])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2896,plain,(
    ! [A_3912,B_3913,C_3914] :
      ( ~ r2_hidden('#skF_1'(A_3912,B_3913,C_3914),C_3914)
      | r2_hidden('#skF_2'(A_3912,B_3913,C_3914),B_3913)
      | ~ r2_hidden('#skF_2'(A_3912,B_3913,C_3914),A_3912)
      | k4_xboole_0(A_3912,B_3913) = C_3914 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36087,plain,(
    ! [A_7747,B_7748] :
      ( r2_hidden('#skF_2'(A_7747,B_7748,A_7747),B_7748)
      | ~ r2_hidden('#skF_2'(A_7747,B_7748,A_7747),A_7747)
      | k4_xboole_0(A_7747,B_7748) = A_7747 ) ),
    inference(resolution,[status(thm)],[c_14,c_2896])).

tff(c_36123,plain,(
    ! [A_7803,B_7804] :
      ( r2_hidden('#skF_2'(A_7803,B_7804,A_7803),B_7804)
      | k4_xboole_0(A_7803,B_7804) = A_7803 ) ),
    inference(resolution,[status(thm)],[c_2679,c_36087])).

tff(c_32,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88799,plain,(
    ! [A_12171,A_12172] :
      ( '#skF_2'(A_12171,k1_tarski(A_12172),A_12171) = A_12172
      | k4_xboole_0(A_12171,k1_tarski(A_12172)) = A_12171 ) ),
    inference(resolution,[status(thm)],[c_36123,c_32])).

tff(c_89128,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_88799,c_214])).

tff(c_89140,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_89128,c_2679])).

tff(c_89199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_203,c_89140])).

tff(c_89200,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_34,plain,(
    ! [C_22] : r2_hidden(C_22,k1_tarski(C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89201,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89247,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89201,c_62])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89255,plain,(
    ! [D_12288] :
      ( ~ r2_hidden(D_12288,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_12288,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89247,c_6])).

tff(c_89259,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_89255])).

tff(c_89263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89200,c_89259])).

tff(c_89264,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_89265,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89280,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89265,c_64])).

tff(c_89292,plain,(
    ! [D_12297] :
      ( ~ r2_hidden(D_12297,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_12297,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89280,c_6])).

tff(c_89296,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_89292])).

tff(c_89300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89264,c_89296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.47/26.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.47/26.78  
% 35.47/26.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.47/26.78  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 35.47/26.78  
% 35.47/26.78  %Foreground sorts:
% 35.47/26.78  
% 35.47/26.78  
% 35.47/26.78  %Background operators:
% 35.47/26.78  
% 35.47/26.78  
% 35.47/26.78  %Foreground operators:
% 35.47/26.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 35.47/26.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.47/26.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 35.47/26.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 35.47/26.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 35.47/26.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 35.47/26.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 35.47/26.78  tff('#skF_7', type, '#skF_7': $i).
% 35.47/26.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 35.47/26.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 35.47/26.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 35.47/26.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 35.47/26.78  tff('#skF_5', type, '#skF_5': $i).
% 35.47/26.78  tff('#skF_6', type, '#skF_6': $i).
% 35.47/26.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 35.47/26.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 35.47/26.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 35.47/26.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 35.47/26.78  tff('#skF_8', type, '#skF_8': $i).
% 35.47/26.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.47/26.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.47/26.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 35.47/26.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 35.47/26.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 35.47/26.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 35.47/26.78  
% 35.47/26.79  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 35.47/26.79  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 35.47/26.79  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 35.47/26.79  tff(c_58, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.47/26.79  tff(c_214, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_58])).
% 35.47/26.79  tff(c_60, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.47/26.79  tff(c_203, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 35.47/26.79  tff(c_2613, plain, (![A_3625, B_3626, C_3627]: (r2_hidden('#skF_1'(A_3625, B_3626, C_3627), A_3625) | r2_hidden('#skF_2'(A_3625, B_3626, C_3627), C_3627) | k4_xboole_0(A_3625, B_3626)=C_3627)), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.47/26.79  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.47/26.79  tff(c_2679, plain, (![A_3625, B_3626]: (r2_hidden('#skF_2'(A_3625, B_3626, A_3625), A_3625) | k4_xboole_0(A_3625, B_3626)=A_3625)), inference(resolution, [status(thm)], [c_2613, c_16])).
% 35.47/26.79  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.47/26.79  tff(c_2896, plain, (![A_3912, B_3913, C_3914]: (~r2_hidden('#skF_1'(A_3912, B_3913, C_3914), C_3914) | r2_hidden('#skF_2'(A_3912, B_3913, C_3914), B_3913) | ~r2_hidden('#skF_2'(A_3912, B_3913, C_3914), A_3912) | k4_xboole_0(A_3912, B_3913)=C_3914)), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.47/26.79  tff(c_36087, plain, (![A_7747, B_7748]: (r2_hidden('#skF_2'(A_7747, B_7748, A_7747), B_7748) | ~r2_hidden('#skF_2'(A_7747, B_7748, A_7747), A_7747) | k4_xboole_0(A_7747, B_7748)=A_7747)), inference(resolution, [status(thm)], [c_14, c_2896])).
% 35.47/26.79  tff(c_36123, plain, (![A_7803, B_7804]: (r2_hidden('#skF_2'(A_7803, B_7804, A_7803), B_7804) | k4_xboole_0(A_7803, B_7804)=A_7803)), inference(resolution, [status(thm)], [c_2679, c_36087])).
% 35.47/26.79  tff(c_32, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 35.47/26.79  tff(c_88799, plain, (![A_12171, A_12172]: ('#skF_2'(A_12171, k1_tarski(A_12172), A_12171)=A_12172 | k4_xboole_0(A_12171, k1_tarski(A_12172))=A_12171)), inference(resolution, [status(thm)], [c_36123, c_32])).
% 35.47/26.79  tff(c_89128, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_88799, c_214])).
% 35.47/26.79  tff(c_89140, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_89128, c_2679])).
% 35.47/26.79  tff(c_89199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_203, c_89140])).
% 35.47/26.79  tff(c_89200, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 35.47/26.79  tff(c_34, plain, (![C_22]: (r2_hidden(C_22, k1_tarski(C_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 35.47/26.79  tff(c_89201, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 35.47/26.79  tff(c_62, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.47/26.79  tff(c_89247, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_89201, c_62])).
% 35.47/26.79  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.47/26.79  tff(c_89255, plain, (![D_12288]: (~r2_hidden(D_12288, k1_tarski('#skF_8')) | ~r2_hidden(D_12288, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_89247, c_6])).
% 35.47/26.79  tff(c_89259, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_89255])).
% 35.47/26.79  tff(c_89263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89200, c_89259])).
% 35.47/26.79  tff(c_89264, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 35.47/26.79  tff(c_89265, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 35.47/26.79  tff(c_64, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.47/26.79  tff(c_89280, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_89265, c_64])).
% 35.47/26.79  tff(c_89292, plain, (![D_12297]: (~r2_hidden(D_12297, k1_tarski('#skF_8')) | ~r2_hidden(D_12297, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_89280, c_6])).
% 35.47/26.79  tff(c_89296, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_89292])).
% 35.47/26.79  tff(c_89300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89264, c_89296])).
% 35.47/26.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.47/26.79  
% 35.47/26.79  Inference rules
% 35.47/26.79  ----------------------
% 35.47/26.79  #Ref     : 0
% 35.47/26.79  #Sup     : 22855
% 35.47/26.79  #Fact    : 10
% 35.47/26.79  #Define  : 0
% 35.47/26.79  #Split   : 4
% 35.47/26.79  #Chain   : 0
% 35.47/26.79  #Close   : 0
% 35.47/26.79  
% 35.47/26.79  Ordering : KBO
% 35.47/26.79  
% 35.47/26.79  Simplification rules
% 35.47/26.79  ----------------------
% 35.47/26.79  #Subsume      : 1729
% 35.47/26.79  #Demod        : 32720
% 35.47/26.79  #Tautology    : 7010
% 35.47/26.79  #SimpNegUnit  : 2
% 35.47/26.79  #BackRed      : 2
% 35.47/26.79  
% 35.47/26.79  #Partial instantiations: 4536
% 35.47/26.79  #Strategies tried      : 1
% 35.47/26.79  
% 35.47/26.79  Timing (in seconds)
% 35.47/26.79  ----------------------
% 35.47/26.80  Preprocessing        : 0.32
% 35.47/26.80  Parsing              : 0.16
% 35.47/26.80  CNF conversion       : 0.02
% 35.47/26.80  Main loop            : 25.72
% 35.47/26.80  Inferencing          : 2.33
% 35.47/26.80  Reduction            : 19.52
% 35.47/26.80  Demodulation         : 18.87
% 35.47/26.80  BG Simplification    : 0.42
% 35.47/26.80  Subsumption          : 2.71
% 35.47/26.80  Abstraction          : 0.69
% 35.47/26.80  MUC search           : 0.00
% 35.47/26.80  Cooper               : 0.00
% 35.47/26.80  Total                : 26.07
% 35.47/26.80  Index Insertion      : 0.00
% 35.47/26.80  Index Deletion       : 0.00
% 35.47/26.80  Index Matching       : 0.00
% 35.47/26.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
