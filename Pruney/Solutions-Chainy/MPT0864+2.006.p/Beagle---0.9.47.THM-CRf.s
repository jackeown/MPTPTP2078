%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 171 expanded)
%              Number of equality atoms :   52 ( 105 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_596,plain,(
    ! [A_108,C_109,B_110] :
      ( r2_hidden(k2_mcart_1(A_108),C_109)
      | ~ r2_hidden(A_108,k2_zfmisc_1(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_625,plain,(
    ! [A_115,B_116] :
      ( r2_hidden(k2_mcart_1(A_115),B_116)
      | ~ r2_hidden(A_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_596])).

tff(c_28,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_735,plain,(
    ! [B_130,A_131] :
      ( ~ r1_tarski(B_130,k2_mcart_1(A_131))
      | ~ r2_hidden(A_131,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_625,c_28])).

tff(c_745,plain,(
    ! [A_131] : ~ r2_hidden(A_131,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_735])).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k1_mcart_1(A_51),B_52)
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_208,plain,(
    ! [A_54,A_55] :
      ( r2_hidden(k1_mcart_1(A_54),A_55)
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_199])).

tff(c_332,plain,(
    ! [A_70,A_71] :
      ( ~ r1_tarski(A_70,k1_mcart_1(A_71))
      | ~ r2_hidden(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_208,c_28])).

tff(c_342,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_46,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_76,plain,(
    ! [A_34,B_35] : k2_mcart_1(k4_tarski(A_34,B_35)) = B_35 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,
    ( '#skF_6' = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_44])).

tff(c_114,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_101,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_101])).

tff(c_119,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_110])).

tff(c_124,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_46])).

tff(c_147,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_3'(A_41),A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_3] :
      ( '#skF_3'(k1_tarski(A_3)) = A_3
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_147,c_8])).

tff(c_10,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_266,plain,(
    ! [C_62,A_63,D_64] :
      ( ~ r2_hidden(C_62,A_63)
      | k4_tarski(C_62,D_64) != '#skF_3'(A_63)
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_470,plain,(
    ! [C_90,D_91] :
      ( k4_tarski(C_90,D_91) != '#skF_3'(k1_tarski(C_90))
      | k1_tarski(C_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_266])).

tff(c_478,plain,(
    ! [A_94,D_95] :
      ( k4_tarski(A_94,D_95) != A_94
      | k1_tarski(A_94) = k1_xboole_0
      | k1_tarski(A_94) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_470])).

tff(c_482,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_478])).

tff(c_501,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_10])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_501])).

tff(c_509,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_517,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_46])).

tff(c_550,plain,(
    ! [A_101] :
      ( r2_hidden('#skF_3'(A_101),A_101)
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_558,plain,(
    ! [A_3] :
      ( '#skF_3'(k1_tarski(A_3)) = A_3
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_550,c_8])).

tff(c_660,plain,(
    ! [D_119,A_120,C_121] :
      ( ~ r2_hidden(D_119,A_120)
      | k4_tarski(C_121,D_119) != '#skF_3'(A_120)
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_860,plain,(
    ! [C_147,C_148] :
      ( k4_tarski(C_147,C_148) != '#skF_3'(k1_tarski(C_148))
      | k1_tarski(C_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_660])).

tff(c_868,plain,(
    ! [C_151,A_152] :
      ( k4_tarski(C_151,A_152) != A_152
      | k1_tarski(A_152) = k1_xboole_0
      | k1_tarski(A_152) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_860])).

tff(c_872,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_868])).

tff(c_891,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_10])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.46  
% 2.85/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.46  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.85/1.46  
% 2.85/1.46  %Foreground sorts:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Background operators:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Foreground operators:
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.85/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.85/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.46  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.85/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.46  
% 2.85/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.48  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.85/1.48  tff(f_57, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.85/1.48  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.85/1.48  tff(f_87, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.85/1.48  tff(f_61, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.85/1.48  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.85/1.48  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.85/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.48  tff(c_26, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.48  tff(c_596, plain, (![A_108, C_109, B_110]: (r2_hidden(k2_mcart_1(A_108), C_109) | ~r2_hidden(A_108, k2_zfmisc_1(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.48  tff(c_625, plain, (![A_115, B_116]: (r2_hidden(k2_mcart_1(A_115), B_116) | ~r2_hidden(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_596])).
% 2.85/1.48  tff(c_28, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.85/1.48  tff(c_735, plain, (![B_130, A_131]: (~r1_tarski(B_130, k2_mcart_1(A_131)) | ~r2_hidden(A_131, k1_xboole_0))), inference(resolution, [status(thm)], [c_625, c_28])).
% 2.85/1.48  tff(c_745, plain, (![A_131]: (~r2_hidden(A_131, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_735])).
% 2.85/1.48  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.48  tff(c_199, plain, (![A_51, B_52, C_53]: (r2_hidden(k1_mcart_1(A_51), B_52) | ~r2_hidden(A_51, k2_zfmisc_1(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.48  tff(c_208, plain, (![A_54, A_55]: (r2_hidden(k1_mcart_1(A_54), A_55) | ~r2_hidden(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_199])).
% 2.85/1.48  tff(c_332, plain, (![A_70, A_71]: (~r1_tarski(A_70, k1_mcart_1(A_71)) | ~r2_hidden(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_208, c_28])).
% 2.85/1.48  tff(c_342, plain, (![A_71]: (~r2_hidden(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_332])).
% 2.85/1.48  tff(c_46, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.85/1.48  tff(c_76, plain, (![A_34, B_35]: (k2_mcart_1(k4_tarski(A_34, B_35))=B_35)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.85/1.48  tff(c_85, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_46, c_76])).
% 2.85/1.48  tff(c_44, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.85/1.48  tff(c_113, plain, ('#skF_6'='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_44])).
% 2.85/1.48  tff(c_114, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_113])).
% 2.85/1.48  tff(c_101, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.85/1.48  tff(c_110, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_46, c_101])).
% 2.85/1.48  tff(c_119, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_110])).
% 2.85/1.48  tff(c_124, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_46])).
% 2.85/1.48  tff(c_147, plain, (![A_41]: (r2_hidden('#skF_3'(A_41), A_41) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.48  tff(c_8, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.48  tff(c_152, plain, (![A_3]: ('#skF_3'(k1_tarski(A_3))=A_3 | k1_tarski(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_147, c_8])).
% 2.85/1.48  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.48  tff(c_266, plain, (![C_62, A_63, D_64]: (~r2_hidden(C_62, A_63) | k4_tarski(C_62, D_64)!='#skF_3'(A_63) | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.48  tff(c_470, plain, (![C_90, D_91]: (k4_tarski(C_90, D_91)!='#skF_3'(k1_tarski(C_90)) | k1_tarski(C_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_266])).
% 2.85/1.48  tff(c_478, plain, (![A_94, D_95]: (k4_tarski(A_94, D_95)!=A_94 | k1_tarski(A_94)=k1_xboole_0 | k1_tarski(A_94)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_470])).
% 2.85/1.48  tff(c_482, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124, c_478])).
% 2.85/1.48  tff(c_501, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_482, c_10])).
% 2.85/1.48  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_501])).
% 2.85/1.48  tff(c_509, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 2.85/1.48  tff(c_517, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_509, c_46])).
% 2.85/1.48  tff(c_550, plain, (![A_101]: (r2_hidden('#skF_3'(A_101), A_101) | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.48  tff(c_558, plain, (![A_3]: ('#skF_3'(k1_tarski(A_3))=A_3 | k1_tarski(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_550, c_8])).
% 2.85/1.48  tff(c_660, plain, (![D_119, A_120, C_121]: (~r2_hidden(D_119, A_120) | k4_tarski(C_121, D_119)!='#skF_3'(A_120) | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.48  tff(c_860, plain, (![C_147, C_148]: (k4_tarski(C_147, C_148)!='#skF_3'(k1_tarski(C_148)) | k1_tarski(C_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_660])).
% 2.85/1.48  tff(c_868, plain, (![C_151, A_152]: (k4_tarski(C_151, A_152)!=A_152 | k1_tarski(A_152)=k1_xboole_0 | k1_tarski(A_152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_558, c_860])).
% 2.85/1.48  tff(c_872, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_517, c_868])).
% 2.85/1.48  tff(c_891, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_872, c_10])).
% 2.85/1.48  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_745, c_891])).
% 2.85/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.48  
% 2.85/1.48  Inference rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Ref     : 0
% 2.85/1.48  #Sup     : 216
% 2.85/1.48  #Fact    : 0
% 2.85/1.48  #Define  : 0
% 2.85/1.48  #Split   : 3
% 2.85/1.48  #Chain   : 0
% 2.85/1.48  #Close   : 0
% 2.85/1.48  
% 2.85/1.48  Ordering : KBO
% 2.85/1.48  
% 2.85/1.48  Simplification rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Subsume      : 66
% 2.85/1.48  #Demod        : 27
% 2.85/1.48  #Tautology    : 79
% 2.85/1.48  #SimpNegUnit  : 6
% 2.85/1.48  #BackRed      : 4
% 2.85/1.48  
% 2.85/1.48  #Partial instantiations: 0
% 2.85/1.48  #Strategies tried      : 1
% 2.85/1.48  
% 2.85/1.48  Timing (in seconds)
% 2.85/1.48  ----------------------
% 2.85/1.48  Preprocessing        : 0.33
% 2.85/1.48  Parsing              : 0.17
% 2.85/1.48  CNF conversion       : 0.02
% 2.85/1.48  Main loop            : 0.33
% 2.85/1.48  Inferencing          : 0.13
% 2.85/1.48  Reduction            : 0.09
% 2.85/1.48  Demodulation         : 0.06
% 2.85/1.48  BG Simplification    : 0.02
% 2.85/1.48  Subsumption          : 0.06
% 2.96/1.48  Abstraction          : 0.02
% 2.96/1.48  MUC search           : 0.00
% 2.96/1.48  Cooper               : 0.00
% 2.96/1.48  Total                : 0.69
% 2.96/1.48  Index Insertion      : 0.00
% 2.96/1.48  Index Deletion       : 0.00
% 2.96/1.48  Index Matching       : 0.00
% 2.96/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
