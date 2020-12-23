%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 124 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 224 expanded)
%              Number of equality atoms :   14 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9')
    | k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,(
    k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_123,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_60)
      | r2_hidden('#skF_2'(A_59,B_60),A_59)
      | B_60 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_141,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_60),B_60)
      | k1_xboole_0 = B_60 ) ),
    inference(resolution,[status(thm)],[c_123,c_55])).

tff(c_184,plain,(
    ! [A_68,C_69] :
      ( r2_hidden(k4_tarski('#skF_7'(A_68,k2_relat_1(A_68),C_69),C_69),A_68)
      | ~ r2_hidden(C_69,k2_relat_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_199,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_184,c_55])).

tff(c_234,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_199])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_235,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1,k2_relat_1(k1_xboole_0)),A_1)
      | k2_relat_1(k1_xboole_0) = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_502,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1,k1_xboole_0),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_235])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_8'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k10_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_480,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden('#skF_8'(A_90,B_91,C_92),k2_relat_1(C_92))
      | ~ r2_hidden(A_90,k10_relat_1(C_92,B_91))
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,
    ( k10_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_48])).

tff(c_73,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,B_47)
      | ~ r2_hidden(C_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [C_48] :
      ( ~ r2_hidden(C_48,'#skF_9')
      | ~ r2_hidden(C_48,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_58,c_73])).

tff(c_488,plain,(
    ! [A_90,B_91] :
      ( ~ r2_hidden('#skF_8'(A_90,B_91,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_90,k10_relat_1('#skF_10',B_91))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_480,c_81])).

tff(c_828,plain,(
    ! [A_112,B_113] :
      ( ~ r2_hidden('#skF_8'(A_112,B_113,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_112,k10_relat_1('#skF_10',B_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_488])).

tff(c_832,plain,(
    ! [A_31] :
      ( ~ r2_hidden(A_31,k10_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_828])).

tff(c_836,plain,(
    ! [A_114] : ~ r2_hidden(A_114,k10_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_832])).

tff(c_840,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_502,c_836])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_840])).

tff(c_885,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_886,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_20,plain,(
    ! [A_12,C_27] :
      ( r2_hidden(k4_tarski('#skF_7'(A_12,k2_relat_1(A_12),C_27),C_27),A_12)
      | ~ r2_hidden(C_27,k2_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1453,plain,(
    ! [A_175,C_176,B_177,D_178] :
      ( r2_hidden(A_175,k10_relat_1(C_176,B_177))
      | ~ r2_hidden(D_178,B_177)
      | ~ r2_hidden(k4_tarski(A_175,D_178),C_176)
      | ~ r2_hidden(D_178,k2_relat_1(C_176))
      | ~ v1_relat_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2518,plain,(
    ! [A_237,C_238,B_239,A_240] :
      ( r2_hidden(A_237,k10_relat_1(C_238,B_239))
      | ~ r2_hidden(k4_tarski(A_237,'#skF_3'(A_240,B_239)),C_238)
      | ~ r2_hidden('#skF_3'(A_240,B_239),k2_relat_1(C_238))
      | ~ v1_relat_1(C_238)
      | r1_xboole_0(A_240,B_239) ) ),
    inference(resolution,[status(thm)],[c_12,c_1453])).

tff(c_17643,plain,(
    ! [A_4295,A_4296,B_4297] :
      ( r2_hidden('#skF_7'(A_4295,k2_relat_1(A_4295),'#skF_3'(A_4296,B_4297)),k10_relat_1(A_4295,B_4297))
      | ~ v1_relat_1(A_4295)
      | r1_xboole_0(A_4296,B_4297)
      | ~ r2_hidden('#skF_3'(A_4296,B_4297),k2_relat_1(A_4295)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2518])).

tff(c_17841,plain,(
    ! [A_4296] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_3'(A_4296,'#skF_9')),k1_xboole_0)
      | ~ v1_relat_1('#skF_10')
      | r1_xboole_0(A_4296,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4296,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_17643])).

tff(c_17863,plain,(
    ! [A_4296] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_3'(A_4296,'#skF_9')),k1_xboole_0)
      | r1_xboole_0(A_4296,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4296,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17841])).

tff(c_17865,plain,(
    ! [A_4322] :
      ( r1_xboole_0(A_4322,'#skF_9')
      | ~ r2_hidden('#skF_3'(A_4322,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_17863])).

tff(c_17872,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_17865])).

tff(c_17876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_885,c_885,c_17872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.47/4.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.18  
% 11.47/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.18  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 11.47/4.18  
% 11.47/4.18  %Foreground sorts:
% 11.47/4.18  
% 11.47/4.18  
% 11.47/4.18  %Background operators:
% 11.47/4.18  
% 11.47/4.18  
% 11.47/4.18  %Foreground operators:
% 11.47/4.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.47/4.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.47/4.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.47/4.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.47/4.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.47/4.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.47/4.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.47/4.18  tff('#skF_10', type, '#skF_10': $i).
% 11.47/4.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.47/4.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.47/4.18  tff('#skF_9', type, '#skF_9': $i).
% 11.47/4.18  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 11.47/4.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.47/4.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.47/4.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.47/4.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.47/4.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.47/4.18  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 11.47/4.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.47/4.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.47/4.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.47/4.18  
% 11.78/4.19  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 11.78/4.19  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 11.78/4.19  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.78/4.19  tff(f_57, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 11.78/4.19  tff(f_65, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 11.78/4.19  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 11.78/4.19  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.78/4.19  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9') | k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.78/4.19  tff(c_57, plain, (k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 11.78/4.19  tff(c_123, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), B_60) | r2_hidden('#skF_2'(A_59, B_60), A_59) | B_60=A_59)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.19  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.78/4.19  tff(c_50, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.78/4.19  tff(c_55, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_50])).
% 11.78/4.19  tff(c_141, plain, (![B_60]: (r2_hidden('#skF_1'(k1_xboole_0, B_60), B_60) | k1_xboole_0=B_60)), inference(resolution, [status(thm)], [c_123, c_55])).
% 11.78/4.19  tff(c_184, plain, (![A_68, C_69]: (r2_hidden(k4_tarski('#skF_7'(A_68, k2_relat_1(A_68), C_69), C_69), A_68) | ~r2_hidden(C_69, k2_relat_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.78/4.19  tff(c_199, plain, (![C_70]: (~r2_hidden(C_70, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_184, c_55])).
% 11.78/4.19  tff(c_234, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_199])).
% 11.78/4.19  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.19  tff(c_235, plain, (![A_1]: (r2_hidden('#skF_2'(A_1, k2_relat_1(k1_xboole_0)), A_1) | k2_relat_1(k1_xboole_0)=A_1)), inference(resolution, [status(thm)], [c_8, c_199])).
% 11.78/4.19  tff(c_502, plain, (![A_1]: (r2_hidden('#skF_2'(A_1, k1_xboole_0), A_1) | k1_xboole_0=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_235])).
% 11.78/4.19  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.78/4.19  tff(c_34, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_8'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k10_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.78/4.19  tff(c_480, plain, (![A_90, B_91, C_92]: (r2_hidden('#skF_8'(A_90, B_91, C_92), k2_relat_1(C_92)) | ~r2_hidden(A_90, k10_relat_1(C_92, B_91)) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.78/4.19  tff(c_48, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.78/4.19  tff(c_58, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_57, c_48])).
% 11.78/4.19  tff(c_73, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, B_47) | ~r2_hidden(C_48, A_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.78/4.19  tff(c_81, plain, (![C_48]: (~r2_hidden(C_48, '#skF_9') | ~r2_hidden(C_48, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_58, c_73])).
% 11.78/4.19  tff(c_488, plain, (![A_90, B_91]: (~r2_hidden('#skF_8'(A_90, B_91, '#skF_10'), '#skF_9') | ~r2_hidden(A_90, k10_relat_1('#skF_10', B_91)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_480, c_81])).
% 11.78/4.19  tff(c_828, plain, (![A_112, B_113]: (~r2_hidden('#skF_8'(A_112, B_113, '#skF_10'), '#skF_9') | ~r2_hidden(A_112, k10_relat_1('#skF_10', B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_488])).
% 11.78/4.19  tff(c_832, plain, (![A_31]: (~r2_hidden(A_31, k10_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_828])).
% 11.78/4.19  tff(c_836, plain, (![A_114]: (~r2_hidden(A_114, k10_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_832])).
% 11.78/4.19  tff(c_840, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_502, c_836])).
% 11.78/4.19  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_840])).
% 11.78/4.19  tff(c_885, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_42])).
% 11.78/4.19  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.78/4.19  tff(c_886, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 11.78/4.19  tff(c_20, plain, (![A_12, C_27]: (r2_hidden(k4_tarski('#skF_7'(A_12, k2_relat_1(A_12), C_27), C_27), A_12) | ~r2_hidden(C_27, k2_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.78/4.19  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.78/4.19  tff(c_1453, plain, (![A_175, C_176, B_177, D_178]: (r2_hidden(A_175, k10_relat_1(C_176, B_177)) | ~r2_hidden(D_178, B_177) | ~r2_hidden(k4_tarski(A_175, D_178), C_176) | ~r2_hidden(D_178, k2_relat_1(C_176)) | ~v1_relat_1(C_176))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.78/4.19  tff(c_2518, plain, (![A_237, C_238, B_239, A_240]: (r2_hidden(A_237, k10_relat_1(C_238, B_239)) | ~r2_hidden(k4_tarski(A_237, '#skF_3'(A_240, B_239)), C_238) | ~r2_hidden('#skF_3'(A_240, B_239), k2_relat_1(C_238)) | ~v1_relat_1(C_238) | r1_xboole_0(A_240, B_239))), inference(resolution, [status(thm)], [c_12, c_1453])).
% 11.78/4.19  tff(c_17643, plain, (![A_4295, A_4296, B_4297]: (r2_hidden('#skF_7'(A_4295, k2_relat_1(A_4295), '#skF_3'(A_4296, B_4297)), k10_relat_1(A_4295, B_4297)) | ~v1_relat_1(A_4295) | r1_xboole_0(A_4296, B_4297) | ~r2_hidden('#skF_3'(A_4296, B_4297), k2_relat_1(A_4295)))), inference(resolution, [status(thm)], [c_20, c_2518])).
% 11.78/4.19  tff(c_17841, plain, (![A_4296]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_3'(A_4296, '#skF_9')), k1_xboole_0) | ~v1_relat_1('#skF_10') | r1_xboole_0(A_4296, '#skF_9') | ~r2_hidden('#skF_3'(A_4296, '#skF_9'), k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_886, c_17643])).
% 11.78/4.19  tff(c_17863, plain, (![A_4296]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_3'(A_4296, '#skF_9')), k1_xboole_0) | r1_xboole_0(A_4296, '#skF_9') | ~r2_hidden('#skF_3'(A_4296, '#skF_9'), k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17841])).
% 11.78/4.19  tff(c_17865, plain, (![A_4322]: (r1_xboole_0(A_4322, '#skF_9') | ~r2_hidden('#skF_3'(A_4322, '#skF_9'), k2_relat_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_55, c_17863])).
% 11.78/4.19  tff(c_17872, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_14, c_17865])).
% 11.78/4.19  tff(c_17876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_885, c_885, c_17872])).
% 11.78/4.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/4.19  
% 11.78/4.19  Inference rules
% 11.78/4.19  ----------------------
% 11.78/4.19  #Ref     : 0
% 11.78/4.19  #Sup     : 3595
% 11.78/4.19  #Fact    : 0
% 11.78/4.19  #Define  : 0
% 11.78/4.19  #Split   : 8
% 11.78/4.19  #Chain   : 0
% 11.78/4.19  #Close   : 0
% 11.78/4.19  
% 11.78/4.19  Ordering : KBO
% 11.78/4.19  
% 11.78/4.19  Simplification rules
% 11.78/4.19  ----------------------
% 11.78/4.19  #Subsume      : 1474
% 11.78/4.19  #Demod        : 1269
% 11.78/4.19  #Tautology    : 432
% 11.78/4.19  #SimpNegUnit  : 168
% 11.78/4.19  #BackRed      : 2
% 11.78/4.19  
% 11.78/4.19  #Partial instantiations: 2385
% 11.78/4.19  #Strategies tried      : 1
% 11.78/4.19  
% 11.78/4.19  Timing (in seconds)
% 11.78/4.19  ----------------------
% 11.78/4.20  Preprocessing        : 0.31
% 11.78/4.20  Parsing              : 0.17
% 11.78/4.20  CNF conversion       : 0.03
% 11.78/4.20  Main loop            : 3.08
% 11.78/4.20  Inferencing          : 0.70
% 11.78/4.20  Reduction            : 0.52
% 11.78/4.20  Demodulation         : 0.31
% 11.78/4.20  BG Simplification    : 0.07
% 11.78/4.20  Subsumption          : 1.68
% 11.78/4.20  Abstraction          : 0.09
% 11.78/4.20  MUC search           : 0.00
% 11.78/4.20  Cooper               : 0.00
% 11.78/4.20  Total                : 3.43
% 11.78/4.20  Index Insertion      : 0.00
% 11.78/4.20  Index Deletion       : 0.00
% 11.78/4.20  Index Matching       : 0.00
% 11.78/4.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
