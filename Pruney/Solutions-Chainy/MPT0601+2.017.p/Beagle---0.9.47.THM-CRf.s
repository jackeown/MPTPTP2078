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
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 105 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_110,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2799,plain,(
    ! [B_247,A_248] :
      ( ~ r2_hidden(B_247,A_248)
      | k4_xboole_0(A_248,k1_tarski(B_247)) != A_248 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2812,plain,(
    ! [B_247] : ~ r2_hidden(B_247,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2799])).

tff(c_74,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_130,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1482,plain,(
    ! [A_186,B_187] :
      ( r2_hidden(k4_tarski('#skF_2'(A_186,B_187),'#skF_3'(A_186,B_187)),A_186)
      | r2_hidden('#skF_4'(A_186,B_187),B_187)
      | k1_relat_1(A_186) = B_187 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_311,plain,(
    ! [B_86,A_87] :
      ( ~ r2_hidden(B_86,A_87)
      | k4_xboole_0(A_87,k1_tarski(B_86)) != A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_324,plain,(
    ! [B_86] : ~ r2_hidden(B_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_1500,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_187),B_187)
      | k1_relat_1(k1_xboole_0) = B_187 ) ),
    inference(resolution,[status(thm)],[c_1482,c_324])).

tff(c_1506,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_187),B_187)
      | k1_xboole_0 = B_187 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1500])).

tff(c_1136,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden(k4_tarski(A_155,B_156),C_157)
      | ~ r2_hidden(B_156,k11_relat_1(C_157,A_155))
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    ! [C_45,A_30,D_48] :
      ( r2_hidden(C_45,k1_relat_1(A_30))
      | ~ r2_hidden(k4_tarski(C_45,D_48),A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2235,plain,(
    ! [A_210,C_211,B_212] :
      ( r2_hidden(A_210,k1_relat_1(C_211))
      | ~ r2_hidden(B_212,k11_relat_1(C_211,A_210))
      | ~ v1_relat_1(C_211) ) ),
    inference(resolution,[status(thm)],[c_1136,c_36])).

tff(c_2499,plain,(
    ! [A_219,C_220] :
      ( r2_hidden(A_219,k1_relat_1(C_220))
      | ~ v1_relat_1(C_220)
      | k11_relat_1(C_220,A_219) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1506,c_2235])).

tff(c_68,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_179,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_68])).

tff(c_2528,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2499,c_179])).

tff(c_2550,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2528])).

tff(c_2552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2550])).

tff(c_2553,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2554,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_3639,plain,(
    ! [C_315,A_316] :
      ( r2_hidden(k4_tarski(C_315,'#skF_5'(A_316,k1_relat_1(A_316),C_315)),A_316)
      | ~ r2_hidden(C_315,k1_relat_1(A_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [B_56,C_57,A_55] :
      ( r2_hidden(B_56,k11_relat_1(C_57,A_55))
      | ~ r2_hidden(k4_tarski(A_55,B_56),C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6578,plain,(
    ! [A_414,C_415] :
      ( r2_hidden('#skF_5'(A_414,k1_relat_1(A_414),C_415),k11_relat_1(A_414,C_415))
      | ~ v1_relat_1(A_414)
      | ~ r2_hidden(C_415,k1_relat_1(A_414)) ) ),
    inference(resolution,[status(thm)],[c_3639,c_56])).

tff(c_6602,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2554,c_6578])).

tff(c_6612,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2553,c_66,c_6602])).

tff(c_6614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2812,c_6612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.07  
% 5.29/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.07  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 5.67/2.07  
% 5.67/2.07  %Foreground sorts:
% 5.67/2.07  
% 5.67/2.07  
% 5.67/2.07  %Background operators:
% 5.67/2.07  
% 5.67/2.07  
% 5.67/2.07  %Foreground operators:
% 5.67/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.67/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.67/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.67/2.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.67/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.67/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.67/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.67/2.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.67/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.67/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.67/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.67/2.07  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.67/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.67/2.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.67/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.67/2.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.67/2.07  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.67/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.67/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.67/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.67/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.67/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.67/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.67/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.67/2.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.67/2.07  
% 5.67/2.08  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.67/2.08  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.67/2.08  tff(f_124, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 5.67/2.08  tff(f_110, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.67/2.08  tff(f_87, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.67/2.08  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 5.67/2.08  tff(c_12, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.08  tff(c_2799, plain, (![B_247, A_248]: (~r2_hidden(B_247, A_248) | k4_xboole_0(A_248, k1_tarski(B_247))!=A_248)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.67/2.08  tff(c_2812, plain, (![B_247]: (~r2_hidden(B_247, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2799])).
% 5.67/2.08  tff(c_74, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.67/2.08  tff(c_130, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 5.67/2.08  tff(c_66, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.67/2.08  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.67/2.08  tff(c_1482, plain, (![A_186, B_187]: (r2_hidden(k4_tarski('#skF_2'(A_186, B_187), '#skF_3'(A_186, B_187)), A_186) | r2_hidden('#skF_4'(A_186, B_187), B_187) | k1_relat_1(A_186)=B_187)), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.67/2.08  tff(c_311, plain, (![B_86, A_87]: (~r2_hidden(B_86, A_87) | k4_xboole_0(A_87, k1_tarski(B_86))!=A_87)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.67/2.08  tff(c_324, plain, (![B_86]: (~r2_hidden(B_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 5.67/2.08  tff(c_1500, plain, (![B_187]: (r2_hidden('#skF_4'(k1_xboole_0, B_187), B_187) | k1_relat_1(k1_xboole_0)=B_187)), inference(resolution, [status(thm)], [c_1482, c_324])).
% 5.67/2.08  tff(c_1506, plain, (![B_187]: (r2_hidden('#skF_4'(k1_xboole_0, B_187), B_187) | k1_xboole_0=B_187)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1500])).
% 5.67/2.08  tff(c_1136, plain, (![A_155, B_156, C_157]: (r2_hidden(k4_tarski(A_155, B_156), C_157) | ~r2_hidden(B_156, k11_relat_1(C_157, A_155)) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.67/2.08  tff(c_36, plain, (![C_45, A_30, D_48]: (r2_hidden(C_45, k1_relat_1(A_30)) | ~r2_hidden(k4_tarski(C_45, D_48), A_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.67/2.08  tff(c_2235, plain, (![A_210, C_211, B_212]: (r2_hidden(A_210, k1_relat_1(C_211)) | ~r2_hidden(B_212, k11_relat_1(C_211, A_210)) | ~v1_relat_1(C_211))), inference(resolution, [status(thm)], [c_1136, c_36])).
% 5.67/2.08  tff(c_2499, plain, (![A_219, C_220]: (r2_hidden(A_219, k1_relat_1(C_220)) | ~v1_relat_1(C_220) | k11_relat_1(C_220, A_219)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1506, c_2235])).
% 5.67/2.08  tff(c_68, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.67/2.08  tff(c_179, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_130, c_68])).
% 5.67/2.08  tff(c_2528, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2499, c_179])).
% 5.67/2.08  tff(c_2550, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2528])).
% 5.67/2.08  tff(c_2552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_2550])).
% 5.67/2.08  tff(c_2553, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_74])).
% 5.67/2.08  tff(c_2554, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 5.67/2.08  tff(c_3639, plain, (![C_315, A_316]: (r2_hidden(k4_tarski(C_315, '#skF_5'(A_316, k1_relat_1(A_316), C_315)), A_316) | ~r2_hidden(C_315, k1_relat_1(A_316)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.67/2.08  tff(c_56, plain, (![B_56, C_57, A_55]: (r2_hidden(B_56, k11_relat_1(C_57, A_55)) | ~r2_hidden(k4_tarski(A_55, B_56), C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.67/2.08  tff(c_6578, plain, (![A_414, C_415]: (r2_hidden('#skF_5'(A_414, k1_relat_1(A_414), C_415), k11_relat_1(A_414, C_415)) | ~v1_relat_1(A_414) | ~r2_hidden(C_415, k1_relat_1(A_414)))), inference(resolution, [status(thm)], [c_3639, c_56])).
% 5.67/2.08  tff(c_6602, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2554, c_6578])).
% 5.67/2.08  tff(c_6612, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2553, c_66, c_6602])).
% 5.67/2.08  tff(c_6614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2812, c_6612])).
% 5.67/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.08  
% 5.67/2.08  Inference rules
% 5.67/2.08  ----------------------
% 5.67/2.08  #Ref     : 0
% 5.67/2.08  #Sup     : 1564
% 5.67/2.08  #Fact    : 0
% 5.67/2.08  #Define  : 0
% 5.67/2.08  #Split   : 3
% 5.67/2.08  #Chain   : 0
% 5.67/2.08  #Close   : 0
% 5.67/2.08  
% 5.67/2.08  Ordering : KBO
% 5.67/2.08  
% 5.67/2.08  Simplification rules
% 5.67/2.08  ----------------------
% 5.67/2.08  #Subsume      : 221
% 5.67/2.08  #Demod        : 1200
% 5.67/2.08  #Tautology    : 763
% 5.67/2.08  #SimpNegUnit  : 71
% 5.67/2.08  #BackRed      : 2
% 5.67/2.08  
% 5.67/2.08  #Partial instantiations: 0
% 5.67/2.08  #Strategies tried      : 1
% 5.67/2.08  
% 5.67/2.08  Timing (in seconds)
% 5.67/2.08  ----------------------
% 5.67/2.08  Preprocessing        : 0.33
% 5.67/2.08  Parsing              : 0.18
% 5.67/2.08  CNF conversion       : 0.02
% 5.67/2.08  Main loop            : 0.98
% 5.67/2.08  Inferencing          : 0.33
% 5.67/2.08  Reduction            : 0.37
% 5.67/2.08  Demodulation         : 0.28
% 5.67/2.08  BG Simplification    : 0.04
% 5.67/2.08  Subsumption          : 0.17
% 5.67/2.09  Abstraction          : 0.04
% 5.67/2.09  MUC search           : 0.00
% 5.67/2.09  Cooper               : 0.00
% 5.67/2.09  Total                : 1.34
% 5.67/2.09  Index Insertion      : 0.00
% 5.67/2.09  Index Deletion       : 0.00
% 5.67/2.09  Index Matching       : 0.00
% 5.67/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
