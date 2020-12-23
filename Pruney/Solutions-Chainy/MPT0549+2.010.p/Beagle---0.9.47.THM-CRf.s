%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 10.75s
% Output     : CNFRefutation 10.75s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 125 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_50,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | k9_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_96,plain,(
    k9_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,
    ( k9_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_112,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_56])).

tff(c_183,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_189,plain,
    ( k7_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_112,c_183])).

tff(c_200,plain,(
    k7_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_189])).

tff(c_38,plain,(
    ! [B_38,A_37] :
      ( k2_relat_1(k7_relat_1(B_38,A_37)) = k9_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_208,plain,
    ( k9_relat_1('#skF_8','#skF_7') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_38])).

tff(c_212,plain,(
    k9_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_208])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_212])).

tff(c_215,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_216,plain,(
    k9_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_18,plain,(
    ! [C_27,A_12] :
      ( r2_hidden(k4_tarski(C_27,'#skF_5'(A_12,k1_relat_1(A_12),C_27)),A_12)
      | ~ r2_hidden(C_27,k1_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_974,plain,(
    ! [A_151,C_152,B_153,D_154] :
      ( r2_hidden(A_151,k9_relat_1(C_152,B_153))
      | ~ r2_hidden(D_154,B_153)
      | ~ r2_hidden(k4_tarski(D_154,A_151),C_152)
      | ~ r2_hidden(D_154,k1_relat_1(C_152))
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2084,plain,(
    ! [A_220,C_221,A_222,B_223] :
      ( r2_hidden(A_220,k9_relat_1(C_221,A_222))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_222,B_223),A_220),C_221)
      | ~ r2_hidden('#skF_1'(A_222,B_223),k1_relat_1(C_221))
      | ~ v1_relat_1(C_221)
      | r1_xboole_0(A_222,B_223) ) ),
    inference(resolution,[status(thm)],[c_8,c_974])).

tff(c_14546,plain,(
    ! [A_555,A_556,B_557] :
      ( r2_hidden('#skF_5'(A_555,k1_relat_1(A_555),'#skF_1'(A_556,B_557)),k9_relat_1(A_555,A_556))
      | ~ v1_relat_1(A_555)
      | r1_xboole_0(A_556,B_557)
      | ~ r2_hidden('#skF_1'(A_556,B_557),k1_relat_1(A_555)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2084])).

tff(c_14682,plain,(
    ! [B_557] :
      ( r2_hidden('#skF_5'('#skF_8',k1_relat_1('#skF_8'),'#skF_1'('#skF_7',B_557)),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0('#skF_7',B_557)
      | ~ r2_hidden('#skF_1'('#skF_7',B_557),k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_14546])).

tff(c_14711,plain,(
    ! [B_557] :
      ( r2_hidden('#skF_5'('#skF_8',k1_relat_1('#skF_8'),'#skF_1'('#skF_7',B_557)),k1_xboole_0)
      | r1_xboole_0('#skF_7',B_557)
      | ~ r2_hidden('#skF_1'('#skF_7',B_557),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14682])).

tff(c_14714,plain,(
    ! [B_558] :
      ( r1_xboole_0('#skF_7',B_558)
      | ~ r2_hidden('#skF_1'('#skF_7',B_558),k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_14711])).

tff(c_14719,plain,(
    r1_xboole_0('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_14714])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14723,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_14719,c_2])).

tff(c_14728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_14723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.75/3.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.75/3.73  
% 10.75/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.75/3.73  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 10.75/3.73  
% 10.75/3.73  %Foreground sorts:
% 10.75/3.73  
% 10.75/3.73  
% 10.75/3.73  %Background operators:
% 10.75/3.73  
% 10.75/3.73  
% 10.75/3.73  %Foreground operators:
% 10.75/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.75/3.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.75/3.73  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.75/3.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.75/3.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.75/3.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.75/3.73  tff('#skF_7', type, '#skF_7': $i).
% 10.75/3.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.75/3.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.75/3.73  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.75/3.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.75/3.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.75/3.73  tff('#skF_8', type, '#skF_8': $i).
% 10.75/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.75/3.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.75/3.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.75/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.75/3.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.75/3.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.75/3.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.75/3.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.75/3.73  
% 10.75/3.74  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 10.75/3.74  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 10.75/3.74  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 10.75/3.74  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 10.75/3.74  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.75/3.74  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.75/3.74  tff(f_56, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 10.75/3.74  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 10.75/3.74  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 10.75/3.74  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.75/3.74  tff(c_50, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | k9_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.74  tff(c_96, plain, (k9_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 10.75/3.74  tff(c_48, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.74  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.75/3.74  tff(c_56, plain, (k9_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.74  tff(c_112, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_96, c_56])).
% 10.75/3.74  tff(c_183, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.75/3.74  tff(c_189, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_112, c_183])).
% 10.75/3.74  tff(c_200, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_189])).
% 10.75/3.74  tff(c_38, plain, (![B_38, A_37]: (k2_relat_1(k7_relat_1(B_38, A_37))=k9_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.75/3.74  tff(c_208, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_200, c_38])).
% 10.75/3.74  tff(c_212, plain, (k9_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_208])).
% 10.75/3.74  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_212])).
% 10.75/3.74  tff(c_215, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 10.75/3.74  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.75/3.74  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.75/3.74  tff(c_87, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.75/3.74  tff(c_90, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_87])).
% 10.75/3.74  tff(c_216, plain, (k9_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 10.75/3.74  tff(c_18, plain, (![C_27, A_12]: (r2_hidden(k4_tarski(C_27, '#skF_5'(A_12, k1_relat_1(A_12), C_27)), A_12) | ~r2_hidden(C_27, k1_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.75/3.74  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.75/3.74  tff(c_974, plain, (![A_151, C_152, B_153, D_154]: (r2_hidden(A_151, k9_relat_1(C_152, B_153)) | ~r2_hidden(D_154, B_153) | ~r2_hidden(k4_tarski(D_154, A_151), C_152) | ~r2_hidden(D_154, k1_relat_1(C_152)) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.75/3.74  tff(c_2084, plain, (![A_220, C_221, A_222, B_223]: (r2_hidden(A_220, k9_relat_1(C_221, A_222)) | ~r2_hidden(k4_tarski('#skF_1'(A_222, B_223), A_220), C_221) | ~r2_hidden('#skF_1'(A_222, B_223), k1_relat_1(C_221)) | ~v1_relat_1(C_221) | r1_xboole_0(A_222, B_223))), inference(resolution, [status(thm)], [c_8, c_974])).
% 10.75/3.74  tff(c_14546, plain, (![A_555, A_556, B_557]: (r2_hidden('#skF_5'(A_555, k1_relat_1(A_555), '#skF_1'(A_556, B_557)), k9_relat_1(A_555, A_556)) | ~v1_relat_1(A_555) | r1_xboole_0(A_556, B_557) | ~r2_hidden('#skF_1'(A_556, B_557), k1_relat_1(A_555)))), inference(resolution, [status(thm)], [c_18, c_2084])).
% 10.75/3.74  tff(c_14682, plain, (![B_557]: (r2_hidden('#skF_5'('#skF_8', k1_relat_1('#skF_8'), '#skF_1'('#skF_7', B_557)), k1_xboole_0) | ~v1_relat_1('#skF_8') | r1_xboole_0('#skF_7', B_557) | ~r2_hidden('#skF_1'('#skF_7', B_557), k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_216, c_14546])).
% 10.75/3.74  tff(c_14711, plain, (![B_557]: (r2_hidden('#skF_5'('#skF_8', k1_relat_1('#skF_8'), '#skF_1'('#skF_7', B_557)), k1_xboole_0) | r1_xboole_0('#skF_7', B_557) | ~r2_hidden('#skF_1'('#skF_7', B_557), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14682])).
% 10.75/3.74  tff(c_14714, plain, (![B_558]: (r1_xboole_0('#skF_7', B_558) | ~r2_hidden('#skF_1'('#skF_7', B_558), k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_90, c_14711])).
% 10.75/3.74  tff(c_14719, plain, (r1_xboole_0('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_14714])).
% 10.75/3.74  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.75/3.74  tff(c_14723, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_14719, c_2])).
% 10.75/3.74  tff(c_14728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_14723])).
% 10.75/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.75/3.74  
% 10.75/3.74  Inference rules
% 10.75/3.74  ----------------------
% 10.75/3.74  #Ref     : 0
% 10.75/3.74  #Sup     : 3705
% 10.75/3.74  #Fact    : 0
% 10.75/3.74  #Define  : 0
% 10.75/3.74  #Split   : 8
% 10.75/3.74  #Chain   : 0
% 10.75/3.74  #Close   : 0
% 10.75/3.74  
% 10.75/3.74  Ordering : KBO
% 10.75/3.74  
% 10.75/3.74  Simplification rules
% 10.75/3.74  ----------------------
% 10.75/3.74  #Subsume      : 1987
% 10.75/3.74  #Demod        : 2781
% 10.75/3.74  #Tautology    : 851
% 10.75/3.74  #SimpNegUnit  : 127
% 10.75/3.74  #BackRed      : 0
% 10.75/3.74  
% 10.75/3.74  #Partial instantiations: 0
% 10.75/3.74  #Strategies tried      : 1
% 10.75/3.74  
% 10.75/3.74  Timing (in seconds)
% 10.75/3.74  ----------------------
% 10.75/3.74  Preprocessing        : 0.31
% 10.75/3.74  Parsing              : 0.18
% 10.75/3.74  CNF conversion       : 0.02
% 10.75/3.74  Main loop            : 2.61
% 10.75/3.74  Inferencing          : 0.63
% 10.75/3.74  Reduction            : 0.54
% 10.75/3.74  Demodulation         : 0.36
% 10.75/3.74  BG Simplification    : 0.05
% 10.75/3.74  Subsumption          : 1.27
% 10.75/3.74  Abstraction          : 0.09
% 10.75/3.74  MUC search           : 0.00
% 10.75/3.74  Cooper               : 0.00
% 10.75/3.74  Total                : 2.95
% 10.75/3.74  Index Insertion      : 0.00
% 10.75/3.75  Index Deletion       : 0.00
% 10.75/3.75  Index Matching       : 0.00
% 10.75/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
