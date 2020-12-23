%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.04s
% Verified   : 
% Statistics : Number of formulae       :   64 (  99 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 182 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_36,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7')
    | k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_723,plain,(
    ! [A_126,B_127] :
      ( r2_hidden(k4_tarski('#skF_3'(A_126,B_127),'#skF_2'(A_126,B_127)),A_126)
      | r2_hidden('#skF_4'(A_126,B_127),B_127)
      | k2_relat_1(A_126) = B_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | ~ r1_xboole_0(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_793,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_128),B_128)
      | k2_relat_1(k1_xboole_0) = B_128 ) ),
    inference(resolution,[status(thm)],[c_723,c_58])).

tff(c_859,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_793,c_58])).

tff(c_792,plain,(
    ! [B_127] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_127),B_127)
      | k2_relat_1(k1_xboole_0) = B_127 ) ),
    inference(resolution,[status(thm)],[c_723,c_58])).

tff(c_860,plain,(
    ! [B_127] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_127),B_127)
      | k1_xboole_0 = B_127 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_792])).

tff(c_34,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_6'(A_30,B_31,C_32),B_31)
      | ~ r2_hidden(A_30,k10_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_418,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_6'(A_89,B_90,C_91),k2_relat_1(C_91))
      | ~ r2_hidden(A_89,k10_relat_1(C_91,B_90))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_42])).

tff(c_84,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,B_51)
      | ~ r2_hidden(C_52,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [C_52] :
      ( ~ r2_hidden(C_52,'#skF_7')
      | ~ r2_hidden(C_52,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_68,c_84])).

tff(c_442,plain,(
    ! [A_89,B_90] :
      ( ~ r2_hidden('#skF_6'(A_89,B_90,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_89,k10_relat_1('#skF_8',B_90))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_418,c_94])).

tff(c_1114,plain,(
    ! [A_141,B_142] :
      ( ~ r2_hidden('#skF_6'(A_141,B_142,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_141,k10_relat_1('#skF_8',B_142)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_442])).

tff(c_1118,plain,(
    ! [A_30] :
      ( ~ r2_hidden(A_30,k10_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_1114])).

tff(c_1122,plain,(
    ! [A_143] : ~ r2_hidden(A_143,k10_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1118])).

tff(c_1126,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_860,c_1122])).

tff(c_1154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1126])).

tff(c_1155,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1156,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_14,plain,(
    ! [A_11,C_26] :
      ( r2_hidden(k4_tarski('#skF_5'(A_11,k2_relat_1(A_11),C_26),C_26),A_11)
      | ~ r2_hidden(C_26,k2_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1504,plain,(
    ! [A_191,C_192,B_193,D_194] :
      ( r2_hidden(A_191,k10_relat_1(C_192,B_193))
      | ~ r2_hidden(D_194,B_193)
      | ~ r2_hidden(k4_tarski(A_191,D_194),C_192)
      | ~ r2_hidden(D_194,k2_relat_1(C_192))
      | ~ v1_relat_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2192,plain,(
    ! [A_231,C_232,A_233,B_234] :
      ( r2_hidden(A_231,k10_relat_1(C_232,A_233))
      | ~ r2_hidden(k4_tarski(A_231,'#skF_1'(A_233,B_234)),C_232)
      | ~ r2_hidden('#skF_1'(A_233,B_234),k2_relat_1(C_232))
      | ~ v1_relat_1(C_232)
      | r1_xboole_0(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_8,c_1504])).

tff(c_6265,plain,(
    ! [A_416,A_417,B_418] :
      ( r2_hidden('#skF_5'(A_416,k2_relat_1(A_416),'#skF_1'(A_417,B_418)),k10_relat_1(A_416,A_417))
      | ~ v1_relat_1(A_416)
      | r1_xboole_0(A_417,B_418)
      | ~ r2_hidden('#skF_1'(A_417,B_418),k2_relat_1(A_416)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2192])).

tff(c_6362,plain,(
    ! [B_418] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_418)),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0('#skF_7',B_418)
      | ~ r2_hidden('#skF_1'('#skF_7',B_418),k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_6265])).

tff(c_6381,plain,(
    ! [B_418] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'('#skF_7',B_418)),k1_xboole_0)
      | r1_xboole_0('#skF_7',B_418)
      | ~ r2_hidden('#skF_1'('#skF_7',B_418),k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6362])).

tff(c_6383,plain,(
    ! [B_419] :
      ( r1_xboole_0('#skF_7',B_419)
      | ~ r2_hidden('#skF_1'('#skF_7',B_419),k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6381])).

tff(c_6388,plain,(
    r1_xboole_0('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_6383])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6392,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6388,c_2])).

tff(c_6397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1155,c_6392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.42  
% 7.04/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.43  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.04/2.43  
% 7.04/2.43  %Foreground sorts:
% 7.04/2.43  
% 7.04/2.43  
% 7.04/2.43  %Background operators:
% 7.04/2.43  
% 7.04/2.43  
% 7.04/2.43  %Foreground operators:
% 7.04/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.04/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.04/2.43  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.04/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.04/2.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.04/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.04/2.43  tff('#skF_7', type, '#skF_7': $i).
% 7.04/2.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.04/2.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.04/2.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.04/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.04/2.43  tff('#skF_8', type, '#skF_8': $i).
% 7.04/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.04/2.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.04/2.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.04/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.04/2.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.04/2.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.04/2.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.04/2.43  
% 7.04/2.45  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 7.04/2.45  tff(f_62, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 7.04/2.45  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.04/2.45  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 7.04/2.45  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 7.04/2.45  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.04/2.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.04/2.45  tff(c_36, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7') | k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.04/2.45  tff(c_59, plain, (k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 7.04/2.45  tff(c_723, plain, (![A_126, B_127]: (r2_hidden(k4_tarski('#skF_3'(A_126, B_127), '#skF_2'(A_126, B_127)), A_126) | r2_hidden('#skF_4'(A_126, B_127), B_127) | k2_relat_1(A_126)=B_127)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.04/2.45  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.04/2.45  tff(c_53, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | ~r1_xboole_0(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.04/2.45  tff(c_58, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_53])).
% 7.04/2.45  tff(c_793, plain, (![B_128]: (r2_hidden('#skF_4'(k1_xboole_0, B_128), B_128) | k2_relat_1(k1_xboole_0)=B_128)), inference(resolution, [status(thm)], [c_723, c_58])).
% 7.04/2.45  tff(c_859, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_793, c_58])).
% 7.04/2.45  tff(c_792, plain, (![B_127]: (r2_hidden('#skF_4'(k1_xboole_0, B_127), B_127) | k2_relat_1(k1_xboole_0)=B_127)), inference(resolution, [status(thm)], [c_723, c_58])).
% 7.04/2.45  tff(c_860, plain, (![B_127]: (r2_hidden('#skF_4'(k1_xboole_0, B_127), B_127) | k1_xboole_0=B_127)), inference(demodulation, [status(thm), theory('equality')], [c_859, c_792])).
% 7.04/2.45  tff(c_34, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.04/2.45  tff(c_28, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_6'(A_30, B_31, C_32), B_31) | ~r2_hidden(A_30, k10_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.04/2.45  tff(c_418, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_6'(A_89, B_90, C_91), k2_relat_1(C_91)) | ~r2_hidden(A_89, k10_relat_1(C_91, B_90)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.04/2.45  tff(c_42, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.04/2.45  tff(c_68, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_59, c_42])).
% 7.04/2.45  tff(c_84, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, B_51) | ~r2_hidden(C_52, A_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.04/2.45  tff(c_94, plain, (![C_52]: (~r2_hidden(C_52, '#skF_7') | ~r2_hidden(C_52, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_68, c_84])).
% 7.04/2.45  tff(c_442, plain, (![A_89, B_90]: (~r2_hidden('#skF_6'(A_89, B_90, '#skF_8'), '#skF_7') | ~r2_hidden(A_89, k10_relat_1('#skF_8', B_90)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_418, c_94])).
% 7.04/2.45  tff(c_1114, plain, (![A_141, B_142]: (~r2_hidden('#skF_6'(A_141, B_142, '#skF_8'), '#skF_7') | ~r2_hidden(A_141, k10_relat_1('#skF_8', B_142)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_442])).
% 7.04/2.45  tff(c_1118, plain, (![A_30]: (~r2_hidden(A_30, k10_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_28, c_1114])).
% 7.04/2.45  tff(c_1122, plain, (![A_143]: (~r2_hidden(A_143, k10_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1118])).
% 7.04/2.45  tff(c_1126, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_860, c_1122])).
% 7.04/2.45  tff(c_1154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_1126])).
% 7.04/2.45  tff(c_1155, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 7.04/2.45  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.04/2.45  tff(c_1156, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 7.04/2.45  tff(c_14, plain, (![A_11, C_26]: (r2_hidden(k4_tarski('#skF_5'(A_11, k2_relat_1(A_11), C_26), C_26), A_11) | ~r2_hidden(C_26, k2_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.04/2.45  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.04/2.45  tff(c_1504, plain, (![A_191, C_192, B_193, D_194]: (r2_hidden(A_191, k10_relat_1(C_192, B_193)) | ~r2_hidden(D_194, B_193) | ~r2_hidden(k4_tarski(A_191, D_194), C_192) | ~r2_hidden(D_194, k2_relat_1(C_192)) | ~v1_relat_1(C_192))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.04/2.45  tff(c_2192, plain, (![A_231, C_232, A_233, B_234]: (r2_hidden(A_231, k10_relat_1(C_232, A_233)) | ~r2_hidden(k4_tarski(A_231, '#skF_1'(A_233, B_234)), C_232) | ~r2_hidden('#skF_1'(A_233, B_234), k2_relat_1(C_232)) | ~v1_relat_1(C_232) | r1_xboole_0(A_233, B_234))), inference(resolution, [status(thm)], [c_8, c_1504])).
% 7.04/2.45  tff(c_6265, plain, (![A_416, A_417, B_418]: (r2_hidden('#skF_5'(A_416, k2_relat_1(A_416), '#skF_1'(A_417, B_418)), k10_relat_1(A_416, A_417)) | ~v1_relat_1(A_416) | r1_xboole_0(A_417, B_418) | ~r2_hidden('#skF_1'(A_417, B_418), k2_relat_1(A_416)))), inference(resolution, [status(thm)], [c_14, c_2192])).
% 7.04/2.45  tff(c_6362, plain, (![B_418]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_418)), k1_xboole_0) | ~v1_relat_1('#skF_8') | r1_xboole_0('#skF_7', B_418) | ~r2_hidden('#skF_1'('#skF_7', B_418), k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_6265])).
% 7.04/2.45  tff(c_6381, plain, (![B_418]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'('#skF_7', B_418)), k1_xboole_0) | r1_xboole_0('#skF_7', B_418) | ~r2_hidden('#skF_1'('#skF_7', B_418), k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6362])).
% 7.04/2.45  tff(c_6383, plain, (![B_419]: (r1_xboole_0('#skF_7', B_419) | ~r2_hidden('#skF_1'('#skF_7', B_419), k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_58, c_6381])).
% 7.04/2.45  tff(c_6388, plain, (r1_xboole_0('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_6383])).
% 7.04/2.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.04/2.45  tff(c_6392, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_6388, c_2])).
% 7.04/2.45  tff(c_6397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1155, c_6392])).
% 7.04/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.04/2.45  
% 7.04/2.45  Inference rules
% 7.04/2.45  ----------------------
% 7.04/2.45  #Ref     : 0
% 7.04/2.45  #Sup     : 1457
% 7.04/2.45  #Fact    : 0
% 7.04/2.45  #Define  : 0
% 7.04/2.45  #Split   : 6
% 7.04/2.45  #Chain   : 0
% 7.04/2.45  #Close   : 0
% 7.04/2.45  
% 7.04/2.45  Ordering : KBO
% 7.04/2.45  
% 7.04/2.45  Simplification rules
% 7.04/2.45  ----------------------
% 7.04/2.45  #Subsume      : 661
% 7.04/2.45  #Demod        : 989
% 7.04/2.45  #Tautology    : 337
% 7.04/2.45  #SimpNegUnit  : 57
% 7.04/2.45  #BackRed      : 39
% 7.04/2.45  
% 7.04/2.45  #Partial instantiations: 0
% 7.04/2.45  #Strategies tried      : 1
% 7.04/2.45  
% 7.04/2.45  Timing (in seconds)
% 7.04/2.45  ----------------------
% 7.04/2.45  Preprocessing        : 0.28
% 7.04/2.45  Parsing              : 0.15
% 7.04/2.45  CNF conversion       : 0.02
% 7.04/2.45  Main loop            : 1.38
% 7.04/2.45  Inferencing          : 0.44
% 7.04/2.45  Reduction            : 0.35
% 7.04/2.45  Demodulation         : 0.24
% 7.04/2.45  BG Simplification    : 0.04
% 7.04/2.45  Subsumption          : 0.47
% 7.04/2.45  Abstraction          : 0.06
% 7.04/2.45  MUC search           : 0.00
% 7.04/2.45  Cooper               : 0.00
% 7.04/2.45  Total                : 1.70
% 7.04/2.45  Index Insertion      : 0.00
% 7.04/2.45  Index Deletion       : 0.00
% 7.04/2.45  Index Matching       : 0.00
% 7.04/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
