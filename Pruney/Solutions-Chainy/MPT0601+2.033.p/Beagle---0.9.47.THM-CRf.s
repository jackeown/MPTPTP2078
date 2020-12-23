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
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 157 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1596,plain,(
    ! [A_152,C_153,B_154] :
      ( ~ r2_hidden(A_152,C_153)
      | ~ r1_xboole_0(k2_tarski(A_152,B_154),C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1601,plain,(
    ! [A_152] : ~ r2_hidden(A_152,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1596])).

tff(c_42,plain,
    ( k11_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_12'))
    | k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_62,plain,(
    k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48])).

tff(c_40,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    ! [C_80,A_81] :
      ( r2_hidden(k4_tarski(C_80,'#skF_7'(A_81,k1_relat_1(A_81),C_80)),A_81)
      | ~ r2_hidden(C_80,k1_relat_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_61,C_62,B_63] :
      ( ~ r2_hidden(A_61,C_62)
      | ~ r1_xboole_0(k2_tarski(A_61,B_63),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [A_61] : ~ r2_hidden(A_61,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_154,plain,(
    ! [C_82] : ~ r2_hidden(C_82,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_140,c_68])).

tff(c_182,plain,(
    v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_76,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | r2_hidden(k4_tarski('#skF_9'(A_68),'#skF_10'(A_68)),A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k1_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(C_38,D_41),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_9'(A_68),k1_relat_1(A_68))
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_76,c_14])).

tff(c_12,plain,(
    ! [C_38,A_23] :
      ( r2_hidden(k4_tarski(C_38,'#skF_7'(A_23,k1_relat_1(A_23),C_38)),A_23)
      | ~ r2_hidden(C_38,k1_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_183,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_195,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_88,c_183])).

tff(c_208,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_195])).

tff(c_689,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(k4_tarski('#skF_4'(A_122,B_123),'#skF_5'(A_122,B_123)),A_122)
      | r2_hidden('#skF_6'(A_122,B_123),B_123)
      | k1_relat_1(A_122) = B_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_708,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_123),B_123)
      | k1_relat_1(k1_xboole_0) = B_123 ) ),
    inference(resolution,[status(thm)],[c_689,c_68])).

tff(c_717,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_123),B_123)
      | k1_xboole_0 = B_123 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_708])).

tff(c_90,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski(A_70,B_71),C_72)
      | ~ r2_hidden(B_71,k11_relat_1(C_72,A_70))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1257,plain,(
    ! [A_141,C_142,B_143] :
      ( r2_hidden(A_141,k1_relat_1(C_142))
      | ~ r2_hidden(B_143,k11_relat_1(C_142,A_141))
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_90,c_14])).

tff(c_1517,plain,(
    ! [A_149,C_150] :
      ( r2_hidden(A_149,k1_relat_1(C_150))
      | ~ v1_relat_1(C_150)
      | k11_relat_1(C_150,A_149) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_717,c_1257])).

tff(c_1552,plain,
    ( ~ v1_relat_1('#skF_12')
    | k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1517,c_52])).

tff(c_1576,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1552])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1576])).

tff(c_1580,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1579,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1753,plain,(
    ! [C_184,A_185] :
      ( r2_hidden(k4_tarski(C_184,'#skF_7'(A_185,k1_relat_1(A_185),C_184)),A_185)
      | ~ r2_hidden(C_184,k1_relat_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [B_50,C_51,A_49] :
      ( r2_hidden(B_50,k11_relat_1(C_51,A_49))
      | ~ r2_hidden(k4_tarski(A_49,B_50),C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4205,plain,(
    ! [A_283,C_284] :
      ( r2_hidden('#skF_7'(A_283,k1_relat_1(A_283),C_284),k11_relat_1(A_283,C_284))
      | ~ v1_relat_1(A_283)
      | ~ r2_hidden(C_284,k1_relat_1(A_283)) ) ),
    inference(resolution,[status(thm)],[c_1753,c_36])).

tff(c_4233,plain,
    ( r2_hidden('#skF_7'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0)
    | ~ v1_relat_1('#skF_12')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1579,c_4205])).

tff(c_4243,plain,(
    r2_hidden('#skF_7'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1580,c_40,c_4233])).

tff(c_4245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1601,c_4243])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.78  
% 4.40/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 4.40/1.79  
% 4.40/1.79  %Foreground sorts:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Background operators:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Foreground operators:
% 4.40/1.79  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.40/1.79  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.79  tff('#skF_11', type, '#skF_11': $i).
% 4.40/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.40/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.40/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.40/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.40/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.79  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.40/1.79  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.40/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.40/1.79  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.40/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.40/1.79  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.40/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.40/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.40/1.79  tff('#skF_12', type, '#skF_12': $i).
% 4.40/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.40/1.79  
% 4.52/1.80  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.52/1.80  tff(f_32, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.52/1.80  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.52/1.80  tff(f_42, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 4.52/1.80  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.52/1.80  tff(f_79, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 4.52/1.80  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.52/1.80  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.80  tff(c_1596, plain, (![A_152, C_153, B_154]: (~r2_hidden(A_152, C_153) | ~r1_xboole_0(k2_tarski(A_152, B_154), C_153))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.52/1.80  tff(c_1601, plain, (![A_152]: (~r2_hidden(A_152, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1596])).
% 4.52/1.80  tff(c_42, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.52/1.80  tff(c_52, plain, (~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.52/1.80  tff(c_48, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12')) | k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.52/1.80  tff(c_62, plain, (k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_48])).
% 4.52/1.80  tff(c_40, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.52/1.80  tff(c_10, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.80  tff(c_140, plain, (![C_80, A_81]: (r2_hidden(k4_tarski(C_80, '#skF_7'(A_81, k1_relat_1(A_81), C_80)), A_81) | ~r2_hidden(C_80, k1_relat_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.80  tff(c_63, plain, (![A_61, C_62, B_63]: (~r2_hidden(A_61, C_62) | ~r1_xboole_0(k2_tarski(A_61, B_63), C_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.52/1.80  tff(c_68, plain, (![A_61]: (~r2_hidden(A_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_63])).
% 4.52/1.80  tff(c_154, plain, (![C_82]: (~r2_hidden(C_82, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_140, c_68])).
% 4.52/1.80  tff(c_182, plain, (v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_154])).
% 4.52/1.80  tff(c_76, plain, (![A_68]: (k1_xboole_0=A_68 | r2_hidden(k4_tarski('#skF_9'(A_68), '#skF_10'(A_68)), A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.52/1.80  tff(c_14, plain, (![C_38, A_23, D_41]: (r2_hidden(C_38, k1_relat_1(A_23)) | ~r2_hidden(k4_tarski(C_38, D_41), A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.80  tff(c_88, plain, (![A_68]: (r2_hidden('#skF_9'(A_68), k1_relat_1(A_68)) | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_76, c_14])).
% 4.52/1.80  tff(c_12, plain, (![C_38, A_23]: (r2_hidden(k4_tarski(C_38, '#skF_7'(A_23, k1_relat_1(A_23), C_38)), A_23) | ~r2_hidden(C_38, k1_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.80  tff(c_183, plain, (![C_83]: (~r2_hidden(C_83, k1_relat_1(k1_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_12, c_154])).
% 4.52/1.80  tff(c_195, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_88, c_183])).
% 4.52/1.80  tff(c_208, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_182, c_195])).
% 4.52/1.80  tff(c_689, plain, (![A_122, B_123]: (r2_hidden(k4_tarski('#skF_4'(A_122, B_123), '#skF_5'(A_122, B_123)), A_122) | r2_hidden('#skF_6'(A_122, B_123), B_123) | k1_relat_1(A_122)=B_123)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.80  tff(c_708, plain, (![B_123]: (r2_hidden('#skF_6'(k1_xboole_0, B_123), B_123) | k1_relat_1(k1_xboole_0)=B_123)), inference(resolution, [status(thm)], [c_689, c_68])).
% 4.52/1.80  tff(c_717, plain, (![B_123]: (r2_hidden('#skF_6'(k1_xboole_0, B_123), B_123) | k1_xboole_0=B_123)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_708])).
% 4.52/1.80  tff(c_90, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski(A_70, B_71), C_72) | ~r2_hidden(B_71, k11_relat_1(C_72, A_70)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.80  tff(c_1257, plain, (![A_141, C_142, B_143]: (r2_hidden(A_141, k1_relat_1(C_142)) | ~r2_hidden(B_143, k11_relat_1(C_142, A_141)) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_90, c_14])).
% 4.52/1.80  tff(c_1517, plain, (![A_149, C_150]: (r2_hidden(A_149, k1_relat_1(C_150)) | ~v1_relat_1(C_150) | k11_relat_1(C_150, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_717, c_1257])).
% 4.52/1.80  tff(c_1552, plain, (~v1_relat_1('#skF_12') | k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_1517, c_52])).
% 4.52/1.80  tff(c_1576, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1552])).
% 4.52/1.80  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1576])).
% 4.52/1.80  tff(c_1580, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_42])).
% 4.52/1.80  tff(c_1579, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 4.52/1.80  tff(c_1753, plain, (![C_184, A_185]: (r2_hidden(k4_tarski(C_184, '#skF_7'(A_185, k1_relat_1(A_185), C_184)), A_185) | ~r2_hidden(C_184, k1_relat_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.80  tff(c_36, plain, (![B_50, C_51, A_49]: (r2_hidden(B_50, k11_relat_1(C_51, A_49)) | ~r2_hidden(k4_tarski(A_49, B_50), C_51) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.80  tff(c_4205, plain, (![A_283, C_284]: (r2_hidden('#skF_7'(A_283, k1_relat_1(A_283), C_284), k11_relat_1(A_283, C_284)) | ~v1_relat_1(A_283) | ~r2_hidden(C_284, k1_relat_1(A_283)))), inference(resolution, [status(thm)], [c_1753, c_36])).
% 4.52/1.80  tff(c_4233, plain, (r2_hidden('#skF_7'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0) | ~v1_relat_1('#skF_12') | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1579, c_4205])).
% 4.52/1.80  tff(c_4243, plain, (r2_hidden('#skF_7'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1580, c_40, c_4233])).
% 4.52/1.80  tff(c_4245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1601, c_4243])).
% 4.52/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.80  
% 4.52/1.80  Inference rules
% 4.52/1.80  ----------------------
% 4.52/1.80  #Ref     : 2
% 4.52/1.80  #Sup     : 898
% 4.52/1.80  #Fact    : 0
% 4.52/1.80  #Define  : 0
% 4.52/1.80  #Split   : 1
% 4.52/1.80  #Chain   : 0
% 4.52/1.80  #Close   : 0
% 4.52/1.80  
% 4.52/1.80  Ordering : KBO
% 4.52/1.80  
% 4.52/1.80  Simplification rules
% 4.52/1.80  ----------------------
% 4.52/1.80  #Subsume      : 234
% 4.52/1.80  #Demod        : 914
% 4.52/1.80  #Tautology    : 323
% 4.52/1.80  #SimpNegUnit  : 58
% 4.52/1.80  #BackRed      : 16
% 4.52/1.80  
% 4.52/1.80  #Partial instantiations: 0
% 4.52/1.80  #Strategies tried      : 1
% 4.52/1.80  
% 4.52/1.80  Timing (in seconds)
% 4.52/1.80  ----------------------
% 4.52/1.80  Preprocessing        : 0.29
% 4.52/1.80  Parsing              : 0.15
% 4.52/1.80  CNF conversion       : 0.03
% 4.52/1.80  Main loop            : 0.75
% 4.52/1.80  Inferencing          : 0.26
% 4.52/1.80  Reduction            : 0.22
% 4.52/1.80  Demodulation         : 0.15
% 4.52/1.80  BG Simplification    : 0.03
% 4.52/1.80  Subsumption          : 0.18
% 4.52/1.80  Abstraction          : 0.03
% 4.52/1.80  MUC search           : 0.00
% 4.52/1.80  Cooper               : 0.00
% 4.52/1.80  Total                : 1.07
% 4.52/1.80  Index Insertion      : 0.00
% 4.52/1.80  Index Deletion       : 0.00
% 4.52/1.80  Index Matching       : 0.00
% 4.52/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
