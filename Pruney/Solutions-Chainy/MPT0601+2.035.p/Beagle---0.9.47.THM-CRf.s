%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 164 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_40,plain,
    ( r2_hidden('#skF_10',k1_relat_1('#skF_11'))
    | k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_65,plain,(
    k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [C_75,A_76] :
      ( r2_hidden(k4_tarski(C_75,'#skF_7'(A_76,k1_relat_1(A_76),C_75)),A_76)
      | ~ r2_hidden(C_75,k1_relat_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_128,c_58])).

tff(c_175,plain,(
    v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_68,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | r2_hidden(k4_tarski('#skF_8'(A_64),'#skF_9'(A_64)),A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k1_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(C_40,D_43),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_8'(A_64),k1_relat_1(A_64))
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_68,c_16])).

tff(c_14,plain,(
    ! [C_40,A_25] :
      ( r2_hidden(k4_tarski(C_40,'#skF_7'(A_25,k1_relat_1(A_25),C_40)),A_25)
      | ~ r2_hidden(C_40,k1_relat_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,(
    ! [C_79] : ~ r2_hidden(C_79,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_14,c_147])).

tff(c_189,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_202,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_189])).

tff(c_326,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(k4_tarski('#skF_4'(A_93,B_94),'#skF_5'(A_93,B_94)),A_93)
      | r2_hidden('#skF_6'(A_93,B_94),B_94)
      | k1_relat_1(A_93) = B_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_336,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_94),B_94)
      | k1_relat_1(k1_xboole_0) = B_94 ) ),
    inference(resolution,[status(thm)],[c_326,c_58])).

tff(c_340,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_94),B_94)
      | k1_xboole_0 = B_94 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_336])).

tff(c_88,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski(A_70,B_71),C_72)
      | ~ r2_hidden(B_71,k11_relat_1(C_72,A_70))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_355,plain,(
    ! [A_98,C_99,B_100] :
      ( r2_hidden(A_98,k1_relat_1(C_99))
      | ~ r2_hidden(B_100,k11_relat_1(C_99,A_98))
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_88,c_16])).

tff(c_437,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(A_106,k1_relat_1(C_107))
      | ~ v1_relat_1(C_107)
      | k11_relat_1(C_107,A_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_340,c_355])).

tff(c_34,plain,
    ( k11_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_458,plain,
    ( ~ v1_relat_1('#skF_11')
    | k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_437,c_66])).

tff(c_469,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_458])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_469])).

tff(c_472,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_472])).

tff(c_475,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_476,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_520,plain,(
    ! [C_120,A_121] :
      ( r2_hidden(k4_tarski(C_120,'#skF_7'(A_121,k1_relat_1(A_121),C_120)),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [B_45,C_46,A_44] :
      ( r2_hidden(B_45,k11_relat_1(C_46,A_44))
      | ~ r2_hidden(k4_tarski(A_44,B_45),C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1435,plain,(
    ! [A_186,C_187] :
      ( r2_hidden('#skF_7'(A_186,k1_relat_1(A_186),C_187),k11_relat_1(A_186,C_187))
      | ~ v1_relat_1(A_186)
      | ~ r2_hidden(C_187,k1_relat_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_520,c_28])).

tff(c_1455,plain,
    ( r2_hidden('#skF_7'('#skF_11',k1_relat_1('#skF_11'),'#skF_10'),k1_xboole_0)
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_1435])).

tff(c_1465,plain,(
    r2_hidden('#skF_7'('#skF_11',k1_relat_1('#skF_11'),'#skF_10'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_32,c_1455])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.47  
% 2.97/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.47  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 2.97/1.47  
% 2.97/1.47  %Foreground sorts:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Background operators:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Foreground operators:
% 2.97/1.47  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.97/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.47  tff('#skF_11', type, '#skF_11': $i).
% 2.97/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.47  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.97/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.47  tff('#skF_10', type, '#skF_10': $i).
% 2.97/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.97/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.47  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.97/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.97/1.47  
% 3.07/1.49  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.07/1.49  tff(f_34, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.07/1.49  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.07/1.49  tff(f_44, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.07/1.49  tff(f_52, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.07/1.49  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 3.07/1.49  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.07/1.49  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.49  tff(c_53, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.49  tff(c_58, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_53])).
% 3.07/1.49  tff(c_40, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11')) | k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.49  tff(c_65, plain, (k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.07/1.49  tff(c_32, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.49  tff(c_12, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.49  tff(c_128, plain, (![C_75, A_76]: (r2_hidden(k4_tarski(C_75, '#skF_7'(A_76, k1_relat_1(A_76), C_75)), A_76) | ~r2_hidden(C_75, k1_relat_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_147, plain, (![C_77]: (~r2_hidden(C_77, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_128, c_58])).
% 3.07/1.49  tff(c_175, plain, (v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_147])).
% 3.07/1.49  tff(c_68, plain, (![A_64]: (k1_xboole_0=A_64 | r2_hidden(k4_tarski('#skF_8'(A_64), '#skF_9'(A_64)), A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.07/1.49  tff(c_16, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k1_relat_1(A_25)) | ~r2_hidden(k4_tarski(C_40, D_43), A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_76, plain, (![A_64]: (r2_hidden('#skF_8'(A_64), k1_relat_1(A_64)) | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_68, c_16])).
% 3.07/1.49  tff(c_14, plain, (![C_40, A_25]: (r2_hidden(k4_tarski(C_40, '#skF_7'(A_25, k1_relat_1(A_25), C_40)), A_25) | ~r2_hidden(C_40, k1_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_177, plain, (![C_79]: (~r2_hidden(C_79, k1_relat_1(k1_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_14, c_147])).
% 3.07/1.49  tff(c_189, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_76, c_177])).
% 3.07/1.49  tff(c_202, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_189])).
% 3.07/1.49  tff(c_326, plain, (![A_93, B_94]: (r2_hidden(k4_tarski('#skF_4'(A_93, B_94), '#skF_5'(A_93, B_94)), A_93) | r2_hidden('#skF_6'(A_93, B_94), B_94) | k1_relat_1(A_93)=B_94)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_336, plain, (![B_94]: (r2_hidden('#skF_6'(k1_xboole_0, B_94), B_94) | k1_relat_1(k1_xboole_0)=B_94)), inference(resolution, [status(thm)], [c_326, c_58])).
% 3.07/1.49  tff(c_340, plain, (![B_94]: (r2_hidden('#skF_6'(k1_xboole_0, B_94), B_94) | k1_xboole_0=B_94)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_336])).
% 3.07/1.49  tff(c_88, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski(A_70, B_71), C_72) | ~r2_hidden(B_71, k11_relat_1(C_72, A_70)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.49  tff(c_355, plain, (![A_98, C_99, B_100]: (r2_hidden(A_98, k1_relat_1(C_99)) | ~r2_hidden(B_100, k11_relat_1(C_99, A_98)) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_88, c_16])).
% 3.07/1.49  tff(c_437, plain, (![A_106, C_107]: (r2_hidden(A_106, k1_relat_1(C_107)) | ~v1_relat_1(C_107) | k11_relat_1(C_107, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_340, c_355])).
% 3.07/1.49  tff(c_34, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | ~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.49  tff(c_66, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.07/1.49  tff(c_458, plain, (~v1_relat_1('#skF_11') | k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_437, c_66])).
% 3.07/1.49  tff(c_469, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_458])).
% 3.07/1.49  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_469])).
% 3.07/1.49  tff(c_472, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.07/1.49  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_472])).
% 3.07/1.49  tff(c_475, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_40])).
% 3.07/1.49  tff(c_476, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.07/1.49  tff(c_520, plain, (![C_120, A_121]: (r2_hidden(k4_tarski(C_120, '#skF_7'(A_121, k1_relat_1(A_121), C_120)), A_121) | ~r2_hidden(C_120, k1_relat_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_28, plain, (![B_45, C_46, A_44]: (r2_hidden(B_45, k11_relat_1(C_46, A_44)) | ~r2_hidden(k4_tarski(A_44, B_45), C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.49  tff(c_1435, plain, (![A_186, C_187]: (r2_hidden('#skF_7'(A_186, k1_relat_1(A_186), C_187), k11_relat_1(A_186, C_187)) | ~v1_relat_1(A_186) | ~r2_hidden(C_187, k1_relat_1(A_186)))), inference(resolution, [status(thm)], [c_520, c_28])).
% 3.07/1.49  tff(c_1455, plain, (r2_hidden('#skF_7'('#skF_11', k1_relat_1('#skF_11'), '#skF_10'), k1_xboole_0) | ~v1_relat_1('#skF_11') | ~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_1435])).
% 3.07/1.49  tff(c_1465, plain, (r2_hidden('#skF_7'('#skF_11', k1_relat_1('#skF_11'), '#skF_10'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_475, c_32, c_1455])).
% 3.07/1.49  tff(c_1467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1465])).
% 3.07/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  Inference rules
% 3.07/1.49  ----------------------
% 3.07/1.49  #Ref     : 2
% 3.07/1.49  #Sup     : 277
% 3.07/1.49  #Fact    : 0
% 3.07/1.49  #Define  : 0
% 3.07/1.49  #Split   : 2
% 3.07/1.49  #Chain   : 0
% 3.07/1.49  #Close   : 0
% 3.07/1.49  
% 3.07/1.49  Ordering : KBO
% 3.07/1.49  
% 3.07/1.49  Simplification rules
% 3.07/1.49  ----------------------
% 3.07/1.49  #Subsume      : 61
% 3.07/1.49  #Demod        : 241
% 3.07/1.49  #Tautology    : 86
% 3.07/1.49  #SimpNegUnit  : 48
% 3.07/1.49  #BackRed      : 12
% 3.07/1.49  
% 3.07/1.49  #Partial instantiations: 0
% 3.07/1.49  #Strategies tried      : 1
% 3.07/1.49  
% 3.07/1.49  Timing (in seconds)
% 3.07/1.49  ----------------------
% 3.07/1.49  Preprocessing        : 0.30
% 3.07/1.49  Parsing              : 0.15
% 3.07/1.49  CNF conversion       : 0.02
% 3.07/1.49  Main loop            : 0.43
% 3.07/1.49  Inferencing          : 0.16
% 3.07/1.49  Reduction            : 0.13
% 3.07/1.49  Demodulation         : 0.09
% 3.07/1.49  BG Simplification    : 0.02
% 3.07/1.49  Subsumption          : 0.09
% 3.07/1.49  Abstraction          : 0.03
% 3.07/1.49  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.76
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
