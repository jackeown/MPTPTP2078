%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   71 (  85 expanded)
%              Number of leaves         :   42 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  94 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_146,plain,(
    ~ r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_72,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_433,plain,(
    ! [A_136] :
      ( k2_xboole_0(k1_relat_1(A_136),k2_relat_1(A_136)) = k3_relat_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_284,plain,(
    ! [C_119,A_120,D_121] :
      ( r2_hidden(C_119,k1_relat_1(A_120))
      | ~ r2_hidden(k4_tarski(C_119,D_121),A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_297,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_70,c_284])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_309,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_12',B_124)
      | ~ r1_tarski(k1_relat_1('#skF_14'),B_124) ) ),
    inference(resolution,[status(thm)],[c_297,c_2])).

tff(c_330,plain,(
    ! [B_7] : r2_hidden('#skF_12',k2_xboole_0(k1_relat_1('#skF_14'),B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_309])).

tff(c_444,plain,
    ( r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_330])).

tff(c_458,plain,(
    r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_444])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_458])).

tff(c_461,plain,(
    ~ r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_643,plain,(
    ! [A_158] :
      ( k2_xboole_0(k1_relat_1(A_158),k2_relat_1(A_158)) = k3_relat_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_116,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_470,plain,(
    ! [B_139,A_140] : k3_tarski(k2_tarski(B_139,A_140)) = k2_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_116])).

tff(c_38,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_496,plain,(
    ! [B_141,A_142] : k2_xboole_0(B_141,A_142) = k2_xboole_0(A_142,B_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_38])).

tff(c_511,plain,(
    ! [A_142,B_141] : r1_tarski(A_142,k2_xboole_0(B_141,A_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_8])).

tff(c_649,plain,(
    ! [A_158] :
      ( r1_tarski(k2_relat_1(A_158),k3_relat_1(A_158))
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_511])).

tff(c_669,plain,(
    ! [C_164,A_165,D_166] :
      ( r2_hidden(C_164,k2_relat_1(A_165))
      | ~ r2_hidden(k4_tarski(D_166,C_164),A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_682,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_70,c_669])).

tff(c_690,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_13',B_168)
      | ~ r1_tarski(k2_relat_1('#skF_14'),B_168) ) ),
    inference(resolution,[status(thm)],[c_682,c_2])).

tff(c_694,plain,
    ( r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_649,c_690])).

tff(c_713,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_694])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.49  
% 2.74/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 2.74/1.49  
% 2.74/1.49  %Foreground sorts:
% 2.74/1.49  
% 2.74/1.49  
% 2.74/1.49  %Background operators:
% 2.74/1.49  
% 2.74/1.49  
% 2.74/1.49  %Foreground operators:
% 2.74/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.74/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.49  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.74/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.74/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.49  tff('#skF_14', type, '#skF_14': $i).
% 2.74/1.49  tff('#skF_13', type, '#skF_13': $i).
% 2.74/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.49  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.74/1.49  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.74/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.49  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 2.74/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.74/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.49  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.74/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.74/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.49  tff('#skF_12', type, '#skF_12': $i).
% 2.74/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.74/1.49  
% 2.74/1.51  tff(f_92, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.74/1.51  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.74/1.51  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.74/1.51  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.74/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.51  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.74/1.51  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.74/1.51  tff(f_79, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.74/1.51  tff(c_68, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_14')) | ~r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.74/1.51  tff(c_146, plain, (~r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_68])).
% 2.74/1.51  tff(c_72, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.74/1.51  tff(c_433, plain, (![A_136]: (k2_xboole_0(k1_relat_1(A_136), k2_relat_1(A_136))=k3_relat_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.74/1.51  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.74/1.51  tff(c_70, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.74/1.51  tff(c_284, plain, (![C_119, A_120, D_121]: (r2_hidden(C_119, k1_relat_1(A_120)) | ~r2_hidden(k4_tarski(C_119, D_121), A_120))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.51  tff(c_297, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_70, c_284])).
% 2.74/1.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.51  tff(c_309, plain, (![B_124]: (r2_hidden('#skF_12', B_124) | ~r1_tarski(k1_relat_1('#skF_14'), B_124))), inference(resolution, [status(thm)], [c_297, c_2])).
% 2.74/1.51  tff(c_330, plain, (![B_7]: (r2_hidden('#skF_12', k2_xboole_0(k1_relat_1('#skF_14'), B_7)))), inference(resolution, [status(thm)], [c_8, c_309])).
% 2.74/1.51  tff(c_444, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_433, c_330])).
% 2.74/1.51  tff(c_458, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_444])).
% 2.74/1.51  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_458])).
% 2.74/1.51  tff(c_461, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_14'))), inference(splitRight, [status(thm)], [c_68])).
% 2.74/1.51  tff(c_643, plain, (![A_158]: (k2_xboole_0(k1_relat_1(A_158), k2_relat_1(A_158))=k3_relat_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.74/1.51  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.74/1.51  tff(c_116, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.51  tff(c_470, plain, (![B_139, A_140]: (k3_tarski(k2_tarski(B_139, A_140))=k2_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_10, c_116])).
% 2.74/1.51  tff(c_38, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.51  tff(c_496, plain, (![B_141, A_142]: (k2_xboole_0(B_141, A_142)=k2_xboole_0(A_142, B_141))), inference(superposition, [status(thm), theory('equality')], [c_470, c_38])).
% 2.74/1.51  tff(c_511, plain, (![A_142, B_141]: (r1_tarski(A_142, k2_xboole_0(B_141, A_142)))), inference(superposition, [status(thm), theory('equality')], [c_496, c_8])).
% 2.74/1.51  tff(c_649, plain, (![A_158]: (r1_tarski(k2_relat_1(A_158), k3_relat_1(A_158)) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_643, c_511])).
% 2.74/1.51  tff(c_669, plain, (![C_164, A_165, D_166]: (r2_hidden(C_164, k2_relat_1(A_165)) | ~r2_hidden(k4_tarski(D_166, C_164), A_165))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.51  tff(c_682, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_70, c_669])).
% 2.74/1.51  tff(c_690, plain, (![B_168]: (r2_hidden('#skF_13', B_168) | ~r1_tarski(k2_relat_1('#skF_14'), B_168))), inference(resolution, [status(thm)], [c_682, c_2])).
% 2.74/1.51  tff(c_694, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_649, c_690])).
% 2.74/1.51  tff(c_713, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_694])).
% 2.74/1.51  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_713])).
% 2.74/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.51  
% 2.74/1.51  Inference rules
% 2.74/1.51  ----------------------
% 2.74/1.51  #Ref     : 0
% 2.74/1.51  #Sup     : 143
% 2.74/1.51  #Fact    : 0
% 2.74/1.51  #Define  : 0
% 2.74/1.51  #Split   : 1
% 2.74/1.51  #Chain   : 0
% 2.74/1.51  #Close   : 0
% 2.74/1.51  
% 2.74/1.51  Ordering : KBO
% 2.74/1.51  
% 2.74/1.51  Simplification rules
% 2.74/1.51  ----------------------
% 2.74/1.51  #Subsume      : 7
% 2.74/1.51  #Demod        : 33
% 2.74/1.51  #Tautology    : 69
% 2.74/1.51  #SimpNegUnit  : 2
% 2.74/1.51  #BackRed      : 0
% 2.74/1.51  
% 2.74/1.51  #Partial instantiations: 0
% 2.74/1.51  #Strategies tried      : 1
% 2.74/1.51  
% 2.74/1.51  Timing (in seconds)
% 2.74/1.51  ----------------------
% 2.74/1.51  Preprocessing        : 0.32
% 2.74/1.51  Parsing              : 0.16
% 2.74/1.51  CNF conversion       : 0.03
% 2.74/1.51  Main loop            : 0.30
% 2.74/1.51  Inferencing          : 0.10
% 2.74/1.51  Reduction            : 0.10
% 2.74/1.51  Demodulation         : 0.07
% 2.74/1.51  BG Simplification    : 0.02
% 2.74/1.51  Subsumption          : 0.05
% 2.74/1.51  Abstraction          : 0.02
% 2.74/1.51  MUC search           : 0.00
% 2.74/1.51  Cooper               : 0.00
% 2.74/1.51  Total                : 0.65
% 2.74/1.51  Index Insertion      : 0.00
% 2.74/1.51  Index Deletion       : 0.00
% 2.74/1.51  Index Matching       : 0.00
% 2.74/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
