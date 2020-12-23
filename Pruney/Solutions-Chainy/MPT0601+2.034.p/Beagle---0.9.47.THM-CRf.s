%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 114 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 181 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_2 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_722,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_xboole_0(A_128,B_129)
      | ~ r2_hidden(C_130,k3_xboole_0(A_128,B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_729,plain,(
    ! [A_6,C_130] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_130,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_722])).

tff(c_732,plain,(
    ! [C_130] : ~ r2_hidden(C_130,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_729])).

tff(c_36,plain,
    ( k11_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_12'))
    | k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_42])).

tff(c_34,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_242,plain,(
    ! [C_92,A_93] :
      ( r2_hidden(k4_tarski(C_92,'#skF_8'(A_93,k1_relat_1(A_93),C_92)),A_93)
      | ~ r2_hidden(C_92,k1_relat_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_6,C_59] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_65,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_265,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_242,c_65])).

tff(c_305,plain,(
    v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_14,c_265])).

tff(c_89,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | r2_hidden(k4_tarski('#skF_9'(A_68),'#skF_10'(A_68)),A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [C_41,A_26,D_44] :
      ( r2_hidden(C_41,k1_relat_1(A_26))
      | ~ r2_hidden(k4_tarski(C_41,D_44),A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_9'(A_68),k1_relat_1(A_68))
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_89,c_18])).

tff(c_16,plain,(
    ! [C_41,A_26] :
      ( r2_hidden(k4_tarski(C_41,'#skF_8'(A_26,k1_relat_1(A_26),C_41)),A_26)
      | ~ r2_hidden(C_41,k1_relat_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_306,plain,(
    ! [C_95] : ~ r2_hidden(C_95,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_16,c_265])).

tff(c_322,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_105,c_306])).

tff(c_342,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_322])).

tff(c_457,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(k4_tarski('#skF_5'(A_109,B_110),'#skF_6'(A_109,B_110)),A_109)
      | r2_hidden('#skF_7'(A_109,B_110),B_110)
      | k1_relat_1(A_109) = B_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_471,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_110),B_110)
      | k1_relat_1(k1_xboole_0) = B_110 ) ),
    inference(resolution,[status(thm)],[c_457,c_65])).

tff(c_486,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_111),B_111)
      | k1_xboole_0 = B_111 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_471])).

tff(c_107,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(k4_tarski(A_69,B_70),C_71)
      | ~ r2_hidden(B_70,k11_relat_1(C_71,A_69))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_69,C_71,B_70] :
      ( r2_hidden(A_69,k1_relat_1(C_71))
      | ~ r2_hidden(B_70,k11_relat_1(C_71,A_69))
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_107,c_18])).

tff(c_663,plain,(
    ! [A_126,C_127] :
      ( r2_hidden(A_126,k1_relat_1(C_127))
      | ~ v1_relat_1(C_127)
      | k11_relat_1(C_127,A_126) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_486,c_122])).

tff(c_692,plain,
    ( ~ v1_relat_1('#skF_12')
    | k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_663,c_53])).

tff(c_711,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_692])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_711])).

tff(c_715,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_714,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_931,plain,(
    ! [C_168,A_169] :
      ( r2_hidden(k4_tarski(C_168,'#skF_8'(A_169,k1_relat_1(A_169),C_168)),A_169)
      | ~ r2_hidden(C_168,k1_relat_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [B_46,C_47,A_45] :
      ( r2_hidden(B_46,k11_relat_1(C_47,A_45))
      | ~ r2_hidden(k4_tarski(A_45,B_46),C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3630,plain,(
    ! [A_292,C_293] :
      ( r2_hidden('#skF_8'(A_292,k1_relat_1(A_292),C_293),k11_relat_1(A_292,C_293))
      | ~ v1_relat_1(A_292)
      | ~ r2_hidden(C_293,k1_relat_1(A_292)) ) ),
    inference(resolution,[status(thm)],[c_931,c_30])).

tff(c_3687,plain,
    ( r2_hidden('#skF_8'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0)
    | ~ v1_relat_1('#skF_12')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_3630])).

tff(c_3699,plain,(
    r2_hidden('#skF_8'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_34,c_3687])).

tff(c_3701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_3699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.81  
% 4.34/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.81  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_2 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 4.34/1.81  
% 4.34/1.81  %Foreground sorts:
% 4.34/1.81  
% 4.34/1.81  
% 4.34/1.81  %Background operators:
% 4.34/1.81  
% 4.34/1.81  
% 4.34/1.81  %Foreground operators:
% 4.34/1.81  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.34/1.81  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.34/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.81  tff('#skF_11', type, '#skF_11': $i).
% 4.34/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.34/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.34/1.81  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.34/1.81  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.34/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.34/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.81  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.34/1.81  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.34/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.34/1.81  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.34/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.34/1.81  tff('#skF_12', type, '#skF_12': $i).
% 4.34/1.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.34/1.81  
% 4.48/1.82  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.48/1.82  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.48/1.82  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.48/1.82  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.48/1.82  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 4.48/1.82  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.48/1.82  tff(f_75, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 4.48/1.82  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.48/1.82  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.48/1.82  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.82  tff(c_722, plain, (![A_128, B_129, C_130]: (~r1_xboole_0(A_128, B_129) | ~r2_hidden(C_130, k3_xboole_0(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.82  tff(c_729, plain, (![A_6, C_130]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_130, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_722])).
% 4.48/1.82  tff(c_732, plain, (![C_130]: (~r2_hidden(C_130, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_729])).
% 4.48/1.82  tff(c_36, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.48/1.82  tff(c_53, plain, (~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_36])).
% 4.48/1.82  tff(c_42, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12')) | k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.48/1.82  tff(c_54, plain, (k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_42])).
% 4.48/1.82  tff(c_34, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.48/1.82  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.48/1.82  tff(c_242, plain, (![C_92, A_93]: (r2_hidden(k4_tarski(C_92, '#skF_8'(A_93, k1_relat_1(A_93), C_92)), A_93) | ~r2_hidden(C_92, k1_relat_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.48/1.82  tff(c_55, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.82  tff(c_62, plain, (![A_6, C_59]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 4.48/1.82  tff(c_65, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_62])).
% 4.48/1.82  tff(c_265, plain, (![C_94]: (~r2_hidden(C_94, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_242, c_65])).
% 4.48/1.82  tff(c_305, plain, (v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_265])).
% 4.48/1.82  tff(c_89, plain, (![A_68]: (k1_xboole_0=A_68 | r2_hidden(k4_tarski('#skF_9'(A_68), '#skF_10'(A_68)), A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.48/1.82  tff(c_18, plain, (![C_41, A_26, D_44]: (r2_hidden(C_41, k1_relat_1(A_26)) | ~r2_hidden(k4_tarski(C_41, D_44), A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.48/1.82  tff(c_105, plain, (![A_68]: (r2_hidden('#skF_9'(A_68), k1_relat_1(A_68)) | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_89, c_18])).
% 4.48/1.82  tff(c_16, plain, (![C_41, A_26]: (r2_hidden(k4_tarski(C_41, '#skF_8'(A_26, k1_relat_1(A_26), C_41)), A_26) | ~r2_hidden(C_41, k1_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.48/1.82  tff(c_306, plain, (![C_95]: (~r2_hidden(C_95, k1_relat_1(k1_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_16, c_265])).
% 4.48/1.82  tff(c_322, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_306])).
% 4.48/1.82  tff(c_342, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_305, c_322])).
% 4.48/1.82  tff(c_457, plain, (![A_109, B_110]: (r2_hidden(k4_tarski('#skF_5'(A_109, B_110), '#skF_6'(A_109, B_110)), A_109) | r2_hidden('#skF_7'(A_109, B_110), B_110) | k1_relat_1(A_109)=B_110)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.48/1.82  tff(c_471, plain, (![B_110]: (r2_hidden('#skF_7'(k1_xboole_0, B_110), B_110) | k1_relat_1(k1_xboole_0)=B_110)), inference(resolution, [status(thm)], [c_457, c_65])).
% 4.48/1.82  tff(c_486, plain, (![B_111]: (r2_hidden('#skF_7'(k1_xboole_0, B_111), B_111) | k1_xboole_0=B_111)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_471])).
% 4.48/1.82  tff(c_107, plain, (![A_69, B_70, C_71]: (r2_hidden(k4_tarski(A_69, B_70), C_71) | ~r2_hidden(B_70, k11_relat_1(C_71, A_69)) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.48/1.82  tff(c_122, plain, (![A_69, C_71, B_70]: (r2_hidden(A_69, k1_relat_1(C_71)) | ~r2_hidden(B_70, k11_relat_1(C_71, A_69)) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_107, c_18])).
% 4.48/1.82  tff(c_663, plain, (![A_126, C_127]: (r2_hidden(A_126, k1_relat_1(C_127)) | ~v1_relat_1(C_127) | k11_relat_1(C_127, A_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_486, c_122])).
% 4.48/1.82  tff(c_692, plain, (~v1_relat_1('#skF_12') | k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_663, c_53])).
% 4.48/1.82  tff(c_711, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_692])).
% 4.48/1.82  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_711])).
% 4.48/1.82  tff(c_715, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_36])).
% 4.48/1.82  tff(c_714, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.48/1.82  tff(c_931, plain, (![C_168, A_169]: (r2_hidden(k4_tarski(C_168, '#skF_8'(A_169, k1_relat_1(A_169), C_168)), A_169) | ~r2_hidden(C_168, k1_relat_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.48/1.82  tff(c_30, plain, (![B_46, C_47, A_45]: (r2_hidden(B_46, k11_relat_1(C_47, A_45)) | ~r2_hidden(k4_tarski(A_45, B_46), C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.48/1.82  tff(c_3630, plain, (![A_292, C_293]: (r2_hidden('#skF_8'(A_292, k1_relat_1(A_292), C_293), k11_relat_1(A_292, C_293)) | ~v1_relat_1(A_292) | ~r2_hidden(C_293, k1_relat_1(A_292)))), inference(resolution, [status(thm)], [c_931, c_30])).
% 4.48/1.82  tff(c_3687, plain, (r2_hidden('#skF_8'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0) | ~v1_relat_1('#skF_12') | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_714, c_3630])).
% 4.48/1.82  tff(c_3699, plain, (r2_hidden('#skF_8'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_715, c_34, c_3687])).
% 4.48/1.82  tff(c_3701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_732, c_3699])).
% 4.48/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.82  
% 4.48/1.82  Inference rules
% 4.48/1.82  ----------------------
% 4.48/1.82  #Ref     : 2
% 4.48/1.82  #Sup     : 799
% 4.48/1.82  #Fact    : 0
% 4.48/1.82  #Define  : 0
% 4.48/1.82  #Split   : 1
% 4.48/1.82  #Chain   : 0
% 4.48/1.82  #Close   : 0
% 4.48/1.82  
% 4.48/1.82  Ordering : KBO
% 4.48/1.82  
% 4.48/1.82  Simplification rules
% 4.48/1.82  ----------------------
% 4.48/1.82  #Subsume      : 257
% 4.48/1.82  #Demod        : 614
% 4.48/1.82  #Tautology    : 206
% 4.48/1.82  #SimpNegUnit  : 133
% 4.48/1.82  #BackRed      : 10
% 4.48/1.82  
% 4.48/1.82  #Partial instantiations: 0
% 4.48/1.82  #Strategies tried      : 1
% 4.48/1.82  
% 4.48/1.82  Timing (in seconds)
% 4.48/1.82  ----------------------
% 4.55/1.83  Preprocessing        : 0.30
% 4.55/1.83  Parsing              : 0.16
% 4.55/1.83  CNF conversion       : 0.03
% 4.55/1.83  Main loop            : 0.76
% 4.55/1.83  Inferencing          : 0.28
% 4.55/1.83  Reduction            : 0.23
% 4.55/1.83  Demodulation         : 0.16
% 4.55/1.83  BG Simplification    : 0.03
% 4.55/1.83  Subsumption          : 0.16
% 4.55/1.83  Abstraction          : 0.04
% 4.55/1.83  MUC search           : 0.00
% 4.55/1.83  Cooper               : 0.00
% 4.55/1.83  Total                : 1.09
% 4.55/1.83  Index Insertion      : 0.00
% 4.55/1.83  Index Deletion       : 0.00
% 4.55/1.83  Index Matching       : 0.00
% 4.55/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
