%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 202 expanded)
%              Number of leaves         :   27 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 374 expanded)
%              Number of equality atoms :   23 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_40,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_46])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_211,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k4_tarski(A_59,B_60),C_61)
      | ~ r2_hidden(B_60,k11_relat_1(C_61,A_59))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_230,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden(A_62,k1_relat_1(C_63))
      | ~ r2_hidden(B_64,k11_relat_1(C_63,A_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_211,c_24])).

tff(c_239,plain,(
    ! [A_65,C_66] :
      ( r2_hidden(A_65,k1_relat_1(C_66))
      | ~ v1_relat_1(C_66)
      | k11_relat_1(C_66,A_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_230])).

tff(c_250,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_239,c_90])).

tff(c_255,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_250])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_255])).

tff(c_258,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_260,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_260])).

tff(c_267,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_437,plain,(
    ! [C_97,A_98] :
      ( r2_hidden(k4_tarski(C_97,'#skF_5'(A_98,k1_relat_1(A_98),C_97)),A_98)
      | ~ r2_hidden(C_97,k1_relat_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [B_31,C_32,A_30] :
      ( r2_hidden(B_31,k11_relat_1(C_32,A_30))
      | ~ r2_hidden(k4_tarski(A_30,B_31),C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1383,plain,(
    ! [A_151,C_152] :
      ( r2_hidden('#skF_5'(A_151,k1_relat_1(A_151),C_152),k11_relat_1(A_151,C_152))
      | ~ v1_relat_1(A_151)
      | ~ r2_hidden(C_152,k1_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_437,c_36])).

tff(c_1388,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_1383])).

tff(c_1391,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_38,c_1388])).

tff(c_20,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_331,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(A_77,B_78)
      | ~ r2_hidden(A_77,C_79)
      | r2_hidden(A_77,k5_xboole_0(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_803,plain,(
    ! [A_125,A_126,B_127] :
      ( r2_hidden(A_125,A_126)
      | ~ r2_hidden(A_125,k3_xboole_0(A_126,B_127))
      | r2_hidden(A_125,k4_xboole_0(A_126,B_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_331])).

tff(c_857,plain,(
    ! [A_128,A_129] :
      ( r2_hidden(A_128,A_129)
      | ~ r2_hidden(A_128,k3_xboole_0(A_129,k1_xboole_0))
      | r2_hidden(A_128,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_803])).

tff(c_886,plain,(
    ! [A_130] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_130,k1_xboole_0)),A_130)
      | k3_xboole_0(A_130,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_857])).

tff(c_363,plain,(
    ! [A_83,C_84,B_85] :
      ( ~ r2_hidden(A_83,C_84)
      | ~ r2_hidden(A_83,B_85)
      | ~ r2_hidden(A_83,k5_xboole_0(B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_523,plain,(
    ! [A_106,A_107,B_108] :
      ( ~ r2_hidden(A_106,k3_xboole_0(A_107,B_108))
      | ~ r2_hidden(A_106,A_107)
      | ~ r2_hidden(A_106,k4_xboole_0(A_107,B_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_363])).

tff(c_542,plain,(
    ! [A_109,A_110] :
      ( ~ r2_hidden(A_109,k3_xboole_0(A_110,k1_xboole_0))
      | ~ r2_hidden(A_109,A_110)
      | ~ r2_hidden(A_109,A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_523])).

tff(c_565,plain,(
    ! [A_110] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_110,k1_xboole_0)),A_110)
      | k3_xboole_0(A_110,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_542])).

tff(c_947,plain,(
    ! [A_130] : k3_xboole_0(A_130,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_886,c_565])).

tff(c_843,plain,(
    ! [A_125,A_10] :
      ( r2_hidden(A_125,A_10)
      | ~ r2_hidden(A_125,k3_xboole_0(A_10,k1_xboole_0))
      | r2_hidden(A_125,A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_803])).

tff(c_1036,plain,(
    ! [A_125,A_10] :
      ( r2_hidden(A_125,A_10)
      | ~ r2_hidden(A_125,k1_xboole_0)
      | r2_hidden(A_125,A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_843])).

tff(c_1396,plain,(
    ! [A_10] : r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),A_10) ),
    inference(resolution,[status(thm)],[c_1391,c_1036])).

tff(c_1399,plain,(
    ! [A_153] : r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),A_153) ),
    inference(resolution,[status(thm)],[c_1391,c_1036])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_275,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_284,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_275])).

tff(c_372,plain,(
    ! [A_83,B_2,A_1] :
      ( ~ r2_hidden(A_83,k3_xboole_0(B_2,A_1))
      | ~ r2_hidden(A_83,A_1)
      | ~ r2_hidden(A_83,k4_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_363])).

tff(c_1403,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k3_xboole_0(B_2,A_1))
      | ~ r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),A_1) ) ),
    inference(resolution,[status(thm)],[c_1399,c_372])).

tff(c_1434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1396,c_1403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.50  
% 3.08/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.51  %$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.08/1.51  
% 3.08/1.51  %Foreground sorts:
% 3.08/1.51  
% 3.08/1.51  
% 3.08/1.51  %Background operators:
% 3.08/1.51  
% 3.08/1.51  
% 3.08/1.51  %Foreground operators:
% 3.08/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.08/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.08/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.08/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.08/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.08/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.08/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.08/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.08/1.51  
% 3.08/1.52  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.08/1.52  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.08/1.52  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.08/1.52  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.08/1.52  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.08/1.52  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.08/1.52  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.08/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.08/1.52  tff(c_40, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.52  tff(c_90, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.08/1.52  tff(c_46, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.52  tff(c_106, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_46])).
% 3.08/1.52  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.52  tff(c_16, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.08/1.52  tff(c_211, plain, (![A_59, B_60, C_61]: (r2_hidden(k4_tarski(A_59, B_60), C_61) | ~r2_hidden(B_60, k11_relat_1(C_61, A_59)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.52  tff(c_24, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.08/1.52  tff(c_230, plain, (![A_62, C_63, B_64]: (r2_hidden(A_62, k1_relat_1(C_63)) | ~r2_hidden(B_64, k11_relat_1(C_63, A_62)) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_211, c_24])).
% 3.08/1.52  tff(c_239, plain, (![A_65, C_66]: (r2_hidden(A_65, k1_relat_1(C_66)) | ~v1_relat_1(C_66) | k11_relat_1(C_66, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_230])).
% 3.08/1.52  tff(c_250, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_239, c_90])).
% 3.08/1.52  tff(c_255, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_250])).
% 3.08/1.52  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_255])).
% 3.08/1.52  tff(c_258, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.08/1.52  tff(c_260, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.08/1.52  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_260])).
% 3.08/1.52  tff(c_267, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 3.08/1.52  tff(c_437, plain, (![C_97, A_98]: (r2_hidden(k4_tarski(C_97, '#skF_5'(A_98, k1_relat_1(A_98), C_97)), A_98) | ~r2_hidden(C_97, k1_relat_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.08/1.52  tff(c_36, plain, (![B_31, C_32, A_30]: (r2_hidden(B_31, k11_relat_1(C_32, A_30)) | ~r2_hidden(k4_tarski(A_30, B_31), C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.52  tff(c_1383, plain, (![A_151, C_152]: (r2_hidden('#skF_5'(A_151, k1_relat_1(A_151), C_152), k11_relat_1(A_151, C_152)) | ~v1_relat_1(A_151) | ~r2_hidden(C_152, k1_relat_1(A_151)))), inference(resolution, [status(thm)], [c_437, c_36])).
% 3.08/1.52  tff(c_1388, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_1383])).
% 3.08/1.52  tff(c_1391, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_267, c_38, c_1388])).
% 3.08/1.52  tff(c_20, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.08/1.52  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.52  tff(c_331, plain, (![A_77, B_78, C_79]: (r2_hidden(A_77, B_78) | ~r2_hidden(A_77, C_79) | r2_hidden(A_77, k5_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.52  tff(c_803, plain, (![A_125, A_126, B_127]: (r2_hidden(A_125, A_126) | ~r2_hidden(A_125, k3_xboole_0(A_126, B_127)) | r2_hidden(A_125, k4_xboole_0(A_126, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_331])).
% 3.08/1.52  tff(c_857, plain, (![A_128, A_129]: (r2_hidden(A_128, A_129) | ~r2_hidden(A_128, k3_xboole_0(A_129, k1_xboole_0)) | r2_hidden(A_128, A_129))), inference(superposition, [status(thm), theory('equality')], [c_20, c_803])).
% 3.08/1.52  tff(c_886, plain, (![A_130]: (r2_hidden('#skF_1'(k3_xboole_0(A_130, k1_xboole_0)), A_130) | k3_xboole_0(A_130, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_857])).
% 3.08/1.52  tff(c_363, plain, (![A_83, C_84, B_85]: (~r2_hidden(A_83, C_84) | ~r2_hidden(A_83, B_85) | ~r2_hidden(A_83, k5_xboole_0(B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.52  tff(c_523, plain, (![A_106, A_107, B_108]: (~r2_hidden(A_106, k3_xboole_0(A_107, B_108)) | ~r2_hidden(A_106, A_107) | ~r2_hidden(A_106, k4_xboole_0(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_363])).
% 3.08/1.52  tff(c_542, plain, (![A_109, A_110]: (~r2_hidden(A_109, k3_xboole_0(A_110, k1_xboole_0)) | ~r2_hidden(A_109, A_110) | ~r2_hidden(A_109, A_110))), inference(superposition, [status(thm), theory('equality')], [c_20, c_523])).
% 3.08/1.52  tff(c_565, plain, (![A_110]: (~r2_hidden('#skF_1'(k3_xboole_0(A_110, k1_xboole_0)), A_110) | k3_xboole_0(A_110, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_542])).
% 3.08/1.52  tff(c_947, plain, (![A_130]: (k3_xboole_0(A_130, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_886, c_565])).
% 3.08/1.52  tff(c_843, plain, (![A_125, A_10]: (r2_hidden(A_125, A_10) | ~r2_hidden(A_125, k3_xboole_0(A_10, k1_xboole_0)) | r2_hidden(A_125, A_10))), inference(superposition, [status(thm), theory('equality')], [c_20, c_803])).
% 3.08/1.52  tff(c_1036, plain, (![A_125, A_10]: (r2_hidden(A_125, A_10) | ~r2_hidden(A_125, k1_xboole_0) | r2_hidden(A_125, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_947, c_843])).
% 3.08/1.52  tff(c_1396, plain, (![A_10]: (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), A_10))), inference(resolution, [status(thm)], [c_1391, c_1036])).
% 3.08/1.52  tff(c_1399, plain, (![A_153]: (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), A_153))), inference(resolution, [status(thm)], [c_1391, c_1036])).
% 3.08/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.52  tff(c_275, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.52  tff(c_284, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_275])).
% 3.08/1.52  tff(c_372, plain, (![A_83, B_2, A_1]: (~r2_hidden(A_83, k3_xboole_0(B_2, A_1)) | ~r2_hidden(A_83, A_1) | ~r2_hidden(A_83, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_363])).
% 3.08/1.52  tff(c_1403, plain, (![B_2, A_1]: (~r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k3_xboole_0(B_2, A_1)) | ~r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), A_1))), inference(resolution, [status(thm)], [c_1399, c_372])).
% 3.08/1.52  tff(c_1434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1396, c_1403])).
% 3.08/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.52  
% 3.08/1.52  Inference rules
% 3.08/1.52  ----------------------
% 3.08/1.52  #Ref     : 0
% 3.08/1.52  #Sup     : 294
% 3.08/1.52  #Fact    : 0
% 3.08/1.52  #Define  : 0
% 3.08/1.52  #Split   : 3
% 3.08/1.52  #Chain   : 0
% 3.08/1.52  #Close   : 0
% 3.08/1.52  
% 3.08/1.52  Ordering : KBO
% 3.08/1.52  
% 3.08/1.52  Simplification rules
% 3.08/1.52  ----------------------
% 3.08/1.52  #Subsume      : 22
% 3.08/1.52  #Demod        : 120
% 3.08/1.52  #Tautology    : 106
% 3.08/1.52  #SimpNegUnit  : 2
% 3.08/1.52  #BackRed      : 4
% 3.08/1.52  
% 3.08/1.52  #Partial instantiations: 0
% 3.08/1.52  #Strategies tried      : 1
% 3.08/1.52  
% 3.08/1.52  Timing (in seconds)
% 3.08/1.52  ----------------------
% 3.08/1.52  Preprocessing        : 0.29
% 3.08/1.53  Parsing              : 0.15
% 3.08/1.53  CNF conversion       : 0.02
% 3.08/1.53  Main loop            : 0.47
% 3.08/1.53  Inferencing          : 0.17
% 3.08/1.53  Reduction            : 0.13
% 3.08/1.53  Demodulation         : 0.11
% 3.08/1.53  BG Simplification    : 0.03
% 3.08/1.53  Subsumption          : 0.10
% 3.08/1.53  Abstraction          : 0.02
% 3.08/1.53  MUC search           : 0.00
% 3.08/1.53  Cooper               : 0.00
% 3.08/1.53  Total                : 0.79
% 3.08/1.53  Index Insertion      : 0.00
% 3.08/1.53  Index Deletion       : 0.00
% 3.08/1.53  Index Matching       : 0.00
% 3.08/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
