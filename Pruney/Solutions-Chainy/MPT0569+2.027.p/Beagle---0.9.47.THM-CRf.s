%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 19.21s
% Output     : CNFRefutation 19.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  86 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 158 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_90,axiom,(
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

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_48,plain,
    ( k10_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_69,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9')
    | k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_75,plain,(
    k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42])).

tff(c_16,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_8'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_998,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden('#skF_8'(A_135,B_136,C_137),k2_relat_1(C_137))
      | ~ r2_hidden(A_135,k10_relat_1(C_137,B_136))
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,B_65)
      | ~ r2_hidden(C_66,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [C_66] :
      ( ~ r2_hidden(C_66,'#skF_9')
      | ~ r2_hidden(C_66,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_69,c_171])).

tff(c_1010,plain,(
    ! [A_135,B_136] :
      ( ~ r2_hidden('#skF_8'(A_135,B_136,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_135,k10_relat_1('#skF_10',B_136))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_998,c_184])).

tff(c_1043,plain,(
    ! [A_140,B_141] :
      ( ~ r2_hidden('#skF_8'(A_140,B_141,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_140,k10_relat_1('#skF_10',B_141)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1010])).

tff(c_1047,plain,(
    ! [A_35] :
      ( ~ r2_hidden(A_35,k10_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_1043])).

tff(c_1051,plain,(
    ! [A_142] : ~ r2_hidden(A_142,k10_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1047])).

tff(c_1075,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1051])).

tff(c_1084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1075])).

tff(c_1086,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_1095,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r1_xboole_0(A_143,B_144)
      | ~ r2_hidden(C_145,k3_xboole_0(A_143,B_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1098,plain,(
    ! [A_15,C_145] :
      ( ~ r1_xboole_0(A_15,k1_xboole_0)
      | ~ r2_hidden(C_145,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1095])).

tff(c_1108,plain,(
    ! [C_145] : ~ r2_hidden(C_145,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1098])).

tff(c_1085,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_20,plain,(
    ! [A_16,C_31] :
      ( r2_hidden(k4_tarski('#skF_7'(A_16,k2_relat_1(A_16),C_31),C_31),A_16)
      | ~ r2_hidden(C_31,k2_relat_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2084,plain,(
    ! [A_237,C_238,B_239,D_240] :
      ( r2_hidden(A_237,k10_relat_1(C_238,B_239))
      | ~ r2_hidden(D_240,B_239)
      | ~ r2_hidden(k4_tarski(A_237,D_240),C_238)
      | ~ r2_hidden(D_240,k2_relat_1(C_238))
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6944,plain,(
    ! [A_398,C_399,B_400,A_401] :
      ( r2_hidden(A_398,k10_relat_1(C_399,B_400))
      | ~ r2_hidden(k4_tarski(A_398,'#skF_1'(A_401,B_400)),C_399)
      | ~ r2_hidden('#skF_1'(A_401,B_400),k2_relat_1(C_399))
      | ~ v1_relat_1(C_399)
      | r1_xboole_0(A_401,B_400) ) ),
    inference(resolution,[status(thm)],[c_8,c_2084])).

tff(c_67307,plain,(
    ! [A_1221,A_1222,B_1223] :
      ( r2_hidden('#skF_7'(A_1221,k2_relat_1(A_1221),'#skF_1'(A_1222,B_1223)),k10_relat_1(A_1221,B_1223))
      | ~ v1_relat_1(A_1221)
      | r1_xboole_0(A_1222,B_1223)
      | ~ r2_hidden('#skF_1'(A_1222,B_1223),k2_relat_1(A_1221)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6944])).

tff(c_67583,plain,(
    ! [A_1222] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(A_1222,'#skF_9')),k1_xboole_0)
      | ~ v1_relat_1('#skF_10')
      | r1_xboole_0(A_1222,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1222,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_67307])).

tff(c_67628,plain,(
    ! [A_1222] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(A_1222,'#skF_9')),k1_xboole_0)
      | r1_xboole_0(A_1222,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1222,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_67583])).

tff(c_67630,plain,(
    ! [A_1224] :
      ( r1_xboole_0(A_1224,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1224,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1108,c_67628])).

tff(c_67634,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_67630])).

tff(c_67638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_1086,c_67634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.21/11.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.21/11.08  
% 19.21/11.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.21/11.08  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 19.21/11.08  
% 19.21/11.08  %Foreground sorts:
% 19.21/11.08  
% 19.21/11.08  
% 19.21/11.08  %Background operators:
% 19.21/11.08  
% 19.21/11.08  
% 19.21/11.08  %Foreground operators:
% 19.21/11.08  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 19.21/11.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.21/11.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.21/11.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 19.21/11.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.21/11.08  tff('#skF_10', type, '#skF_10': $i).
% 19.21/11.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.21/11.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.21/11.08  tff('#skF_9', type, '#skF_9': $i).
% 19.21/11.08  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 19.21/11.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.21/11.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.21/11.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.21/11.08  tff('#skF_3', type, '#skF_3': $i > $i).
% 19.21/11.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.21/11.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.21/11.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.21/11.08  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 19.21/11.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.21/11.08  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.21/11.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.21/11.08  
% 19.21/11.09  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 19.21/11.09  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 19.21/11.09  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 19.21/11.09  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 19.21/11.09  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 19.21/11.09  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 19.21/11.09  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 19.21/11.09  tff(f_79, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 19.21/11.09  tff(c_48, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.21/11.09  tff(c_69, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_48])).
% 19.21/11.09  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9') | k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.21/11.09  tff(c_75, plain, (k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42])).
% 19.21/11.09  tff(c_16, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.21/11.09  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.21/11.09  tff(c_34, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_8'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 19.21/11.09  tff(c_998, plain, (![A_135, B_136, C_137]: (r2_hidden('#skF_8'(A_135, B_136, C_137), k2_relat_1(C_137)) | ~r2_hidden(A_135, k10_relat_1(C_137, B_136)) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_90])).
% 19.21/11.09  tff(c_171, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, B_65) | ~r2_hidden(C_66, A_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.21/11.09  tff(c_184, plain, (![C_66]: (~r2_hidden(C_66, '#skF_9') | ~r2_hidden(C_66, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_69, c_171])).
% 19.21/11.09  tff(c_1010, plain, (![A_135, B_136]: (~r2_hidden('#skF_8'(A_135, B_136, '#skF_10'), '#skF_9') | ~r2_hidden(A_135, k10_relat_1('#skF_10', B_136)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_998, c_184])).
% 19.21/11.09  tff(c_1043, plain, (![A_140, B_141]: (~r2_hidden('#skF_8'(A_140, B_141, '#skF_10'), '#skF_9') | ~r2_hidden(A_140, k10_relat_1('#skF_10', B_141)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1010])).
% 19.21/11.09  tff(c_1047, plain, (![A_35]: (~r2_hidden(A_35, k10_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_1043])).
% 19.21/11.09  tff(c_1051, plain, (![A_142]: (~r2_hidden(A_142, k10_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1047])).
% 19.21/11.09  tff(c_1075, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_1051])).
% 19.21/11.09  tff(c_1084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_1075])).
% 19.21/11.09  tff(c_1086, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_48])).
% 19.21/11.09  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.21/11.09  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.21/11.09  tff(c_52, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.21/11.09  tff(c_60, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_52])).
% 19.21/11.09  tff(c_1095, plain, (![A_143, B_144, C_145]: (~r1_xboole_0(A_143, B_144) | ~r2_hidden(C_145, k3_xboole_0(A_143, B_144)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.21/11.09  tff(c_1098, plain, (![A_15, C_145]: (~r1_xboole_0(A_15, k1_xboole_0) | ~r2_hidden(C_145, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1095])).
% 19.21/11.09  tff(c_1108, plain, (![C_145]: (~r2_hidden(C_145, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1098])).
% 19.21/11.09  tff(c_1085, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 19.21/11.09  tff(c_20, plain, (![A_16, C_31]: (r2_hidden(k4_tarski('#skF_7'(A_16, k2_relat_1(A_16), C_31), C_31), A_16) | ~r2_hidden(C_31, k2_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.21/11.09  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.21/11.09  tff(c_2084, plain, (![A_237, C_238, B_239, D_240]: (r2_hidden(A_237, k10_relat_1(C_238, B_239)) | ~r2_hidden(D_240, B_239) | ~r2_hidden(k4_tarski(A_237, D_240), C_238) | ~r2_hidden(D_240, k2_relat_1(C_238)) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_90])).
% 19.21/11.09  tff(c_6944, plain, (![A_398, C_399, B_400, A_401]: (r2_hidden(A_398, k10_relat_1(C_399, B_400)) | ~r2_hidden(k4_tarski(A_398, '#skF_1'(A_401, B_400)), C_399) | ~r2_hidden('#skF_1'(A_401, B_400), k2_relat_1(C_399)) | ~v1_relat_1(C_399) | r1_xboole_0(A_401, B_400))), inference(resolution, [status(thm)], [c_8, c_2084])).
% 19.21/11.09  tff(c_67307, plain, (![A_1221, A_1222, B_1223]: (r2_hidden('#skF_7'(A_1221, k2_relat_1(A_1221), '#skF_1'(A_1222, B_1223)), k10_relat_1(A_1221, B_1223)) | ~v1_relat_1(A_1221) | r1_xboole_0(A_1222, B_1223) | ~r2_hidden('#skF_1'(A_1222, B_1223), k2_relat_1(A_1221)))), inference(resolution, [status(thm)], [c_20, c_6944])).
% 19.21/11.09  tff(c_67583, plain, (![A_1222]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(A_1222, '#skF_9')), k1_xboole_0) | ~v1_relat_1('#skF_10') | r1_xboole_0(A_1222, '#skF_9') | ~r2_hidden('#skF_1'(A_1222, '#skF_9'), k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1085, c_67307])).
% 19.21/11.09  tff(c_67628, plain, (![A_1222]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(A_1222, '#skF_9')), k1_xboole_0) | r1_xboole_0(A_1222, '#skF_9') | ~r2_hidden('#skF_1'(A_1222, '#skF_9'), k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_67583])).
% 19.21/11.09  tff(c_67630, plain, (![A_1224]: (r1_xboole_0(A_1224, '#skF_9') | ~r2_hidden('#skF_1'(A_1224, '#skF_9'), k2_relat_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_1108, c_67628])).
% 19.21/11.09  tff(c_67634, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_10, c_67630])).
% 19.21/11.09  tff(c_67638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1086, c_1086, c_67634])).
% 19.21/11.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.21/11.09  
% 19.21/11.09  Inference rules
% 19.21/11.09  ----------------------
% 19.21/11.09  #Ref     : 0
% 19.21/11.09  #Sup     : 17678
% 19.21/11.09  #Fact    : 0
% 19.21/11.09  #Define  : 0
% 19.21/11.09  #Split   : 7
% 19.21/11.09  #Chain   : 0
% 19.21/11.09  #Close   : 0
% 19.21/11.09  
% 19.21/11.09  Ordering : KBO
% 19.21/11.09  
% 19.21/11.09  Simplification rules
% 19.21/11.09  ----------------------
% 19.21/11.10  #Subsume      : 7109
% 19.21/11.10  #Demod        : 15049
% 19.21/11.10  #Tautology    : 6006
% 19.21/11.10  #SimpNegUnit  : 316
% 19.21/11.10  #BackRed      : 2
% 19.21/11.10  
% 19.21/11.10  #Partial instantiations: 0
% 19.21/11.10  #Strategies tried      : 1
% 19.21/11.10  
% 19.21/11.10  Timing (in seconds)
% 19.21/11.10  ----------------------
% 19.21/11.10  Preprocessing        : 0.31
% 19.21/11.10  Parsing              : 0.17
% 19.21/11.10  CNF conversion       : 0.03
% 19.21/11.10  Main loop            : 9.96
% 19.21/11.10  Inferencing          : 1.51
% 19.21/11.10  Reduction            : 1.63
% 19.21/11.10  Demodulation         : 1.10
% 19.21/11.10  BG Simplification    : 0.14
% 19.21/11.10  Subsumption          : 6.32
% 19.21/11.10  Abstraction          : 0.24
% 19.21/11.10  MUC search           : 0.00
% 19.21/11.10  Cooper               : 0.00
% 19.21/11.10  Total                : 10.30
% 19.21/11.10  Index Insertion      : 0.00
% 19.21/11.10  Index Deletion       : 0.00
% 19.21/11.10  Index Matching       : 0.00
% 19.21/11.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
