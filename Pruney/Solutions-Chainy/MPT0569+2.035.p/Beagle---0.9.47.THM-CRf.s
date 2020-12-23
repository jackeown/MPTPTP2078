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
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 23.50s
% Output     : CNFRefutation 23.54s
% Verified   : 
% Statistics : Number of formulae       :   65 (  90 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 166 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
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

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9')
    | k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_51,plain,(
    k10_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_8'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k10_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_913,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_8'(A_123,B_124,C_125),k2_relat_1(C_125))
      | ~ r2_hidden(A_123,k10_relat_1(C_125,B_124))
      | ~ v1_relat_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,
    ( k10_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_48])).

tff(c_144,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,B_58)
      | ~ r2_hidden(C_59,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,(
    ! [C_59] :
      ( ~ r2_hidden(C_59,'#skF_9')
      | ~ r2_hidden(C_59,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_82,c_144])).

tff(c_921,plain,(
    ! [A_123,B_124] :
      ( ~ r2_hidden('#skF_8'(A_123,B_124,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_123,k10_relat_1('#skF_10',B_124))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_913,c_152])).

tff(c_1816,plain,(
    ! [A_170,B_171] :
      ( ~ r2_hidden('#skF_8'(A_170,B_171,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_170,k10_relat_1('#skF_10',B_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_921])).

tff(c_1820,plain,(
    ! [A_33] :
      ( ~ r2_hidden(A_33,k10_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_1816])).

tff(c_1824,plain,(
    ! [A_172] : ~ r2_hidden(A_172,k10_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1820])).

tff(c_1852,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1824])).

tff(c_1862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1852])).

tff(c_1863,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1869,plain,(
    ! [A_173,B_174,C_175] :
      ( ~ r1_xboole_0(A_173,B_174)
      | ~ r2_hidden(C_175,k3_xboole_0(A_173,B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1875,plain,(
    ! [A_176,B_177] :
      ( ~ r1_xboole_0(A_176,B_177)
      | k3_xboole_0(A_176,B_177) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_1869])).

tff(c_1886,plain,(
    ! [A_180] : k3_xboole_0(A_180,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1875])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1891,plain,(
    ! [A_180,C_10] :
      ( ~ r1_xboole_0(A_180,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1886,c_10])).

tff(c_1896,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1891])).

tff(c_1864,plain,(
    k10_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_16,plain,(
    ! [A_14,C_29] :
      ( r2_hidden(k4_tarski('#skF_7'(A_14,k2_relat_1(A_14),C_29),C_29),A_14)
      | ~ r2_hidden(C_29,k2_relat_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2699,plain,(
    ! [A_252,C_253,B_254,D_255] :
      ( r2_hidden(A_252,k10_relat_1(C_253,B_254))
      | ~ r2_hidden(D_255,B_254)
      | ~ r2_hidden(k4_tarski(A_252,D_255),C_253)
      | ~ r2_hidden(D_255,k2_relat_1(C_253))
      | ~ v1_relat_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12600,plain,(
    ! [A_523,C_524,B_525,A_526] :
      ( r2_hidden(A_523,k10_relat_1(C_524,B_525))
      | ~ r2_hidden(k4_tarski(A_523,'#skF_1'(A_526,B_525)),C_524)
      | ~ r2_hidden('#skF_1'(A_526,B_525),k2_relat_1(C_524))
      | ~ v1_relat_1(C_524)
      | r1_xboole_0(A_526,B_525) ) ),
    inference(resolution,[status(thm)],[c_4,c_2699])).

tff(c_95120,plain,(
    ! [A_1249,A_1250,B_1251] :
      ( r2_hidden('#skF_7'(A_1249,k2_relat_1(A_1249),'#skF_1'(A_1250,B_1251)),k10_relat_1(A_1249,B_1251))
      | ~ v1_relat_1(A_1249)
      | r1_xboole_0(A_1250,B_1251)
      | ~ r2_hidden('#skF_1'(A_1250,B_1251),k2_relat_1(A_1249)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12600])).

tff(c_95416,plain,(
    ! [A_1250] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(A_1250,'#skF_9')),k1_xboole_0)
      | ~ v1_relat_1('#skF_10')
      | r1_xboole_0(A_1250,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1250,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_95120])).

tff(c_95451,plain,(
    ! [A_1250] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(A_1250,'#skF_9')),k1_xboole_0)
      | r1_xboole_0(A_1250,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1250,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95416])).

tff(c_95453,plain,(
    ! [A_1252] :
      ( r1_xboole_0(A_1252,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_1252,'#skF_9'),k2_relat_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1896,c_95451])).

tff(c_95457,plain,(
    r1_xboole_0(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_95453])).

tff(c_95461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1863,c_1863,c_95457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.50/14.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.50/14.41  
% 23.50/14.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.54/14.41  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 23.54/14.41  
% 23.54/14.41  %Foreground sorts:
% 23.54/14.41  
% 23.54/14.41  
% 23.54/14.41  %Background operators:
% 23.54/14.41  
% 23.54/14.41  
% 23.54/14.41  %Foreground operators:
% 23.54/14.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 23.54/14.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.54/14.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.54/14.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.54/14.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.54/14.41  tff('#skF_10', type, '#skF_10': $i).
% 23.54/14.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.54/14.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.54/14.41  tff('#skF_9', type, '#skF_9': $i).
% 23.54/14.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 23.54/14.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.54/14.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 23.54/14.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.54/14.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 23.54/14.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.54/14.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 23.54/14.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.54/14.41  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 23.54/14.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 23.54/14.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 23.54/14.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.54/14.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.54/14.41  
% 23.54/14.42  tff(f_101, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 23.54/14.42  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 23.54/14.42  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 23.54/14.42  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 23.54/14.42  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 23.54/14.42  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 23.54/14.42  tff(f_75, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 23.54/14.42  tff(c_42, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9') | k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.54/14.42  tff(c_51, plain, (k10_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 23.54/14.42  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.54/14.42  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.54/14.42  tff(c_30, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_8'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k10_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.54/14.42  tff(c_913, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_8'(A_123, B_124, C_125), k2_relat_1(C_125)) | ~r2_hidden(A_123, k10_relat_1(C_125, B_124)) | ~v1_relat_1(C_125))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.54/14.42  tff(c_48, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.54/14.42  tff(c_82, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_51, c_48])).
% 23.54/14.42  tff(c_144, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, B_58) | ~r2_hidden(C_59, A_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.54/14.42  tff(c_152, plain, (![C_59]: (~r2_hidden(C_59, '#skF_9') | ~r2_hidden(C_59, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_82, c_144])).
% 23.54/14.42  tff(c_921, plain, (![A_123, B_124]: (~r2_hidden('#skF_8'(A_123, B_124, '#skF_10'), '#skF_9') | ~r2_hidden(A_123, k10_relat_1('#skF_10', B_124)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_913, c_152])).
% 23.54/14.42  tff(c_1816, plain, (![A_170, B_171]: (~r2_hidden('#skF_8'(A_170, B_171, '#skF_10'), '#skF_9') | ~r2_hidden(A_170, k10_relat_1('#skF_10', B_171)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_921])).
% 23.54/14.42  tff(c_1820, plain, (![A_33]: (~r2_hidden(A_33, k10_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_1816])).
% 23.54/14.42  tff(c_1824, plain, (![A_172]: (~r2_hidden(A_172, k10_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1820])).
% 23.54/14.42  tff(c_1852, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_1824])).
% 23.54/14.42  tff(c_1862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1852])).
% 23.54/14.42  tff(c_1863, plain, (~r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_42])).
% 23.54/14.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.54/14.42  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.54/14.42  tff(c_1869, plain, (![A_173, B_174, C_175]: (~r1_xboole_0(A_173, B_174) | ~r2_hidden(C_175, k3_xboole_0(A_173, B_174)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.54/14.42  tff(c_1875, plain, (![A_176, B_177]: (~r1_xboole_0(A_176, B_177) | k3_xboole_0(A_176, B_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1869])).
% 23.54/14.42  tff(c_1886, plain, (![A_180]: (k3_xboole_0(A_180, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1875])).
% 23.54/14.42  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.54/14.42  tff(c_1891, plain, (![A_180, C_10]: (~r1_xboole_0(A_180, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1886, c_10])).
% 23.54/14.42  tff(c_1896, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1891])).
% 23.54/14.42  tff(c_1864, plain, (k10_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 23.54/14.42  tff(c_16, plain, (![A_14, C_29]: (r2_hidden(k4_tarski('#skF_7'(A_14, k2_relat_1(A_14), C_29), C_29), A_14) | ~r2_hidden(C_29, k2_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.54/14.42  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.54/14.42  tff(c_2699, plain, (![A_252, C_253, B_254, D_255]: (r2_hidden(A_252, k10_relat_1(C_253, B_254)) | ~r2_hidden(D_255, B_254) | ~r2_hidden(k4_tarski(A_252, D_255), C_253) | ~r2_hidden(D_255, k2_relat_1(C_253)) | ~v1_relat_1(C_253))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.54/14.42  tff(c_12600, plain, (![A_523, C_524, B_525, A_526]: (r2_hidden(A_523, k10_relat_1(C_524, B_525)) | ~r2_hidden(k4_tarski(A_523, '#skF_1'(A_526, B_525)), C_524) | ~r2_hidden('#skF_1'(A_526, B_525), k2_relat_1(C_524)) | ~v1_relat_1(C_524) | r1_xboole_0(A_526, B_525))), inference(resolution, [status(thm)], [c_4, c_2699])).
% 23.54/14.42  tff(c_95120, plain, (![A_1249, A_1250, B_1251]: (r2_hidden('#skF_7'(A_1249, k2_relat_1(A_1249), '#skF_1'(A_1250, B_1251)), k10_relat_1(A_1249, B_1251)) | ~v1_relat_1(A_1249) | r1_xboole_0(A_1250, B_1251) | ~r2_hidden('#skF_1'(A_1250, B_1251), k2_relat_1(A_1249)))), inference(resolution, [status(thm)], [c_16, c_12600])).
% 23.54/14.42  tff(c_95416, plain, (![A_1250]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(A_1250, '#skF_9')), k1_xboole_0) | ~v1_relat_1('#skF_10') | r1_xboole_0(A_1250, '#skF_9') | ~r2_hidden('#skF_1'(A_1250, '#skF_9'), k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_95120])).
% 23.54/14.42  tff(c_95451, plain, (![A_1250]: (r2_hidden('#skF_7'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(A_1250, '#skF_9')), k1_xboole_0) | r1_xboole_0(A_1250, '#skF_9') | ~r2_hidden('#skF_1'(A_1250, '#skF_9'), k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95416])).
% 23.54/14.42  tff(c_95453, plain, (![A_1252]: (r1_xboole_0(A_1252, '#skF_9') | ~r2_hidden('#skF_1'(A_1252, '#skF_9'), k2_relat_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_1896, c_95451])).
% 23.54/14.42  tff(c_95457, plain, (r1_xboole_0(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_6, c_95453])).
% 23.54/14.42  tff(c_95461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1863, c_1863, c_95457])).
% 23.54/14.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.54/14.42  
% 23.54/14.42  Inference rules
% 23.54/14.42  ----------------------
% 23.54/14.42  #Ref     : 0
% 23.54/14.42  #Sup     : 25477
% 23.54/14.42  #Fact    : 0
% 23.54/14.42  #Define  : 0
% 23.54/14.42  #Split   : 16
% 23.54/14.42  #Chain   : 0
% 23.54/14.42  #Close   : 0
% 23.54/14.42  
% 23.54/14.42  Ordering : KBO
% 23.54/14.42  
% 23.54/14.42  Simplification rules
% 23.54/14.42  ----------------------
% 23.54/14.42  #Subsume      : 10086
% 23.54/14.42  #Demod        : 27959
% 23.54/14.42  #Tautology    : 10076
% 23.54/14.42  #SimpNegUnit  : 301
% 23.54/14.42  #BackRed      : 2
% 23.54/14.42  
% 23.54/14.42  #Partial instantiations: 0
% 23.54/14.42  #Strategies tried      : 1
% 23.54/14.42  
% 23.54/14.42  Timing (in seconds)
% 23.54/14.42  ----------------------
% 23.61/14.42  Preprocessing        : 0.30
% 23.61/14.42  Parsing              : 0.16
% 23.61/14.42  CNF conversion       : 0.02
% 23.61/14.42  Main loop            : 13.36
% 23.61/14.42  Inferencing          : 1.89
% 23.61/14.42  Reduction            : 2.17
% 23.61/14.42  Demodulation         : 1.52
% 23.61/14.42  BG Simplification    : 0.17
% 23.61/14.42  Subsumption          : 8.70
% 23.61/14.43  Abstraction          : 0.31
% 23.61/14.43  MUC search           : 0.00
% 23.61/14.43  Cooper               : 0.00
% 23.61/14.43  Total                : 13.69
% 23.61/14.43  Index Insertion      : 0.00
% 23.61/14.43  Index Deletion       : 0.00
% 23.61/14.43  Index Matching       : 0.00
% 23.61/14.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
