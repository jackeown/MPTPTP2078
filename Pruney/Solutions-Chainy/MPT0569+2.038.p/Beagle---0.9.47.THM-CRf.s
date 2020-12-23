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
% DateTime   : Thu Dec  3 10:01:40 EST 2020

% Result     : Theorem 13.90s
% Output     : CNFRefutation 14.05s
% Verified   : 
% Statistics : Number of formulae       :   62 (  90 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 180 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_84,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_44,plain,
    ( k10_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_67,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5')
    | k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_38])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_4'(A_18,B_19,C_20),B_19)
      | ~ r2_hidden(A_18,k10_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_492,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden('#skF_4'(A_100,B_101,C_102),k2_relat_1(C_102))
      | ~ r2_hidden(A_100,k10_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [C_40] :
      ( ~ r2_hidden(C_40,'#skF_5')
      | ~ r2_hidden(C_40,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_67,c_86])).

tff(c_496,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden('#skF_4'(A_100,B_101,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_100,k10_relat_1('#skF_6',B_101))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_492,c_94])).

tff(c_500,plain,(
    ! [A_103,B_104] :
      ( ~ r2_hidden('#skF_4'(A_103,B_104,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_103,k10_relat_1('#skF_6',B_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_496])).

tff(c_504,plain,(
    ! [A_18] :
      ( ~ r2_hidden(A_18,k10_relat_1('#skF_6','#skF_5'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_500])).

tff(c_508,plain,(
    ! [A_105] : ~ r2_hidden(A_105,k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_504])).

tff(c_528,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_508])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_528])).

tff(c_537,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_544,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | ~ r1_xboole_0(k1_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [A_29] : ~ r2_hidden(A_29,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_3'(A_11,B_12,C_13),A_11),C_13)
      | ~ r2_hidden(A_11,k9_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1093,plain,(
    ! [A_177,C_178,B_179,D_180] :
      ( r2_hidden(A_177,k10_relat_1(C_178,B_179))
      | ~ r2_hidden(D_180,B_179)
      | ~ r2_hidden(k4_tarski(A_177,D_180),C_178)
      | ~ r2_hidden(D_180,k2_relat_1(C_178))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2516,plain,(
    ! [A_330,C_331,B_332,A_333] :
      ( r2_hidden(A_330,k10_relat_1(C_331,B_332))
      | ~ r2_hidden(k4_tarski(A_330,'#skF_1'(A_333,B_332)),C_331)
      | ~ r2_hidden('#skF_1'(A_333,B_332),k2_relat_1(C_331))
      | ~ v1_relat_1(C_331)
      | r1_xboole_0(A_333,B_332) ) ),
    inference(resolution,[status(thm)],[c_4,c_1093])).

tff(c_15779,plain,(
    ! [A_1156,B_1157,B_1158,C_1159] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1156,B_1157),B_1158,C_1159),k10_relat_1(C_1159,B_1157))
      | ~ r2_hidden('#skF_1'(A_1156,B_1157),k2_relat_1(C_1159))
      | r1_xboole_0(A_1156,B_1157)
      | ~ r2_hidden('#skF_1'(A_1156,B_1157),k9_relat_1(C_1159,B_1158))
      | ~ v1_relat_1(C_1159) ) ),
    inference(resolution,[status(thm)],[c_18,c_2516])).

tff(c_15912,plain,(
    ! [A_1156,B_1158] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1156,'#skF_5'),B_1158,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1156,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1156,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1156,'#skF_5'),k9_relat_1('#skF_6',B_1158))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_15779])).

tff(c_15955,plain,(
    ! [A_1156,B_1158] :
      ( r2_hidden('#skF_3'('#skF_1'(A_1156,'#skF_5'),B_1158,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1156,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1156,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1156,'#skF_5'),k9_relat_1('#skF_6',B_1158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15912])).

tff(c_16053,plain,(
    ! [A_1161,B_1162] :
      ( ~ r2_hidden('#skF_1'(A_1161,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1161,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1161,'#skF_5'),k9_relat_1('#skF_6',B_1162)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15955])).

tff(c_16131,plain,(
    ! [A_1161] :
      ( ~ r2_hidden('#skF_1'(A_1161,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_1161,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1161,'#skF_5'),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_16053])).

tff(c_16173,plain,(
    ! [A_1163] :
      ( r1_xboole_0(A_1163,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1163,'#skF_5'),k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16131])).

tff(c_16185,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_16173])).

tff(c_16196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_544,c_16185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n022.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 20:11:40 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.90/6.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/6.69  
% 13.90/6.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/6.69  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 13.90/6.69  
% 13.90/6.69  %Foreground sorts:
% 13.90/6.69  
% 13.90/6.69  
% 13.90/6.69  %Background operators:
% 13.90/6.69  
% 13.90/6.69  
% 13.90/6.69  %Foreground operators:
% 13.90/6.69  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.90/6.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.90/6.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.90/6.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.90/6.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.90/6.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.90/6.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.90/6.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.90/6.69  tff('#skF_5', type, '#skF_5': $i).
% 13.90/6.69  tff('#skF_6', type, '#skF_6': $i).
% 13.90/6.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.90/6.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.90/6.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.90/6.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.90/6.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.90/6.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.90/6.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.90/6.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.90/6.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.90/6.69  
% 14.05/6.71  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 14.05/6.71  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.05/6.71  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 14.05/6.71  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.05/6.71  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 14.05/6.71  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 14.05/6.71  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 14.05/6.71  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 14.05/6.71  tff(c_44, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.05/6.71  tff(c_67, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 14.05/6.71  tff(c_38, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5') | k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.05/6.71  tff(c_75, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_67, c_38])).
% 14.05/6.71  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.05/6.71  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.05/6.71  tff(c_26, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_4'(A_18, B_19, C_20), B_19) | ~r2_hidden(A_18, k10_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.05/6.71  tff(c_492, plain, (![A_100, B_101, C_102]: (r2_hidden('#skF_4'(A_100, B_101, C_102), k2_relat_1(C_102)) | ~r2_hidden(A_100, k10_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.05/6.71  tff(c_86, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.05/6.71  tff(c_94, plain, (![C_40]: (~r2_hidden(C_40, '#skF_5') | ~r2_hidden(C_40, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_67, c_86])).
% 14.05/6.71  tff(c_496, plain, (![A_100, B_101]: (~r2_hidden('#skF_4'(A_100, B_101, '#skF_6'), '#skF_5') | ~r2_hidden(A_100, k10_relat_1('#skF_6', B_101)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_492, c_94])).
% 14.05/6.71  tff(c_500, plain, (![A_103, B_104]: (~r2_hidden('#skF_4'(A_103, B_104, '#skF_6'), '#skF_5') | ~r2_hidden(A_103, k10_relat_1('#skF_6', B_104)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_496])).
% 14.05/6.71  tff(c_504, plain, (![A_18]: (~r2_hidden(A_18, k10_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_500])).
% 14.05/6.71  tff(c_508, plain, (![A_105]: (~r2_hidden(A_105, k10_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_504])).
% 14.05/6.71  tff(c_528, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_508])).
% 14.05/6.71  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_528])).
% 14.05/6.71  tff(c_537, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 14.05/6.71  tff(c_544, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_38])).
% 14.05/6.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.05/6.71  tff(c_22, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.05/6.71  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.05/6.71  tff(c_47, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | ~r1_xboole_0(k1_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.05/6.71  tff(c_52, plain, (![A_29]: (~r2_hidden(A_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_47])).
% 14.05/6.71  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden(k4_tarski('#skF_3'(A_11, B_12, C_13), A_11), C_13) | ~r2_hidden(A_11, k9_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.05/6.71  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.05/6.71  tff(c_1093, plain, (![A_177, C_178, B_179, D_180]: (r2_hidden(A_177, k10_relat_1(C_178, B_179)) | ~r2_hidden(D_180, B_179) | ~r2_hidden(k4_tarski(A_177, D_180), C_178) | ~r2_hidden(D_180, k2_relat_1(C_178)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.05/6.71  tff(c_2516, plain, (![A_330, C_331, B_332, A_333]: (r2_hidden(A_330, k10_relat_1(C_331, B_332)) | ~r2_hidden(k4_tarski(A_330, '#skF_1'(A_333, B_332)), C_331) | ~r2_hidden('#skF_1'(A_333, B_332), k2_relat_1(C_331)) | ~v1_relat_1(C_331) | r1_xboole_0(A_333, B_332))), inference(resolution, [status(thm)], [c_4, c_1093])).
% 14.05/6.71  tff(c_15779, plain, (![A_1156, B_1157, B_1158, C_1159]: (r2_hidden('#skF_3'('#skF_1'(A_1156, B_1157), B_1158, C_1159), k10_relat_1(C_1159, B_1157)) | ~r2_hidden('#skF_1'(A_1156, B_1157), k2_relat_1(C_1159)) | r1_xboole_0(A_1156, B_1157) | ~r2_hidden('#skF_1'(A_1156, B_1157), k9_relat_1(C_1159, B_1158)) | ~v1_relat_1(C_1159))), inference(resolution, [status(thm)], [c_18, c_2516])).
% 14.05/6.71  tff(c_15912, plain, (![A_1156, B_1158]: (r2_hidden('#skF_3'('#skF_1'(A_1156, '#skF_5'), B_1158, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1156, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1156, '#skF_5') | ~r2_hidden('#skF_1'(A_1156, '#skF_5'), k9_relat_1('#skF_6', B_1158)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_15779])).
% 14.05/6.71  tff(c_15955, plain, (![A_1156, B_1158]: (r2_hidden('#skF_3'('#skF_1'(A_1156, '#skF_5'), B_1158, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1156, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1156, '#skF_5') | ~r2_hidden('#skF_1'(A_1156, '#skF_5'), k9_relat_1('#skF_6', B_1158)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_15912])).
% 14.05/6.71  tff(c_16053, plain, (![A_1161, B_1162]: (~r2_hidden('#skF_1'(A_1161, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1161, '#skF_5') | ~r2_hidden('#skF_1'(A_1161, '#skF_5'), k9_relat_1('#skF_6', B_1162)))), inference(negUnitSimplification, [status(thm)], [c_52, c_15955])).
% 14.05/6.71  tff(c_16131, plain, (![A_1161]: (~r2_hidden('#skF_1'(A_1161, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_1161, '#skF_5') | ~r2_hidden('#skF_1'(A_1161, '#skF_5'), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_16053])).
% 14.05/6.71  tff(c_16173, plain, (![A_1163]: (r1_xboole_0(A_1163, '#skF_5') | ~r2_hidden('#skF_1'(A_1163, '#skF_5'), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16131])).
% 14.05/6.71  tff(c_16185, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_16173])).
% 14.05/6.71  tff(c_16196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_544, c_16185])).
% 14.05/6.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.05/6.71  
% 14.05/6.71  Inference rules
% 14.05/6.71  ----------------------
% 14.05/6.71  #Ref     : 0
% 14.05/6.71  #Sup     : 3700
% 14.05/6.71  #Fact    : 0
% 14.05/6.71  #Define  : 0
% 14.05/6.71  #Split   : 16
% 14.05/6.71  #Chain   : 0
% 14.05/6.71  #Close   : 0
% 14.05/6.71  
% 14.05/6.71  Ordering : KBO
% 14.05/6.71  
% 14.05/6.71  Simplification rules
% 14.05/6.71  ----------------------
% 14.05/6.71  #Subsume      : 2013
% 14.05/6.71  #Demod        : 1114
% 14.05/6.71  #Tautology    : 711
% 14.05/6.71  #SimpNegUnit  : 97
% 14.05/6.71  #BackRed      : 0
% 14.05/6.71  
% 14.05/6.71  #Partial instantiations: 0
% 14.05/6.71  #Strategies tried      : 1
% 14.05/6.71  
% 14.05/6.71  Timing (in seconds)
% 14.05/6.71  ----------------------
% 14.05/6.71  Preprocessing        : 0.31
% 14.05/6.71  Parsing              : 0.17
% 14.05/6.71  CNF conversion       : 0.02
% 14.05/6.71  Main loop            : 5.68
% 14.05/6.71  Inferencing          : 0.86
% 14.05/6.71  Reduction            : 0.54
% 14.05/6.71  Demodulation         : 0.35
% 14.05/6.71  BG Simplification    : 0.06
% 14.05/6.71  Subsumption          : 4.08
% 14.05/6.71  Abstraction          : 0.08
% 14.05/6.71  MUC search           : 0.00
% 14.05/6.71  Cooper               : 0.00
% 14.05/6.71  Total                : 6.02
% 14.05/6.71  Index Insertion      : 0.00
% 14.05/6.71  Index Deletion       : 0.00
% 14.05/6.71  Index Matching       : 0.00
% 14.05/6.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
