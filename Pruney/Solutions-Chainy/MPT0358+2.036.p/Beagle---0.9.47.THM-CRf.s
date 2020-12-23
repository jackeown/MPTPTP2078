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
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 136 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 200 expanded)
%              Number of equality atoms :   39 (  98 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_66,plain,(
    ! [A_31] : k1_subset_1(A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_81,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80])).

tff(c_147,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_44,plain,(
    ! [A_23] : k4_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,(
    ! [A_23] : k4_xboole_0('#skF_7',A_23) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_147,c_44])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_254,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | k4_xboole_0(A_54,B_55) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_28])).

tff(c_74,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_247,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_82])).

tff(c_257,plain,(
    k4_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_254,c_247])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_257])).

tff(c_263,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_262,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_316,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_323,plain,(
    k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_262,c_316])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_591,plain,(
    ! [D_88,A_89,B_90] :
      ( r2_hidden(D_88,A_89)
      | ~ r2_hidden(D_88,k4_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_728,plain,(
    ! [D_104,A_105,B_106] :
      ( r2_hidden(D_104,A_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_105,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_591])).

tff(c_4914,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_278,B_279)),A_278)
      | k3_xboole_0(A_278,B_279) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_728])).

tff(c_4985,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_4914])).

tff(c_5012,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_4985])).

tff(c_5013,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_5012])).

tff(c_302,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_309,plain,(
    k4_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_262,c_302])).

tff(c_878,plain,(
    ! [D_113,A_114,B_115] :
      ( r2_hidden(D_113,k4_xboole_0(A_114,B_115))
      | r2_hidden(D_113,B_115)
      | ~ r2_hidden(D_113,A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5807,plain,(
    ! [D_316] :
      ( r2_hidden(D_316,k1_xboole_0)
      | r2_hidden(D_316,k3_subset_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_316,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_878])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_757,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = k3_subset_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_777,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_757])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_782,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_4])).

tff(c_5859,plain,(
    ! [D_317] :
      ( r2_hidden(D_317,k1_xboole_0)
      | ~ r2_hidden(D_317,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5807,c_782])).

tff(c_38,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_633,plain,(
    ! [D_93,B_94,A_95] :
      ( ~ r2_hidden(D_93,B_94)
      | ~ r2_hidden(D_93,k4_xboole_0(A_95,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4119,plain,(
    ! [A_250,B_251] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_250,B_251)),B_251)
      | k4_xboole_0(A_250,B_251) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_633])).

tff(c_4172,plain,(
    ! [A_18] :
      ( ~ r2_hidden('#skF_3'(A_18),k1_xboole_0)
      | k4_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4119])).

tff(c_4193,plain,(
    ! [A_18] :
      ( ~ r2_hidden('#skF_3'(A_18),k1_xboole_0)
      | k1_xboole_0 = A_18 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4172])).

tff(c_5983,plain,(
    ! [A_321] :
      ( k1_xboole_0 = A_321
      | ~ r2_hidden('#skF_3'(A_321),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5859,c_4193])).

tff(c_5986,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5013,c_5983])).

tff(c_6008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_5986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.46/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.46/2.34  
% 6.46/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.46/2.34  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 6.46/2.34  
% 6.46/2.34  %Foreground sorts:
% 6.46/2.34  
% 6.46/2.34  
% 6.46/2.34  %Background operators:
% 6.46/2.34  
% 6.46/2.34  
% 6.46/2.34  %Foreground operators:
% 6.46/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.46/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.46/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.46/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.46/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.46/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.46/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.46/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.46/2.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.46/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.46/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.46/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.46/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.46/2.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.46/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.46/2.34  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.46/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.46/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.46/2.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.46/2.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.46/2.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.46/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.46/2.34  
% 6.46/2.36  tff(f_91, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.46/2.36  tff(f_105, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 6.46/2.36  tff(f_69, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.46/2.36  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.46/2.36  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.46/2.36  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.46/2.36  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.46/2.36  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.46/2.36  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.46/2.36  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.46/2.36  tff(c_66, plain, (![A_31]: (k1_subset_1(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.46/2.36  tff(c_80, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.46/2.36  tff(c_81, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80])).
% 6.46/2.36  tff(c_147, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_81])).
% 6.46/2.36  tff(c_44, plain, (![A_23]: (k4_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.46/2.36  tff(c_152, plain, (![A_23]: (k4_xboole_0('#skF_7', A_23)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_147, c_44])).
% 6.46/2.36  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.46/2.36  tff(c_254, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | k4_xboole_0(A_54, B_55)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_28])).
% 6.46/2.36  tff(c_74, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.46/2.36  tff(c_82, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74])).
% 6.46/2.36  tff(c_247, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_82])).
% 6.46/2.36  tff(c_257, plain, (k4_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))!='#skF_7'), inference(resolution, [status(thm)], [c_254, c_247])).
% 6.46/2.36  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_257])).
% 6.46/2.36  tff(c_263, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_81])).
% 6.46/2.36  tff(c_262, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_81])).
% 6.46/2.36  tff(c_316, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.46/2.36  tff(c_323, plain, (k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_262, c_316])).
% 6.46/2.36  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.46/2.36  tff(c_42, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.46/2.36  tff(c_591, plain, (![D_88, A_89, B_90]: (r2_hidden(D_88, A_89) | ~r2_hidden(D_88, k4_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.46/2.36  tff(c_728, plain, (![D_104, A_105, B_106]: (r2_hidden(D_104, A_105) | ~r2_hidden(D_104, k3_xboole_0(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_591])).
% 6.46/2.36  tff(c_4914, plain, (![A_278, B_279]: (r2_hidden('#skF_3'(k3_xboole_0(A_278, B_279)), A_278) | k3_xboole_0(A_278, B_279)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_728])).
% 6.46/2.36  tff(c_4985, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_323, c_4914])).
% 6.46/2.36  tff(c_5012, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_4985])).
% 6.46/2.36  tff(c_5013, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_263, c_5012])).
% 6.46/2.36  tff(c_302, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.46/2.36  tff(c_309, plain, (k4_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_262, c_302])).
% 6.46/2.36  tff(c_878, plain, (![D_113, A_114, B_115]: (r2_hidden(D_113, k4_xboole_0(A_114, B_115)) | r2_hidden(D_113, B_115) | ~r2_hidden(D_113, A_114))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.46/2.36  tff(c_5807, plain, (![D_316]: (r2_hidden(D_316, k1_xboole_0) | r2_hidden(D_316, k3_subset_1('#skF_6', '#skF_7')) | ~r2_hidden(D_316, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_878])).
% 6.46/2.36  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.46/2.36  tff(c_757, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=k3_subset_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.46/2.36  tff(c_777, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_757])).
% 6.46/2.36  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.46/2.36  tff(c_782, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | ~r2_hidden(D_6, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_777, c_4])).
% 6.46/2.36  tff(c_5859, plain, (![D_317]: (r2_hidden(D_317, k1_xboole_0) | ~r2_hidden(D_317, '#skF_7'))), inference(resolution, [status(thm)], [c_5807, c_782])).
% 6.46/2.36  tff(c_38, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.46/2.36  tff(c_633, plain, (![D_93, B_94, A_95]: (~r2_hidden(D_93, B_94) | ~r2_hidden(D_93, k4_xboole_0(A_95, B_94)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.46/2.36  tff(c_4119, plain, (![A_250, B_251]: (~r2_hidden('#skF_3'(k4_xboole_0(A_250, B_251)), B_251) | k4_xboole_0(A_250, B_251)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_633])).
% 6.46/2.36  tff(c_4172, plain, (![A_18]: (~r2_hidden('#skF_3'(A_18), k1_xboole_0) | k4_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_4119])).
% 6.46/2.36  tff(c_4193, plain, (![A_18]: (~r2_hidden('#skF_3'(A_18), k1_xboole_0) | k1_xboole_0=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4172])).
% 6.46/2.36  tff(c_5983, plain, (![A_321]: (k1_xboole_0=A_321 | ~r2_hidden('#skF_3'(A_321), '#skF_7'))), inference(resolution, [status(thm)], [c_5859, c_4193])).
% 6.46/2.36  tff(c_5986, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_5013, c_5983])).
% 6.46/2.36  tff(c_6008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_5986])).
% 6.46/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.46/2.36  
% 6.46/2.36  Inference rules
% 6.46/2.36  ----------------------
% 6.46/2.36  #Ref     : 0
% 6.46/2.36  #Sup     : 1321
% 6.46/2.36  #Fact    : 2
% 6.46/2.36  #Define  : 0
% 6.46/2.36  #Split   : 22
% 6.46/2.36  #Chain   : 0
% 6.46/2.36  #Close   : 0
% 6.46/2.36  
% 6.46/2.36  Ordering : KBO
% 6.46/2.36  
% 6.46/2.36  Simplification rules
% 6.46/2.36  ----------------------
% 6.46/2.36  #Subsume      : 212
% 6.46/2.36  #Demod        : 505
% 6.46/2.36  #Tautology    : 423
% 6.46/2.36  #SimpNegUnit  : 112
% 6.46/2.36  #BackRed      : 17
% 6.46/2.36  
% 6.46/2.36  #Partial instantiations: 0
% 6.46/2.36  #Strategies tried      : 1
% 6.46/2.36  
% 6.46/2.36  Timing (in seconds)
% 6.46/2.36  ----------------------
% 6.46/2.36  Preprocessing        : 0.34
% 6.46/2.36  Parsing              : 0.17
% 6.46/2.36  CNF conversion       : 0.03
% 6.46/2.36  Main loop            : 1.24
% 6.46/2.36  Inferencing          : 0.41
% 6.46/2.36  Reduction            : 0.42
% 6.46/2.36  Demodulation         : 0.29
% 6.46/2.36  BG Simplification    : 0.05
% 6.46/2.36  Subsumption          : 0.27
% 6.46/2.36  Abstraction          : 0.06
% 6.46/2.36  MUC search           : 0.00
% 6.46/2.36  Cooper               : 0.00
% 6.46/2.36  Total                : 1.62
% 6.46/2.36  Index Insertion      : 0.00
% 6.46/2.36  Index Deletion       : 0.00
% 6.46/2.36  Index Matching       : 0.00
% 6.46/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
