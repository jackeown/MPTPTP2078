%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 149 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_96,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_74,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_62,axiom,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_33] : k1_subset_1(A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72,plain,
    ( k1_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_79,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_147,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_79])).

tff(c_42,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_42])).

tff(c_317,plain,(
    ! [A_79,B_80] :
      ( ~ r2_hidden('#skF_1'(A_79,B_80),B_80)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_333,plain,(
    ! [A_81] : r1_tarski(A_81,A_81) ),
    inference(resolution,[status(thm)],[c_8,c_317])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_338,plain,(
    ! [A_82] : k3_xboole_0(A_82,A_82) = A_82 ),
    inference(resolution,[status(thm)],[c_333,c_36])).

tff(c_34,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_344,plain,(
    ! [A_82] : k5_xboole_0(A_82,A_82) = k4_xboole_0(A_82,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_34])).

tff(c_351,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_344])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_400,plain,(
    ! [D_88,A_89] :
      ( r2_hidden(D_88,A_89)
      | ~ r2_hidden(D_88,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_14])).

tff(c_525,plain,(
    ! [B_98,A_99] :
      ( r2_hidden('#skF_1'('#skF_8',B_98),A_99)
      | r1_tarski('#skF_8',B_98) ) ),
    inference(resolution,[status(thm)],[c_8,c_400])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_560,plain,(
    ! [A_99] : r1_tarski('#skF_8',A_99) ),
    inference(resolution,[status(thm)],[c_525,c_6])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_145])).

tff(c_570,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),A_14)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1050,plain,(
    ! [A_153,B_154] :
      ( k4_xboole_0(A_153,B_154) = k3_subset_1(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1063,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1050])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1101,plain,(
    ! [D_156] :
      ( ~ r2_hidden(D_156,'#skF_8')
      | ~ r2_hidden(D_156,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_12])).

tff(c_2667,plain,(
    ! [A_249] :
      ( ~ r2_hidden('#skF_4'(A_249,k3_subset_1('#skF_7','#skF_8')),'#skF_8')
      | r1_xboole_0(A_249,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_30,c_1101])).

tff(c_2676,plain,(
    r1_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_32,c_2667])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2683,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2676,c_38])).

tff(c_571,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_573,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0(A_102,B_103) = A_102
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_577,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_571,c_573])).

tff(c_589,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_598,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = k5_xboole_0('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_589])).

tff(c_607,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_598])).

tff(c_2684,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_607])).

tff(c_2686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_2684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.73  
% 3.98/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.98/1.73  
% 3.98/1.73  %Foreground sorts:
% 3.98/1.73  
% 3.98/1.73  
% 3.98/1.73  %Background operators:
% 3.98/1.73  
% 3.98/1.73  
% 3.98/1.73  %Foreground operators:
% 3.98/1.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.98/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.73  tff('#skF_7', type, '#skF_7': $i).
% 3.98/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.73  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.98/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.98/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.98/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.73  tff('#skF_8', type, '#skF_8': $i).
% 3.98/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.98/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.73  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.98/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.98/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.98/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.73  
% 3.98/1.74  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.98/1.74  tff(f_96, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.98/1.74  tff(f_110, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.98/1.74  tff(f_74, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.98/1.74  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.98/1.74  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.98/1.74  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.98/1.74  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.98/1.74  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.98/1.74  tff(f_72, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.98/1.74  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.74  tff(c_64, plain, (![A_33]: (k1_subset_1(A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.98/1.74  tff(c_72, plain, (k1_subset_1('#skF_7')!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.74  tff(c_80, plain, (k1_xboole_0!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 3.98/1.74  tff(c_145, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_80])).
% 3.98/1.74  tff(c_78, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.74  tff(c_79, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_78])).
% 3.98/1.74  tff(c_147, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_145, c_79])).
% 3.98/1.74  tff(c_42, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.98/1.74  tff(c_148, plain, (![A_25]: (k5_xboole_0(A_25, A_25)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_42])).
% 3.98/1.74  tff(c_317, plain, (![A_79, B_80]: (~r2_hidden('#skF_1'(A_79, B_80), B_80) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.74  tff(c_333, plain, (![A_81]: (r1_tarski(A_81, A_81))), inference(resolution, [status(thm)], [c_8, c_317])).
% 3.98/1.74  tff(c_36, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.74  tff(c_338, plain, (![A_82]: (k3_xboole_0(A_82, A_82)=A_82)), inference(resolution, [status(thm)], [c_333, c_36])).
% 3.98/1.74  tff(c_34, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.74  tff(c_344, plain, (![A_82]: (k5_xboole_0(A_82, A_82)=k4_xboole_0(A_82, A_82))), inference(superposition, [status(thm), theory('equality')], [c_338, c_34])).
% 3.98/1.74  tff(c_351, plain, (![A_83]: (k4_xboole_0(A_83, A_83)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_344])).
% 3.98/1.74  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.98/1.74  tff(c_400, plain, (![D_88, A_89]: (r2_hidden(D_88, A_89) | ~r2_hidden(D_88, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_14])).
% 3.98/1.74  tff(c_525, plain, (![B_98, A_99]: (r2_hidden('#skF_1'('#skF_8', B_98), A_99) | r1_tarski('#skF_8', B_98))), inference(resolution, [status(thm)], [c_8, c_400])).
% 3.98/1.74  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.74  tff(c_560, plain, (![A_99]: (r1_tarski('#skF_8', A_99))), inference(resolution, [status(thm)], [c_525, c_6])).
% 3.98/1.74  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_145])).
% 3.98/1.74  tff(c_570, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 3.98/1.74  tff(c_32, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), A_14) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.74  tff(c_30, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.98/1.74  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.74  tff(c_1050, plain, (![A_153, B_154]: (k4_xboole_0(A_153, B_154)=k3_subset_1(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.98/1.74  tff(c_1063, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_1050])).
% 3.98/1.74  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.98/1.74  tff(c_1101, plain, (![D_156]: (~r2_hidden(D_156, '#skF_8') | ~r2_hidden(D_156, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_12])).
% 3.98/1.74  tff(c_2667, plain, (![A_249]: (~r2_hidden('#skF_4'(A_249, k3_subset_1('#skF_7', '#skF_8')), '#skF_8') | r1_xboole_0(A_249, k3_subset_1('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_30, c_1101])).
% 3.98/1.74  tff(c_2676, plain, (r1_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_32, c_2667])).
% 3.98/1.74  tff(c_38, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.98/1.74  tff(c_2683, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_2676, c_38])).
% 3.98/1.74  tff(c_571, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_80])).
% 3.98/1.74  tff(c_573, plain, (![A_102, B_103]: (k3_xboole_0(A_102, B_103)=A_102 | ~r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.74  tff(c_577, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_571, c_573])).
% 3.98/1.74  tff(c_589, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.74  tff(c_598, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))=k5_xboole_0('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_577, c_589])).
% 3.98/1.74  tff(c_607, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_598])).
% 3.98/1.74  tff(c_2684, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2683, c_607])).
% 3.98/1.74  tff(c_2686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_2684])).
% 3.98/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.74  
% 3.98/1.74  Inference rules
% 3.98/1.74  ----------------------
% 3.98/1.74  #Ref     : 0
% 3.98/1.74  #Sup     : 605
% 3.98/1.74  #Fact    : 2
% 3.98/1.74  #Define  : 0
% 3.98/1.74  #Split   : 6
% 3.98/1.74  #Chain   : 0
% 3.98/1.74  #Close   : 0
% 3.98/1.74  
% 3.98/1.74  Ordering : KBO
% 3.98/1.74  
% 3.98/1.74  Simplification rules
% 3.98/1.74  ----------------------
% 3.98/1.74  #Subsume      : 64
% 3.98/1.74  #Demod        : 131
% 3.98/1.74  #Tautology    : 222
% 3.98/1.74  #SimpNegUnit  : 17
% 3.98/1.74  #BackRed      : 8
% 3.98/1.74  
% 3.98/1.74  #Partial instantiations: 0
% 3.98/1.74  #Strategies tried      : 1
% 3.98/1.74  
% 3.98/1.74  Timing (in seconds)
% 3.98/1.74  ----------------------
% 3.98/1.74  Preprocessing        : 0.32
% 3.98/1.74  Parsing              : 0.16
% 3.98/1.74  CNF conversion       : 0.02
% 3.98/1.74  Main loop            : 0.66
% 3.98/1.74  Inferencing          : 0.24
% 3.98/1.74  Reduction            : 0.19
% 3.98/1.74  Demodulation         : 0.13
% 3.98/1.74  BG Simplification    : 0.03
% 3.98/1.74  Subsumption          : 0.13
% 3.98/1.74  Abstraction          : 0.03
% 3.98/1.74  MUC search           : 0.00
% 3.98/1.74  Cooper               : 0.00
% 3.98/1.74  Total                : 1.00
% 3.98/1.74  Index Insertion      : 0.00
% 3.98/1.74  Index Deletion       : 0.00
% 3.98/1.74  Index Matching       : 0.00
% 3.98/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
