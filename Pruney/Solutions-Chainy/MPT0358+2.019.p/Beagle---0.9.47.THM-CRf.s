%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 131 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 185 expanded)
%              Number of equality atoms :   27 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_68,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_234,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_33] : k1_subset_1(A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,
    ( k1_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_133,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_63])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = '#skF_6'
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_10])).

tff(c_157,plain,(
    ! [A_24,B_25] : k3_xboole_0(k4_xboole_0(A_24,B_25),B_25) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_149])).

tff(c_190,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_196,plain,(
    ! [A_24,B_25,C_65] :
      ( ~ r1_xboole_0(k4_xboole_0(A_24,B_25),B_25)
      | ~ r2_hidden(C_65,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_190])).

tff(c_207,plain,(
    ! [C_65] : ~ r2_hidden(C_65,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_196])).

tff(c_255,plain,(
    ! [B_78] : r1_tarski('#skF_6',B_78) ),
    inference(resolution,[status(thm)],[c_234,c_207])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_127])).

tff(c_261,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_262,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_304,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_308,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_262,c_304])).

tff(c_320,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_323,plain,(
    ! [C_93] :
      ( ~ r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6'))
      | ~ r2_hidden(C_93,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_320])).

tff(c_360,plain,(
    ~ r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1155,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(A_154,B_155) = k3_subset_1(A_154,B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1164,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1155])).

tff(c_266,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_274,plain,(
    ! [A_24,B_25] : k3_xboole_0(k4_xboole_0(A_24,B_25),B_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_266])).

tff(c_329,plain,(
    ! [A_24,B_25,C_93] :
      ( ~ r1_xboole_0(k4_xboole_0(A_24,B_25),B_25)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_320])).

tff(c_340,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_329])).

tff(c_275,plain,(
    ! [A_83,B_84] : k3_xboole_0(k4_xboole_0(A_83,B_84),B_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_266])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [B_84,A_83] : k3_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_2])).

tff(c_955,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_2'(A_142,B_143),k3_xboole_0(A_142,B_143))
      | r1_xboole_0(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_978,plain,(
    ! [B_84,A_83] :
      ( r2_hidden('#skF_2'(B_84,k4_xboole_0(A_83,B_84)),k1_xboole_0)
      | r1_xboole_0(B_84,k4_xboole_0(A_83,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_955])).

tff(c_996,plain,(
    ! [B_84,A_83] : r1_xboole_0(B_84,k4_xboole_0(A_83,B_84)) ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_978])).

tff(c_1168,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_996])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_1168])).

tff(c_1183,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_1187,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1183,c_10])).

tff(c_1189,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_1187])).

tff(c_1191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_1189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.05/1.50  
% 3.05/1.50  %Foreground sorts:
% 3.05/1.50  
% 3.05/1.50  
% 3.05/1.50  %Background operators:
% 3.05/1.50  
% 3.05/1.50  
% 3.05/1.50  %Foreground operators:
% 3.05/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.05/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.05/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.05/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.05/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.50  
% 3.05/1.52  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.05/1.52  tff(f_68, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.05/1.52  tff(f_90, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.05/1.52  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.05/1.52  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.05/1.52  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.05/1.52  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.05/1.52  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.05/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.05/1.52  tff(c_234, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), A_77) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.05/1.52  tff(c_26, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.05/1.52  tff(c_48, plain, (![A_33]: (k1_subset_1(A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.05/1.52  tff(c_56, plain, (k1_subset_1('#skF_5')!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.05/1.52  tff(c_64, plain, (k1_xboole_0!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 3.05/1.52  tff(c_127, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.05/1.52  tff(c_62, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.05/1.52  tff(c_63, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 3.05/1.52  tff(c_133, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_127, c_63])).
% 3.05/1.52  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.52  tff(c_149, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)='#skF_6' | ~r1_xboole_0(A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_10])).
% 3.05/1.52  tff(c_157, plain, (![A_24, B_25]: (k3_xboole_0(k4_xboole_0(A_24, B_25), B_25)='#skF_6')), inference(resolution, [status(thm)], [c_26, c_149])).
% 3.05/1.52  tff(c_190, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.52  tff(c_196, plain, (![A_24, B_25, C_65]: (~r1_xboole_0(k4_xboole_0(A_24, B_25), B_25) | ~r2_hidden(C_65, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_190])).
% 3.05/1.52  tff(c_207, plain, (![C_65]: (~r2_hidden(C_65, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_196])).
% 3.05/1.52  tff(c_255, plain, (![B_78]: (r1_tarski('#skF_6', B_78))), inference(resolution, [status(thm)], [c_234, c_207])).
% 3.05/1.52  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_127])).
% 3.05/1.52  tff(c_261, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 3.05/1.52  tff(c_262, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_64])).
% 3.05/1.52  tff(c_304, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.52  tff(c_308, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_262, c_304])).
% 3.05/1.52  tff(c_320, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.52  tff(c_323, plain, (![C_93]: (~r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | ~r2_hidden(C_93, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_320])).
% 3.05/1.52  tff(c_360, plain, (~r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_323])).
% 3.05/1.52  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.05/1.52  tff(c_1155, plain, (![A_154, B_155]: (k4_xboole_0(A_154, B_155)=k3_subset_1(A_154, B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.05/1.52  tff(c_1164, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_1155])).
% 3.05/1.52  tff(c_266, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.52  tff(c_274, plain, (![A_24, B_25]: (k3_xboole_0(k4_xboole_0(A_24, B_25), B_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_266])).
% 3.05/1.52  tff(c_329, plain, (![A_24, B_25, C_93]: (~r1_xboole_0(k4_xboole_0(A_24, B_25), B_25) | ~r2_hidden(C_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_274, c_320])).
% 3.05/1.52  tff(c_340, plain, (![C_93]: (~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_329])).
% 3.05/1.52  tff(c_275, plain, (![A_83, B_84]: (k3_xboole_0(k4_xboole_0(A_83, B_84), B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_266])).
% 3.05/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.52  tff(c_280, plain, (![B_84, A_83]: (k3_xboole_0(B_84, k4_xboole_0(A_83, B_84))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_275, c_2])).
% 3.05/1.52  tff(c_955, plain, (![A_142, B_143]: (r2_hidden('#skF_2'(A_142, B_143), k3_xboole_0(A_142, B_143)) | r1_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.52  tff(c_978, plain, (![B_84, A_83]: (r2_hidden('#skF_2'(B_84, k4_xboole_0(A_83, B_84)), k1_xboole_0) | r1_xboole_0(B_84, k4_xboole_0(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_955])).
% 3.05/1.52  tff(c_996, plain, (![B_84, A_83]: (r1_xboole_0(B_84, k4_xboole_0(A_83, B_84)))), inference(negUnitSimplification, [status(thm)], [c_340, c_978])).
% 3.05/1.52  tff(c_1168, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_996])).
% 3.05/1.52  tff(c_1181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_1168])).
% 3.05/1.52  tff(c_1183, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_323])).
% 3.05/1.52  tff(c_1187, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1183, c_10])).
% 3.05/1.52  tff(c_1189, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_1187])).
% 3.05/1.52  tff(c_1191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_1189])).
% 3.05/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.52  
% 3.05/1.52  Inference rules
% 3.05/1.52  ----------------------
% 3.05/1.52  #Ref     : 1
% 3.05/1.52  #Sup     : 291
% 3.05/1.52  #Fact    : 0
% 3.05/1.52  #Define  : 0
% 3.05/1.52  #Split   : 5
% 3.05/1.52  #Chain   : 0
% 3.05/1.52  #Close   : 0
% 3.05/1.52  
% 3.05/1.52  Ordering : KBO
% 3.05/1.52  
% 3.05/1.52  Simplification rules
% 3.05/1.52  ----------------------
% 3.05/1.52  #Subsume      : 47
% 3.05/1.52  #Demod        : 85
% 3.05/1.52  #Tautology    : 138
% 3.05/1.52  #SimpNegUnit  : 10
% 3.05/1.52  #BackRed      : 3
% 3.05/1.52  
% 3.05/1.52  #Partial instantiations: 0
% 3.05/1.52  #Strategies tried      : 1
% 3.05/1.52  
% 3.05/1.52  Timing (in seconds)
% 3.05/1.52  ----------------------
% 3.05/1.52  Preprocessing        : 0.34
% 3.05/1.52  Parsing              : 0.16
% 3.05/1.52  CNF conversion       : 0.02
% 3.05/1.52  Main loop            : 0.42
% 3.05/1.52  Inferencing          : 0.14
% 3.05/1.52  Reduction            : 0.15
% 3.05/1.52  Demodulation         : 0.11
% 3.05/1.52  BG Simplification    : 0.02
% 3.05/1.52  Subsumption          : 0.07
% 3.05/1.52  Abstraction          : 0.03
% 3.05/1.52  MUC search           : 0.00
% 3.05/1.52  Cooper               : 0.00
% 3.05/1.52  Total                : 0.80
% 3.05/1.52  Index Insertion      : 0.00
% 3.05/1.52  Index Deletion       : 0.00
% 3.05/1.52  Index Matching       : 0.00
% 3.05/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
