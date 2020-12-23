%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   59 (  84 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 123 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_193,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [A_22] : k1_subset_1(A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,
    ( k1_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_55,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_100,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_54,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_113,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_56])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_114,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_105])).

tff(c_153,plain,(
    ! [D_40,A_41,B_42] :
      ( r2_hidden(D_40,A_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_160,plain,(
    ! [D_40,B_17] :
      ( r2_hidden(D_40,B_17)
      | ~ r2_hidden(D_40,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_153])).

tff(c_273,plain,(
    ! [B_64,B_65] :
      ( r2_hidden('#skF_1'('#skF_6',B_64),B_65)
      | r1_tarski('#skF_6',B_64) ) ),
    inference(resolution,[status(thm)],[c_193,c_160])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_294,plain,(
    ! [B_65] : r1_tarski('#skF_6',B_65) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_100])).

tff(c_308,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_309,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_505,plain,(
    ! [C_98,B_99,A_100] :
      ( r2_hidden(C_98,B_99)
      | ~ r2_hidden(C_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_662,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_4'(A_113),B_114)
      | ~ r1_tarski(A_113,B_114)
      | k1_xboole_0 = A_113 ) ),
    inference(resolution,[status(thm)],[c_28,c_505])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_606,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_610,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_606])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_617,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_6')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_12])).

tff(c_1108,plain,(
    ! [A_145] :
      ( ~ r2_hidden('#skF_4'(A_145),'#skF_6')
      | ~ r1_tarski(A_145,k3_subset_1('#skF_5','#skF_6'))
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_662,c_617])).

tff(c_1124,plain,
    ( ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_1108])).

tff(c_1133,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_1124])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_1133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.56  
% 3.04/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.56  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.56  
% 3.04/1.56  %Foreground sorts:
% 3.04/1.56  
% 3.04/1.56  
% 3.04/1.56  %Background operators:
% 3.04/1.56  
% 3.04/1.56  
% 3.04/1.56  %Foreground operators:
% 3.04/1.56  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.04/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.04/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.56  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.04/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.56  
% 3.04/1.57  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.57  tff(f_66, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.04/1.57  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.04/1.57  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.57  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.04/1.57  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.04/1.57  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.04/1.57  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.04/1.57  tff(c_193, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.57  tff(c_42, plain, (![A_22]: (k1_subset_1(A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.04/1.57  tff(c_48, plain, (k1_subset_1('#skF_5')!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.57  tff(c_55, plain, (k1_xboole_0!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_48])).
% 3.04/1.57  tff(c_100, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_55])).
% 3.04/1.57  tff(c_54, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.57  tff(c_56, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 3.04/1.57  tff(c_113, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_100, c_56])).
% 3.04/1.57  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.57  tff(c_101, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.57  tff(c_105, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_101])).
% 3.04/1.57  tff(c_114, plain, (![B_17]: (k4_xboole_0(B_17, B_17)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_105])).
% 3.04/1.57  tff(c_153, plain, (![D_40, A_41, B_42]: (r2_hidden(D_40, A_41) | ~r2_hidden(D_40, k4_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.57  tff(c_160, plain, (![D_40, B_17]: (r2_hidden(D_40, B_17) | ~r2_hidden(D_40, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_153])).
% 3.04/1.57  tff(c_273, plain, (![B_64, B_65]: (r2_hidden('#skF_1'('#skF_6', B_64), B_65) | r1_tarski('#skF_6', B_64))), inference(resolution, [status(thm)], [c_193, c_160])).
% 3.04/1.57  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.57  tff(c_294, plain, (![B_65]: (r1_tarski('#skF_6', B_65))), inference(resolution, [status(thm)], [c_273, c_6])).
% 3.04/1.57  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_294, c_100])).
% 3.04/1.57  tff(c_308, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_55])).
% 3.04/1.57  tff(c_309, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_55])).
% 3.04/1.57  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.57  tff(c_505, plain, (![C_98, B_99, A_100]: (r2_hidden(C_98, B_99) | ~r2_hidden(C_98, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.57  tff(c_662, plain, (![A_113, B_114]: (r2_hidden('#skF_4'(A_113), B_114) | ~r1_tarski(A_113, B_114) | k1_xboole_0=A_113)), inference(resolution, [status(thm)], [c_28, c_505])).
% 3.04/1.57  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.57  tff(c_606, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.04/1.57  tff(c_610, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_606])).
% 3.04/1.57  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.57  tff(c_617, plain, (![D_13]: (~r2_hidden(D_13, '#skF_6') | ~r2_hidden(D_13, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_610, c_12])).
% 3.04/1.57  tff(c_1108, plain, (![A_145]: (~r2_hidden('#skF_4'(A_145), '#skF_6') | ~r1_tarski(A_145, k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_662, c_617])).
% 3.04/1.57  tff(c_1124, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28, c_1108])).
% 3.04/1.57  tff(c_1133, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_1124])).
% 3.04/1.57  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_1133])).
% 3.04/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.57  
% 3.04/1.57  Inference rules
% 3.04/1.57  ----------------------
% 3.04/1.57  #Ref     : 0
% 3.04/1.57  #Sup     : 232
% 3.04/1.57  #Fact    : 0
% 3.04/1.57  #Define  : 0
% 3.04/1.57  #Split   : 3
% 3.04/1.57  #Chain   : 0
% 3.04/1.57  #Close   : 0
% 3.04/1.57  
% 3.04/1.57  Ordering : KBO
% 3.04/1.57  
% 3.04/1.57  Simplification rules
% 3.04/1.57  ----------------------
% 3.04/1.57  #Subsume      : 42
% 3.04/1.57  #Demod        : 80
% 3.04/1.57  #Tautology    : 101
% 3.04/1.57  #SimpNegUnit  : 13
% 3.04/1.57  #BackRed      : 12
% 3.04/1.57  
% 3.04/1.57  #Partial instantiations: 0
% 3.04/1.57  #Strategies tried      : 1
% 3.04/1.57  
% 3.04/1.57  Timing (in seconds)
% 3.04/1.57  ----------------------
% 3.04/1.57  Preprocessing        : 0.38
% 3.04/1.57  Parsing              : 0.18
% 3.04/1.57  CNF conversion       : 0.03
% 3.04/1.57  Main loop            : 0.37
% 3.04/1.57  Inferencing          : 0.13
% 3.04/1.57  Reduction            : 0.12
% 3.04/1.57  Demodulation         : 0.08
% 3.04/1.57  BG Simplification    : 0.02
% 3.04/1.57  Subsumption          : 0.08
% 3.04/1.57  Abstraction          : 0.02
% 3.04/1.57  MUC search           : 0.00
% 3.04/1.57  Cooper               : 0.00
% 3.04/1.57  Total                : 0.79
% 3.04/1.57  Index Insertion      : 0.00
% 3.04/1.57  Index Deletion       : 0.00
% 3.04/1.58  Index Matching       : 0.00
% 3.04/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
