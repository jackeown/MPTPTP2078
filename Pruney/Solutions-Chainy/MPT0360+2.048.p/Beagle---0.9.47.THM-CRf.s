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
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 165 expanded)
%              Number of equality atoms :   21 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1671,plain,(
    ! [A_147,B_148,B_149] :
      ( r2_hidden('#skF_1'(A_147,B_148),B_149)
      | ~ r1_tarski(A_147,B_149)
      | r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_206,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_28,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_393,plain,(
    ! [A_78] :
      ( r1_xboole_0(A_78,'#skF_6')
      | ~ r1_tarski(A_78,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_28])).

tff(c_420,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_393])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_424,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_420,c_34])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_477,plain,(
    ! [D_81] :
      ( ~ r2_hidden(D_81,'#skF_6')
      | ~ r2_hidden(D_81,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_10])).

tff(c_482,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_2),'#skF_6')
      | r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_477])).

tff(c_1682,plain,(
    ! [B_148] :
      ( ~ r1_tarski('#skF_5','#skF_6')
      | r1_tarski('#skF_5',B_148) ) ),
    inference(resolution,[status(thm)],[c_1671,c_482])).

tff(c_1729,plain,(
    ! [B_150] : r1_tarski('#skF_5',B_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1682])).

tff(c_101,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [D_27,B_28,A_29] :
      ( ~ r2_hidden(D_27,B_28)
      | ~ r2_hidden(D_27,k4_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [D_27,A_17] :
      ( ~ r2_hidden(D_27,k1_xboole_0)
      | ~ r2_hidden(D_27,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_62])).

tff(c_287,plain,(
    ! [B_70,A_71] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_70),A_71)
      | r1_tarski(k1_xboole_0,B_70) ) ),
    inference(resolution,[status(thm)],[c_101,c_65])).

tff(c_322,plain,(
    ! [B_75] : r1_tarski(k1_xboole_0,B_75) ),
    inference(resolution,[status(thm)],[c_6,c_287])).

tff(c_340,plain,(
    ! [C_76] : r1_xboole_0(k1_xboole_0,C_76) ),
    inference(resolution,[status(thm)],[c_322,c_28])).

tff(c_345,plain,(
    ! [C_77] : k4_xboole_0(k1_xboole_0,C_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_340,c_34])).

tff(c_533,plain,(
    ! [A_85,C_86] :
      ( r1_xboole_0(A_85,C_86)
      | ~ r1_tarski(A_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_28])).

tff(c_537,plain,(
    ! [A_85,C_86] :
      ( k4_xboole_0(A_85,C_86) = A_85
      | ~ r1_tarski(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_533,c_34])).

tff(c_1808,plain,(
    ! [C_155] : k4_xboole_0('#skF_5',C_155) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1729,c_537])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1097,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r2_hidden('#skF_2'(A_117,B_118,C_119),B_118)
      | r2_hidden('#skF_3'(A_117,B_118,C_119),C_119)
      | k4_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1108,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_1097])).

tff(c_1220,plain,(
    ! [A_128,C_129] :
      ( r2_hidden('#skF_3'(A_128,A_128,C_129),C_129)
      | k4_xboole_0(A_128,A_128) = C_129 ) ),
    inference(resolution,[status(thm)],[c_24,c_1097])).

tff(c_1258,plain,(
    ! [A_130,A_131] :
      ( ~ r2_hidden('#skF_3'(A_130,A_130,k1_xboole_0),A_131)
      | k4_xboole_0(A_130,A_130) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1220,c_65])).

tff(c_1277,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1108,c_1258])).

tff(c_1813,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_1277])).

tff(c_1865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.61  
% 3.11/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.11/1.61  
% 3.11/1.61  %Foreground sorts:
% 3.11/1.61  
% 3.11/1.61  
% 3.11/1.61  %Background operators:
% 3.11/1.61  
% 3.11/1.61  
% 3.11/1.61  %Foreground operators:
% 3.11/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.11/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.11/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.11/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.61  
% 3.50/1.62  tff(f_69, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.50/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.50/1.62  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.50/1.62  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.50/1.62  tff(f_56, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.50/1.62  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.50/1.62  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.50/1.62  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.62  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.62  tff(c_136, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.62  tff(c_1671, plain, (![A_147, B_148, B_149]: (r2_hidden('#skF_1'(A_147, B_148), B_149) | ~r1_tarski(A_147, B_149) | r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_6, c_136])).
% 3.50/1.62  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.62  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.62  tff(c_206, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.50/1.62  tff(c_210, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_206])).
% 3.50/1.62  tff(c_28, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_tarski(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.62  tff(c_393, plain, (![A_78]: (r1_xboole_0(A_78, '#skF_6') | ~r1_tarski(A_78, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_210, c_28])).
% 3.50/1.62  tff(c_420, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_393])).
% 3.50/1.62  tff(c_34, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.50/1.62  tff(c_424, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_420, c_34])).
% 3.50/1.62  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_477, plain, (![D_81]: (~r2_hidden(D_81, '#skF_6') | ~r2_hidden(D_81, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_424, c_10])).
% 3.50/1.62  tff(c_482, plain, (![B_2]: (~r2_hidden('#skF_1'('#skF_5', B_2), '#skF_6') | r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_477])).
% 3.50/1.62  tff(c_1682, plain, (![B_148]: (~r1_tarski('#skF_5', '#skF_6') | r1_tarski('#skF_5', B_148))), inference(resolution, [status(thm)], [c_1671, c_482])).
% 3.50/1.62  tff(c_1729, plain, (![B_150]: (r1_tarski('#skF_5', B_150))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1682])).
% 3.50/1.62  tff(c_101, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.62  tff(c_32, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.50/1.62  tff(c_62, plain, (![D_27, B_28, A_29]: (~r2_hidden(D_27, B_28) | ~r2_hidden(D_27, k4_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_65, plain, (![D_27, A_17]: (~r2_hidden(D_27, k1_xboole_0) | ~r2_hidden(D_27, A_17))), inference(superposition, [status(thm), theory('equality')], [c_32, c_62])).
% 3.50/1.62  tff(c_287, plain, (![B_70, A_71]: (~r2_hidden('#skF_1'(k1_xboole_0, B_70), A_71) | r1_tarski(k1_xboole_0, B_70))), inference(resolution, [status(thm)], [c_101, c_65])).
% 3.50/1.62  tff(c_322, plain, (![B_75]: (r1_tarski(k1_xboole_0, B_75))), inference(resolution, [status(thm)], [c_6, c_287])).
% 3.50/1.62  tff(c_340, plain, (![C_76]: (r1_xboole_0(k1_xboole_0, C_76))), inference(resolution, [status(thm)], [c_322, c_28])).
% 3.50/1.62  tff(c_345, plain, (![C_77]: (k4_xboole_0(k1_xboole_0, C_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_340, c_34])).
% 3.50/1.62  tff(c_533, plain, (![A_85, C_86]: (r1_xboole_0(A_85, C_86) | ~r1_tarski(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_345, c_28])).
% 3.50/1.62  tff(c_537, plain, (![A_85, C_86]: (k4_xboole_0(A_85, C_86)=A_85 | ~r1_tarski(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_533, c_34])).
% 3.50/1.62  tff(c_1808, plain, (![C_155]: (k4_xboole_0('#skF_5', C_155)='#skF_5')), inference(resolution, [status(thm)], [c_1729, c_537])).
% 3.50/1.62  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_1097, plain, (![A_117, B_118, C_119]: (~r2_hidden('#skF_2'(A_117, B_118, C_119), B_118) | r2_hidden('#skF_3'(A_117, B_118, C_119), C_119) | k4_xboole_0(A_117, B_118)=C_119)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_1108, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_1097])).
% 3.50/1.62  tff(c_1220, plain, (![A_128, C_129]: (r2_hidden('#skF_3'(A_128, A_128, C_129), C_129) | k4_xboole_0(A_128, A_128)=C_129)), inference(resolution, [status(thm)], [c_24, c_1097])).
% 3.50/1.62  tff(c_1258, plain, (![A_130, A_131]: (~r2_hidden('#skF_3'(A_130, A_130, k1_xboole_0), A_131) | k4_xboole_0(A_130, A_130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1220, c_65])).
% 3.50/1.62  tff(c_1277, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1108, c_1258])).
% 3.50/1.62  tff(c_1813, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1808, c_1277])).
% 3.50/1.62  tff(c_1865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1813])).
% 3.50/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.62  
% 3.50/1.62  Inference rules
% 3.50/1.62  ----------------------
% 3.50/1.62  #Ref     : 0
% 3.50/1.62  #Sup     : 406
% 3.50/1.62  #Fact    : 0
% 3.50/1.62  #Define  : 0
% 3.50/1.62  #Split   : 0
% 3.50/1.62  #Chain   : 0
% 3.50/1.62  #Close   : 0
% 3.50/1.62  
% 3.50/1.62  Ordering : KBO
% 3.50/1.62  
% 3.50/1.62  Simplification rules
% 3.50/1.62  ----------------------
% 3.50/1.62  #Subsume      : 25
% 3.50/1.62  #Demod        : 262
% 3.50/1.62  #Tautology    : 240
% 3.50/1.62  #SimpNegUnit  : 3
% 3.50/1.62  #BackRed      : 6
% 3.50/1.62  
% 3.50/1.62  #Partial instantiations: 0
% 3.50/1.62  #Strategies tried      : 1
% 3.50/1.63  
% 3.50/1.63  Timing (in seconds)
% 3.50/1.63  ----------------------
% 3.50/1.63  Preprocessing        : 0.35
% 3.50/1.63  Parsing              : 0.18
% 3.50/1.63  CNF conversion       : 0.03
% 3.50/1.63  Main loop            : 0.47
% 3.50/1.63  Inferencing          : 0.17
% 3.50/1.63  Reduction            : 0.15
% 3.50/1.63  Demodulation         : 0.11
% 3.50/1.63  BG Simplification    : 0.02
% 3.50/1.63  Subsumption          : 0.08
% 3.50/1.63  Abstraction          : 0.02
% 3.50/1.63  MUC search           : 0.00
% 3.50/1.63  Cooper               : 0.00
% 3.50/1.63  Total                : 0.85
% 3.50/1.63  Index Insertion      : 0.00
% 3.50/1.63  Index Deletion       : 0.00
% 3.50/1.63  Index Matching       : 0.00
% 3.50/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
