%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 9.97s
% Output     : CNFRefutation 9.97s
% Verified   : 
% Statistics : Number of formulae       :   68 (  97 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 178 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [B_48,A_49] : k3_tarski(k2_tarski(B_48,A_49)) = k2_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_42,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_42])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_645,plain,(
    ! [A_123,B_124,C_125] :
      ( k4_subset_1(A_123,B_124,C_125) = k2_xboole_0(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1360,plain,(
    ! [A_175,B_176] :
      ( k4_subset_1(A_175,B_176,A_175) = k2_xboole_0(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(resolution,[status(thm)],[c_64,c_645])).

tff(c_1372,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_1360])).

tff(c_1380,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1372])).

tff(c_60,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_60])).

tff(c_1388,plain,(
    k2_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_63])).

tff(c_56,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_243,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,A_62)
      | ~ m1_subset_1(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_250,plain,(
    ! [B_61,A_16] :
      ( r1_tarski(B_61,A_16)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_243,c_30])).

tff(c_255,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(B_63,A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_250])).

tff(c_272,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_255])).

tff(c_1436,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden('#skF_2'(A_180,B_181,C_182),B_181)
      | r2_hidden('#skF_2'(A_180,B_181,C_182),A_180)
      | r2_hidden('#skF_3'(A_180,B_181,C_182),C_182)
      | k2_xboole_0(A_180,B_181) = C_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4615,plain,(
    ! [A_361,B_362] :
      ( r2_hidden('#skF_2'(A_361,B_362,A_361),B_362)
      | r2_hidden('#skF_3'(A_361,B_362,A_361),A_361)
      | k2_xboole_0(A_361,B_362) = A_361 ) ),
    inference(resolution,[status(thm)],[c_1436,c_22])).

tff(c_1844,plain,(
    ! [A_203,B_204,C_205] :
      ( r2_hidden('#skF_2'(A_203,B_204,C_205),B_204)
      | r2_hidden('#skF_2'(A_203,B_204,C_205),A_203)
      | ~ r2_hidden('#skF_3'(A_203,B_204,C_205),A_203)
      | k2_xboole_0(A_203,B_204) = C_205 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1908,plain,(
    ! [A_203,B_204] :
      ( r2_hidden('#skF_2'(A_203,B_204,A_203),B_204)
      | ~ r2_hidden('#skF_3'(A_203,B_204,A_203),A_203)
      | k2_xboole_0(A_203,B_204) = A_203 ) ),
    inference(resolution,[status(thm)],[c_1844,c_18])).

tff(c_4679,plain,(
    ! [A_363,B_364] :
      ( r2_hidden('#skF_2'(A_363,B_364,A_363),B_364)
      | k2_xboole_0(A_363,B_364) = A_363 ) ),
    inference(resolution,[status(thm)],[c_4615,c_1908])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12115,plain,(
    ! [A_769,B_770,B_771] :
      ( r2_hidden('#skF_2'(A_769,B_770,A_769),B_771)
      | ~ r1_tarski(B_770,B_771)
      | k2_xboole_0(A_769,B_770) = A_769 ) ),
    inference(resolution,[status(thm)],[c_4679,c_2])).

tff(c_12152,plain,(
    ! [B_771,B_770] :
      ( r2_hidden('#skF_3'(B_771,B_770,B_771),B_771)
      | ~ r1_tarski(B_770,B_771)
      | k2_xboole_0(B_771,B_770) = B_771 ) ),
    inference(resolution,[status(thm)],[c_12115,c_22])).

tff(c_12631,plain,(
    ! [B_783,B_784] :
      ( ~ r2_hidden('#skF_3'(B_783,B_784,B_783),B_783)
      | ~ r1_tarski(B_784,B_783)
      | k2_xboole_0(B_783,B_784) = B_783 ) ),
    inference(resolution,[status(thm)],[c_12115,c_18])).

tff(c_12808,plain,(
    ! [B_790,B_791] :
      ( ~ r1_tarski(B_790,B_791)
      | k2_xboole_0(B_791,B_790) = B_791 ) ),
    inference(resolution,[status(thm)],[c_12152,c_12631])).

tff(c_12865,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_272,c_12808])).

tff(c_12890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1388,c_12865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:21:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.97/3.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.97/3.54  
% 9.97/3.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.97/3.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 9.97/3.55  
% 9.97/3.55  %Foreground sorts:
% 9.97/3.55  
% 9.97/3.55  
% 9.97/3.55  %Background operators:
% 9.97/3.55  
% 9.97/3.55  
% 9.97/3.55  %Foreground operators:
% 9.97/3.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.97/3.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.97/3.55  tff('#skF_7', type, '#skF_7': $i).
% 9.97/3.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.97/3.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.97/3.55  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.97/3.55  tff('#skF_6', type, '#skF_6': $i).
% 9.97/3.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.97/3.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.97/3.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.97/3.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.97/3.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.97/3.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.97/3.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.97/3.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.97/3.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.97/3.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.97/3.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.97/3.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.97/3.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.97/3.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.97/3.55  
% 9.97/3.56  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.97/3.56  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.97/3.56  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 9.97/3.56  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.97/3.56  tff(f_71, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.97/3.56  tff(f_80, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.97/3.56  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.97/3.56  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.97/3.56  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.97/3.56  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 9.97/3.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.97/3.56  tff(c_26, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.97/3.56  tff(c_118, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.97/3.56  tff(c_153, plain, (![B_48, A_49]: (k3_tarski(k2_tarski(B_48, A_49))=k2_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_26, c_118])).
% 9.97/3.56  tff(c_42, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.97/3.56  tff(c_159, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_153, c_42])).
% 9.97/3.56  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.97/3.56  tff(c_52, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.97/3.56  tff(c_54, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.97/3.56  tff(c_64, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 9.97/3.56  tff(c_645, plain, (![A_123, B_124, C_125]: (k4_subset_1(A_123, B_124, C_125)=k2_xboole_0(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.97/3.56  tff(c_1360, plain, (![A_175, B_176]: (k4_subset_1(A_175, B_176, A_175)=k2_xboole_0(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(resolution, [status(thm)], [c_64, c_645])).
% 9.97/3.56  tff(c_1372, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_1360])).
% 9.97/3.56  tff(c_1380, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_1372])).
% 9.97/3.56  tff(c_60, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.97/3.56  tff(c_63, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_60])).
% 9.97/3.56  tff(c_1388, plain, (k2_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_63])).
% 9.97/3.56  tff(c_56, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.97/3.56  tff(c_243, plain, (![B_61, A_62]: (r2_hidden(B_61, A_62) | ~m1_subset_1(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.97/3.56  tff(c_30, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.97/3.56  tff(c_250, plain, (![B_61, A_16]: (r1_tarski(B_61, A_16) | ~m1_subset_1(B_61, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_243, c_30])).
% 9.97/3.56  tff(c_255, plain, (![B_63, A_64]: (r1_tarski(B_63, A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(negUnitSimplification, [status(thm)], [c_56, c_250])).
% 9.97/3.56  tff(c_272, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_255])).
% 9.97/3.56  tff(c_1436, plain, (![A_180, B_181, C_182]: (r2_hidden('#skF_2'(A_180, B_181, C_182), B_181) | r2_hidden('#skF_2'(A_180, B_181, C_182), A_180) | r2_hidden('#skF_3'(A_180, B_181, C_182), C_182) | k2_xboole_0(A_180, B_181)=C_182)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.97/3.56  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.97/3.56  tff(c_4615, plain, (![A_361, B_362]: (r2_hidden('#skF_2'(A_361, B_362, A_361), B_362) | r2_hidden('#skF_3'(A_361, B_362, A_361), A_361) | k2_xboole_0(A_361, B_362)=A_361)), inference(resolution, [status(thm)], [c_1436, c_22])).
% 9.97/3.56  tff(c_1844, plain, (![A_203, B_204, C_205]: (r2_hidden('#skF_2'(A_203, B_204, C_205), B_204) | r2_hidden('#skF_2'(A_203, B_204, C_205), A_203) | ~r2_hidden('#skF_3'(A_203, B_204, C_205), A_203) | k2_xboole_0(A_203, B_204)=C_205)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.97/3.56  tff(c_18, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.97/3.56  tff(c_1908, plain, (![A_203, B_204]: (r2_hidden('#skF_2'(A_203, B_204, A_203), B_204) | ~r2_hidden('#skF_3'(A_203, B_204, A_203), A_203) | k2_xboole_0(A_203, B_204)=A_203)), inference(resolution, [status(thm)], [c_1844, c_18])).
% 9.97/3.56  tff(c_4679, plain, (![A_363, B_364]: (r2_hidden('#skF_2'(A_363, B_364, A_363), B_364) | k2_xboole_0(A_363, B_364)=A_363)), inference(resolution, [status(thm)], [c_4615, c_1908])).
% 9.97/3.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.97/3.56  tff(c_12115, plain, (![A_769, B_770, B_771]: (r2_hidden('#skF_2'(A_769, B_770, A_769), B_771) | ~r1_tarski(B_770, B_771) | k2_xboole_0(A_769, B_770)=A_769)), inference(resolution, [status(thm)], [c_4679, c_2])).
% 9.97/3.56  tff(c_12152, plain, (![B_771, B_770]: (r2_hidden('#skF_3'(B_771, B_770, B_771), B_771) | ~r1_tarski(B_770, B_771) | k2_xboole_0(B_771, B_770)=B_771)), inference(resolution, [status(thm)], [c_12115, c_22])).
% 9.97/3.56  tff(c_12631, plain, (![B_783, B_784]: (~r2_hidden('#skF_3'(B_783, B_784, B_783), B_783) | ~r1_tarski(B_784, B_783) | k2_xboole_0(B_783, B_784)=B_783)), inference(resolution, [status(thm)], [c_12115, c_18])).
% 9.97/3.56  tff(c_12808, plain, (![B_790, B_791]: (~r1_tarski(B_790, B_791) | k2_xboole_0(B_791, B_790)=B_791)), inference(resolution, [status(thm)], [c_12152, c_12631])).
% 9.97/3.56  tff(c_12865, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_272, c_12808])).
% 9.97/3.56  tff(c_12890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1388, c_12865])).
% 9.97/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.97/3.56  
% 9.97/3.56  Inference rules
% 9.97/3.56  ----------------------
% 9.97/3.56  #Ref     : 0
% 9.97/3.56  #Sup     : 2993
% 9.97/3.56  #Fact    : 10
% 9.97/3.56  #Define  : 0
% 9.97/3.56  #Split   : 3
% 9.97/3.56  #Chain   : 0
% 9.97/3.56  #Close   : 0
% 9.97/3.56  
% 9.97/3.56  Ordering : KBO
% 9.97/3.56  
% 9.97/3.56  Simplification rules
% 9.97/3.56  ----------------------
% 9.97/3.56  #Subsume      : 633
% 9.97/3.56  #Demod        : 849
% 9.97/3.56  #Tautology    : 794
% 9.97/3.56  #SimpNegUnit  : 59
% 9.97/3.56  #BackRed      : 4
% 9.97/3.56  
% 9.97/3.56  #Partial instantiations: 0
% 9.97/3.56  #Strategies tried      : 1
% 9.97/3.56  
% 9.97/3.56  Timing (in seconds)
% 9.97/3.56  ----------------------
% 9.97/3.56  Preprocessing        : 0.33
% 9.97/3.56  Parsing              : 0.17
% 9.97/3.56  CNF conversion       : 0.02
% 9.97/3.56  Main loop            : 2.45
% 9.97/3.56  Inferencing          : 0.61
% 9.97/3.56  Reduction            : 0.86
% 9.97/3.56  Demodulation         : 0.69
% 9.97/3.56  BG Simplification    : 0.07
% 9.97/3.56  Subsumption          : 0.74
% 9.97/3.56  Abstraction          : 0.10
% 9.97/3.56  MUC search           : 0.00
% 9.97/3.56  Cooper               : 0.00
% 9.97/3.56  Total                : 2.80
% 9.97/3.56  Index Insertion      : 0.00
% 9.97/3.56  Index Deletion       : 0.00
% 9.97/3.56  Index Matching       : 0.00
% 9.97/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
