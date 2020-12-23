%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :   73 (  90 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 112 expanded)
%              Number of equality atoms :   34 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_42,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_53,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_439,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(B_73,A_74)
      | ~ m1_subset_1(B_73,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_443,plain,(
    ! [B_73,A_16] :
      ( r1_tarski(B_73,A_16)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_439,c_20])).

tff(c_844,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_443])).

tff(c_865,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_844])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_869,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_865,c_8])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_876,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_14])).

tff(c_886,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_876])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_290,plain,(
    ! [B_66,A_67] : k3_tarski(k2_tarski(B_66,A_67)) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_275])).

tff(c_32,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,A_67) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_32])).

tff(c_648,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_657,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_648])).

tff(c_705,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_14])).

tff(c_714,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_705])).

tff(c_908,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_714])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_711,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_12])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( r2_hidden(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_566,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(B_81,A_82)
      | ~ r2_hidden(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_572,plain,(
    ! [C_20,A_16] :
      ( m1_subset_1(C_20,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_566])).

tff(c_579,plain,(
    ! [C_20,A_16] :
      ( m1_subset_1(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_572])).

tff(c_1321,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4144,plain,(
    ! [A_182,B_183,C_184] :
      ( k4_subset_1(A_182,B_183,C_184) = k2_xboole_0(B_183,C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(A_182))
      | ~ r1_tarski(C_184,A_182) ) ),
    inference(resolution,[status(thm)],[c_579,c_1321])).

tff(c_4297,plain,(
    ! [C_187] :
      ( k4_subset_1('#skF_4','#skF_5',C_187) = k2_xboole_0('#skF_5',C_187)
      | ~ r1_tarski(C_187,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_4144])).

tff(c_4367,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_711,c_4297])).

tff(c_4407,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_4367])).

tff(c_4409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_4407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.97  
% 4.96/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.97  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.96/1.97  
% 4.96/1.97  %Foreground sorts:
% 4.96/1.97  
% 4.96/1.97  
% 4.96/1.97  %Background operators:
% 4.96/1.97  
% 4.96/1.97  
% 4.96/1.97  %Foreground operators:
% 4.96/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.96/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.96/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.96/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.96/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.96/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.96/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.96/1.97  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.96/1.97  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.96/1.97  tff('#skF_5', type, '#skF_5': $i).
% 4.96/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.96/1.97  tff('#skF_4', type, '#skF_4': $i).
% 4.96/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.96/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.96/1.97  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.96/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.96/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.97  
% 4.96/1.99  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.96/1.99  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.96/1.99  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.96/1.99  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.96/1.99  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.96/1.99  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.96/1.99  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.96/1.99  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.96/1.99  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.96/1.99  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.96/1.99  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.96/1.99  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.96/1.99  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.96/1.99  tff(c_42, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.96/1.99  tff(c_50, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.96/1.99  tff(c_53, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 4.96/1.99  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.96/1.99  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.96/1.99  tff(c_46, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.96/1.99  tff(c_439, plain, (![B_73, A_74]: (r2_hidden(B_73, A_74) | ~m1_subset_1(B_73, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.96/1.99  tff(c_20, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.96/1.99  tff(c_443, plain, (![B_73, A_16]: (r1_tarski(B_73, A_16) | ~m1_subset_1(B_73, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_439, c_20])).
% 4.96/1.99  tff(c_844, plain, (![B_95, A_96]: (r1_tarski(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)))), inference(negUnitSimplification, [status(thm)], [c_46, c_443])).
% 4.96/1.99  tff(c_865, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_844])).
% 4.96/1.99  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.99  tff(c_869, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_865, c_8])).
% 4.96/1.99  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.96/1.99  tff(c_876, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_869, c_14])).
% 4.96/1.99  tff(c_886, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_876])).
% 4.96/1.99  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.96/1.99  tff(c_275, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.96/1.99  tff(c_290, plain, (![B_66, A_67]: (k3_tarski(k2_tarski(B_66, A_67))=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_16, c_275])).
% 4.96/1.99  tff(c_32, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.96/1.99  tff(c_296, plain, (![B_66, A_67]: (k2_xboole_0(B_66, A_67)=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_290, c_32])).
% 4.96/1.99  tff(c_648, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.96/1.99  tff(c_657, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_648])).
% 4.96/1.99  tff(c_705, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_657, c_14])).
% 4.96/1.99  tff(c_714, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_705])).
% 4.96/1.99  tff(c_908, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_886, c_714])).
% 4.96/1.99  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/1.99  tff(c_711, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_657, c_12])).
% 4.96/1.99  tff(c_22, plain, (![C_20, A_16]: (r2_hidden(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.96/1.99  tff(c_566, plain, (![B_81, A_82]: (m1_subset_1(B_81, A_82) | ~r2_hidden(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.96/1.99  tff(c_572, plain, (![C_20, A_16]: (m1_subset_1(C_20, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(resolution, [status(thm)], [c_22, c_566])).
% 4.96/1.99  tff(c_579, plain, (![C_20, A_16]: (m1_subset_1(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(negUnitSimplification, [status(thm)], [c_46, c_572])).
% 4.96/1.99  tff(c_1321, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.96/1.99  tff(c_4144, plain, (![A_182, B_183, C_184]: (k4_subset_1(A_182, B_183, C_184)=k2_xboole_0(B_183, C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(A_182)) | ~r1_tarski(C_184, A_182))), inference(resolution, [status(thm)], [c_579, c_1321])).
% 4.96/1.99  tff(c_4297, plain, (![C_187]: (k4_subset_1('#skF_4', '#skF_5', C_187)=k2_xboole_0('#skF_5', C_187) | ~r1_tarski(C_187, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_4144])).
% 4.96/1.99  tff(c_4367, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_711, c_4297])).
% 4.96/1.99  tff(c_4407, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_908, c_4367])).
% 4.96/1.99  tff(c_4409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_4407])).
% 4.96/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.99  
% 4.96/1.99  Inference rules
% 4.96/1.99  ----------------------
% 4.96/1.99  #Ref     : 0
% 4.96/1.99  #Sup     : 1017
% 4.96/1.99  #Fact    : 0
% 4.96/1.99  #Define  : 0
% 4.96/1.99  #Split   : 2
% 4.96/1.99  #Chain   : 0
% 4.96/1.99  #Close   : 0
% 4.96/1.99  
% 4.96/1.99  Ordering : KBO
% 4.96/1.99  
% 4.96/1.99  Simplification rules
% 4.96/1.99  ----------------------
% 4.96/1.99  #Subsume      : 34
% 4.96/1.99  #Demod        : 1533
% 4.96/1.99  #Tautology    : 716
% 4.96/1.99  #SimpNegUnit  : 22
% 4.96/1.99  #BackRed      : 0
% 4.96/1.99  
% 4.96/1.99  #Partial instantiations: 0
% 4.96/1.99  #Strategies tried      : 1
% 4.96/1.99  
% 4.96/1.99  Timing (in seconds)
% 4.96/1.99  ----------------------
% 4.96/1.99  Preprocessing        : 0.33
% 4.96/1.99  Parsing              : 0.18
% 4.96/1.99  CNF conversion       : 0.02
% 4.96/1.99  Main loop            : 0.85
% 4.96/1.99  Inferencing          : 0.28
% 4.96/1.99  Reduction            : 0.37
% 4.96/1.99  Demodulation         : 0.29
% 4.96/1.99  BG Simplification    : 0.03
% 4.96/1.99  Subsumption          : 0.12
% 4.96/1.99  Abstraction          : 0.04
% 4.96/1.99  MUC search           : 0.00
% 4.96/1.99  Cooper               : 0.00
% 4.96/1.99  Total                : 1.22
% 4.96/1.99  Index Insertion      : 0.00
% 4.96/1.99  Index Deletion       : 0.00
% 4.96/1.99  Index Matching       : 0.00
% 4.96/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
