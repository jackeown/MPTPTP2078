%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 168 expanded)
%              Number of equality atoms :   36 (  79 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_50,plain,(
    ! [A_24] : r1_tarski(k1_xboole_0,A_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ! [A_25] : k1_subset_1(A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_subset_1(A_31)) = k2_subset_1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_subset_1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60])).

tff(c_76,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_xboole_0) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_75])).

tff(c_62,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_532,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(A_81,k3_subset_1(A_81,B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_536,plain,(
    ! [A_32] : k3_subset_1(A_32,k3_subset_1(A_32,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_532])).

tff(c_539,plain,(
    ! [A_32] : k3_subset_1(A_32,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_536])).

tff(c_66,plain,
    ( k2_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_74,plain,
    ( '#skF_7' != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_137,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_72,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | k2_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72])).

tff(c_138,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_73])).

tff(c_139,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_138,c_137])).

tff(c_541,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_139])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_541])).

tff(c_545,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_546,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_868,plain,(
    ! [C_114,B_115,A_116] :
      ( r2_hidden(C_114,B_115)
      | ~ r2_hidden(C_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1465,plain,(
    ! [A_159,B_160,B_161] :
      ( r2_hidden('#skF_1'(A_159,B_160),B_161)
      | ~ r1_tarski(A_159,B_161)
      | r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_8,c_868])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_969,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k3_subset_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_978,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_969])).

tff(c_30,plain,(
    ! [D_19,B_15,A_14] :
      ( ~ r2_hidden(D_19,B_15)
      | ~ r2_hidden(D_19,k4_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1153,plain,(
    ! [D_141] :
      ( ~ r2_hidden(D_141,'#skF_7')
      | ~ r2_hidden(D_141,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_30])).

tff(c_1158,plain,(
    ! [B_4] :
      ( ~ r2_hidden('#skF_1'(k3_subset_1('#skF_6','#skF_7'),B_4),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_1153])).

tff(c_1469,plain,(
    ! [B_160] :
      ( ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_160) ) ),
    inference(resolution,[status(thm)],[c_1465,c_1158])).

tff(c_1547,plain,(
    ! [B_162] : r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_1469])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1718,plain,(
    ! [B_172] : k3_xboole_0(k3_subset_1('#skF_6','#skF_7'),B_172) = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1547,c_48])).

tff(c_549,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_558,plain,(
    ! [A_85] : k3_xboole_0(k1_xboole_0,A_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_549])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_563,plain,(
    ! [A_85] : k3_xboole_0(A_85,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_2])).

tff(c_1742,plain,(
    k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_563])).

tff(c_931,plain,(
    ! [A_122,B_123] :
      ( k3_subset_1(A_122,k3_subset_1(A_122,B_123)) = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_938,plain,(
    k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_64,c_931])).

tff(c_1782,plain,(
    k3_subset_1('#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_938])).

tff(c_1790,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1782])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_1790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.69  
% 3.95/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.70  
% 3.95/1.70  %Foreground sorts:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Background operators:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Foreground operators:
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.95/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.95/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.70  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.95/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.95/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.95/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.70  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.95/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.95/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.95/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.70  
% 3.95/1.71  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.95/1.71  tff(f_63, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.95/1.71  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.95/1.71  tff(f_75, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.95/1.71  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.95/1.71  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.95/1.71  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.95/1.71  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.95/1.71  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.95/1.71  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.95/1.71  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.95/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.95/1.71  tff(c_50, plain, (![A_24]: (r1_tarski(k1_xboole_0, A_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.95/1.71  tff(c_52, plain, (![A_25]: (k1_subset_1(A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.71  tff(c_54, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.71  tff(c_60, plain, (![A_31]: (k3_subset_1(A_31, k1_subset_1(A_31))=k2_subset_1(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.71  tff(c_75, plain, (![A_31]: (k3_subset_1(A_31, k1_subset_1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60])).
% 3.95/1.71  tff(c_76, plain, (![A_31]: (k3_subset_1(A_31, k1_xboole_0)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_75])).
% 3.95/1.71  tff(c_62, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.71  tff(c_532, plain, (![A_81, B_82]: (k3_subset_1(A_81, k3_subset_1(A_81, B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.95/1.71  tff(c_536, plain, (![A_32]: (k3_subset_1(A_32, k3_subset_1(A_32, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_532])).
% 3.95/1.71  tff(c_539, plain, (![A_32]: (k3_subset_1(A_32, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_536])).
% 3.95/1.71  tff(c_66, plain, (k2_subset_1('#skF_6')!='#skF_7' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.95/1.71  tff(c_74, plain, ('#skF_7'!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66])).
% 3.95/1.71  tff(c_137, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 3.95/1.71  tff(c_72, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | k2_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.95/1.71  tff(c_73, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72])).
% 3.95/1.71  tff(c_138, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_137, c_73])).
% 3.95/1.71  tff(c_139, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_138, c_137])).
% 3.95/1.71  tff(c_541, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_139])).
% 3.95/1.71  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_541])).
% 3.95/1.71  tff(c_545, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 3.95/1.71  tff(c_546, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 3.95/1.71  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.95/1.71  tff(c_868, plain, (![C_114, B_115, A_116]: (r2_hidden(C_114, B_115) | ~r2_hidden(C_114, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.95/1.71  tff(c_1465, plain, (![A_159, B_160, B_161]: (r2_hidden('#skF_1'(A_159, B_160), B_161) | ~r1_tarski(A_159, B_161) | r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_8, c_868])).
% 3.95/1.71  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.95/1.71  tff(c_969, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k3_subset_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.95/1.71  tff(c_978, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_969])).
% 3.95/1.71  tff(c_30, plain, (![D_19, B_15, A_14]: (~r2_hidden(D_19, B_15) | ~r2_hidden(D_19, k4_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.71  tff(c_1153, plain, (![D_141]: (~r2_hidden(D_141, '#skF_7') | ~r2_hidden(D_141, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_978, c_30])).
% 3.95/1.71  tff(c_1158, plain, (![B_4]: (~r2_hidden('#skF_1'(k3_subset_1('#skF_6', '#skF_7'), B_4), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_4))), inference(resolution, [status(thm)], [c_8, c_1153])).
% 3.95/1.71  tff(c_1469, plain, (![B_160]: (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_160))), inference(resolution, [status(thm)], [c_1465, c_1158])).
% 3.95/1.71  tff(c_1547, plain, (![B_162]: (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_162))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_1469])).
% 3.95/1.71  tff(c_48, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.71  tff(c_1718, plain, (![B_172]: (k3_xboole_0(k3_subset_1('#skF_6', '#skF_7'), B_172)=k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1547, c_48])).
% 3.95/1.71  tff(c_549, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.71  tff(c_558, plain, (![A_85]: (k3_xboole_0(k1_xboole_0, A_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_549])).
% 3.95/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.71  tff(c_563, plain, (![A_85]: (k3_xboole_0(A_85, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_558, c_2])).
% 3.95/1.71  tff(c_1742, plain, (k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1718, c_563])).
% 3.95/1.71  tff(c_931, plain, (![A_122, B_123]: (k3_subset_1(A_122, k3_subset_1(A_122, B_123))=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.95/1.71  tff(c_938, plain, (k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_64, c_931])).
% 3.95/1.71  tff(c_1782, plain, (k3_subset_1('#skF_6', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_938])).
% 3.95/1.71  tff(c_1790, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1782])).
% 3.95/1.71  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_1790])).
% 3.95/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.71  
% 3.95/1.71  Inference rules
% 3.95/1.71  ----------------------
% 3.95/1.71  #Ref     : 0
% 3.95/1.71  #Sup     : 427
% 3.95/1.71  #Fact    : 0
% 3.95/1.71  #Define  : 0
% 3.95/1.71  #Split   : 2
% 3.95/1.71  #Chain   : 0
% 3.95/1.71  #Close   : 0
% 3.95/1.71  
% 3.95/1.71  Ordering : KBO
% 3.95/1.71  
% 3.95/1.71  Simplification rules
% 3.95/1.71  ----------------------
% 3.95/1.71  #Subsume      : 80
% 3.95/1.71  #Demod        : 122
% 3.95/1.71  #Tautology    : 203
% 3.95/1.71  #SimpNegUnit  : 3
% 3.95/1.71  #BackRed      : 24
% 3.95/1.71  
% 3.95/1.71  #Partial instantiations: 0
% 3.95/1.71  #Strategies tried      : 1
% 3.95/1.71  
% 3.95/1.71  Timing (in seconds)
% 3.95/1.71  ----------------------
% 3.95/1.71  Preprocessing        : 0.35
% 3.95/1.71  Parsing              : 0.18
% 3.95/1.71  CNF conversion       : 0.03
% 3.95/1.71  Main loop            : 0.53
% 3.95/1.71  Inferencing          : 0.19
% 3.95/1.71  Reduction            : 0.18
% 3.95/1.71  Demodulation         : 0.13
% 3.95/1.71  BG Simplification    : 0.03
% 3.95/1.71  Subsumption          : 0.10
% 3.95/1.71  Abstraction          : 0.03
% 3.95/1.71  MUC search           : 0.00
% 3.95/1.71  Cooper               : 0.00
% 3.95/1.71  Total                : 0.91
% 3.95/1.71  Index Insertion      : 0.00
% 3.95/1.71  Index Deletion       : 0.00
% 3.95/1.71  Index Matching       : 0.00
% 3.95/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
