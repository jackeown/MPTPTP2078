%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   70 (  87 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 128 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_186,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_612,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_628,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_612])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_335,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(A_64,C_65)
      | ~ r1_xboole_0(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_343,plain,(
    ! [A_64,B_16,A_15] :
      ( r1_xboole_0(A_64,B_16)
      | ~ r1_tarski(A_64,k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_18,c_335])).

tff(c_922,plain,(
    ! [A_96] :
      ( r1_xboole_0(A_96,'#skF_5')
      | ~ r1_tarski(A_96,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_343])).

tff(c_929,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_186,c_922])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_929])).

tff(c_935,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1143,plain,(
    ! [B_118,A_119] :
      ( r2_hidden(B_118,A_119)
      | ~ m1_subset_1(B_118,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1150,plain,(
    ! [B_118,A_17] :
      ( r1_tarski(B_118,A_17)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1143,c_20])).

tff(c_1250,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1150])).

tff(c_1267,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1250])).

tff(c_1614,plain,(
    ! [A_152,B_153] :
      ( k4_xboole_0(A_152,B_153) = k3_subset_1(A_152,B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1630,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1614])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_938,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0(A_99,B_100) = k1_xboole_0
      | ~ r1_xboole_0(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_954,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_938])).

tff(c_1103,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k3_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1121,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_1103])).

tff(c_1133,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1121])).

tff(c_936,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_952,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_936,c_938])).

tff(c_1124,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_1103])).

tff(c_1155,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_1124])).

tff(c_1435,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(k4_xboole_0(A_142,C_143),k4_xboole_0(B_144,C_143))
      | ~ r1_tarski(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1956,plain,(
    ! [B_163] :
      ( r1_tarski('#skF_4',k4_xboole_0(B_163,'#skF_5'))
      | ~ r1_tarski('#skF_4',B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_1435])).

tff(c_1964,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_1956])).

tff(c_1981,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1267,c_1964])).

tff(c_1983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_935,c_1981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.62  
% 3.18/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.18/1.62  
% 3.18/1.62  %Foreground sorts:
% 3.18/1.62  
% 3.18/1.62  
% 3.18/1.62  %Background operators:
% 3.18/1.62  
% 3.18/1.62  
% 3.18/1.62  %Foreground operators:
% 3.18/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.18/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.18/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.62  
% 3.18/1.63  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 3.18/1.63  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.18/1.63  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.18/1.63  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.18/1.63  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.18/1.63  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.18/1.63  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.18/1.63  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.18/1.63  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.63  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.18/1.63  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.18/1.63  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 3.18/1.63  tff(c_48, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.63  tff(c_106, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.18/1.63  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.63  tff(c_186, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_106, c_54])).
% 3.18/1.63  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.63  tff(c_612, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.63  tff(c_628, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_612])).
% 3.18/1.63  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.63  tff(c_335, plain, (![A_64, C_65, B_66]: (r1_xboole_0(A_64, C_65) | ~r1_xboole_0(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.63  tff(c_343, plain, (![A_64, B_16, A_15]: (r1_xboole_0(A_64, B_16) | ~r1_tarski(A_64, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_18, c_335])).
% 3.18/1.63  tff(c_922, plain, (![A_96]: (r1_xboole_0(A_96, '#skF_5') | ~r1_tarski(A_96, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_628, c_343])).
% 3.18/1.63  tff(c_929, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_186, c_922])).
% 3.18/1.63  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_929])).
% 3.18/1.63  tff(c_935, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 3.18/1.63  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.63  tff(c_42, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.63  tff(c_1143, plain, (![B_118, A_119]: (r2_hidden(B_118, A_119) | ~m1_subset_1(B_118, A_119) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.18/1.63  tff(c_20, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.63  tff(c_1150, plain, (![B_118, A_17]: (r1_tarski(B_118, A_17) | ~m1_subset_1(B_118, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_1143, c_20])).
% 3.18/1.63  tff(c_1250, plain, (![B_122, A_123]: (r1_tarski(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)))), inference(negUnitSimplification, [status(thm)], [c_42, c_1150])).
% 3.18/1.63  tff(c_1267, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1250])).
% 3.18/1.63  tff(c_1614, plain, (![A_152, B_153]: (k4_xboole_0(A_152, B_153)=k3_subset_1(A_152, B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.63  tff(c_1630, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1614])).
% 3.18/1.63  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.63  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.63  tff(c_938, plain, (![A_99, B_100]: (k3_xboole_0(A_99, B_100)=k1_xboole_0 | ~r1_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.63  tff(c_954, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_938])).
% 3.18/1.63  tff(c_1103, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k3_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.63  tff(c_1121, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_954, c_1103])).
% 3.18/1.63  tff(c_1133, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1121])).
% 3.18/1.63  tff(c_936, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.18/1.63  tff(c_952, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_936, c_938])).
% 3.18/1.63  tff(c_1124, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_952, c_1103])).
% 3.18/1.63  tff(c_1155, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_1124])).
% 3.18/1.63  tff(c_1435, plain, (![A_142, C_143, B_144]: (r1_tarski(k4_xboole_0(A_142, C_143), k4_xboole_0(B_144, C_143)) | ~r1_tarski(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.63  tff(c_1956, plain, (![B_163]: (r1_tarski('#skF_4', k4_xboole_0(B_163, '#skF_5')) | ~r1_tarski('#skF_4', B_163))), inference(superposition, [status(thm), theory('equality')], [c_1155, c_1435])).
% 3.18/1.63  tff(c_1964, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1630, c_1956])).
% 3.18/1.63  tff(c_1981, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1267, c_1964])).
% 3.18/1.63  tff(c_1983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_935, c_1981])).
% 3.18/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.63  
% 3.18/1.63  Inference rules
% 3.18/1.63  ----------------------
% 3.18/1.63  #Ref     : 0
% 3.18/1.63  #Sup     : 494
% 3.18/1.63  #Fact    : 0
% 3.18/1.63  #Define  : 0
% 3.18/1.63  #Split   : 2
% 3.18/1.63  #Chain   : 0
% 3.18/1.63  #Close   : 0
% 3.18/1.63  
% 3.18/1.63  Ordering : KBO
% 3.18/1.63  
% 3.18/1.63  Simplification rules
% 3.18/1.63  ----------------------
% 3.18/1.63  #Subsume      : 18
% 3.18/1.63  #Demod        : 230
% 3.18/1.63  #Tautology    : 300
% 3.18/1.63  #SimpNegUnit  : 8
% 3.18/1.63  #BackRed      : 0
% 3.18/1.63  
% 3.18/1.63  #Partial instantiations: 0
% 3.18/1.63  #Strategies tried      : 1
% 3.18/1.63  
% 3.18/1.63  Timing (in seconds)
% 3.18/1.63  ----------------------
% 3.18/1.64  Preprocessing        : 0.33
% 3.18/1.64  Parsing              : 0.17
% 3.18/1.64  CNF conversion       : 0.02
% 3.18/1.64  Main loop            : 0.49
% 3.18/1.64  Inferencing          : 0.17
% 3.18/1.64  Reduction            : 0.17
% 3.18/1.64  Demodulation         : 0.13
% 3.18/1.64  BG Simplification    : 0.02
% 3.18/1.64  Subsumption          : 0.08
% 3.18/1.64  Abstraction          : 0.02
% 3.18/1.64  MUC search           : 0.00
% 3.18/1.64  Cooper               : 0.00
% 3.18/1.64  Total                : 0.84
% 3.18/1.64  Index Insertion      : 0.00
% 3.18/1.64  Index Deletion       : 0.00
% 3.18/1.64  Index Matching       : 0.00
% 3.18/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
