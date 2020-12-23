%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1551,plain,(
    ! [B_143,A_144] :
      ( r2_hidden(B_143,A_144)
      | ~ m1_subset_1(B_143,A_144)
      | v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1555,plain,(
    ! [B_143,A_11] :
      ( r1_tarski(B_143,A_11)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_1551,c_12])).

tff(c_1559,plain,(
    ! [B_145,A_146] :
      ( r1_tarski(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_146)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1555])).

tff(c_1571,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1559])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_88,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_233,plain,(
    ! [A_59,B_60] :
      ( k3_subset_1(A_59,k3_subset_1(A_59,B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_246,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_233])).

tff(c_326,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k3_subset_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k3_subset_1(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1158,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,k3_subset_1(A_131,B_132)) = k3_subset_1(A_131,k3_subset_1(A_131,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_326,c_32])).

tff(c_1169,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_1158])).

tff(c_1176,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_1169])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1505,plain,(
    ! [A_140] :
      ( r1_xboole_0(A_140,'#skF_5')
      | ~ r1_tarski(A_140,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_8])).

tff(c_1523,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1505])).

tff(c_1531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1523])).

tff(c_1533,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1678,plain,(
    ! [A_161,B_162] :
      ( k4_xboole_0(A_161,B_162) = k3_subset_1(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1695,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1678])).

tff(c_1980,plain,(
    ! [A_177,B_178,C_179] :
      ( r1_tarski(A_177,k4_xboole_0(B_178,C_179))
      | ~ r1_xboole_0(A_177,C_179)
      | ~ r1_tarski(A_177,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2058,plain,(
    ! [A_190] :
      ( r1_tarski(A_190,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_190,'#skF_5')
      | ~ r1_tarski(A_190,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_1980])).

tff(c_1532,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2064,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2058,c_1532])).

tff(c_2069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1533,c_2064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:07:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.69  
% 3.73/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.73/1.69  
% 3.73/1.69  %Foreground sorts:
% 3.73/1.69  
% 3.73/1.69  
% 3.73/1.69  %Background operators:
% 3.73/1.69  
% 3.73/1.69  
% 3.73/1.69  %Foreground operators:
% 3.73/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.69  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.73/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.73/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.73/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.73/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.69  
% 3.73/1.70  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 3.73/1.70  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.73/1.70  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.73/1.70  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.73/1.70  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.73/1.70  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.73/1.70  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.73/1.70  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.73/1.70  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.73/1.70  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.73/1.70  tff(c_36, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.73/1.70  tff(c_1551, plain, (![B_143, A_144]: (r2_hidden(B_143, A_144) | ~m1_subset_1(B_143, A_144) | v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.73/1.70  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.70  tff(c_1555, plain, (![B_143, A_11]: (r1_tarski(B_143, A_11) | ~m1_subset_1(B_143, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_1551, c_12])).
% 3.73/1.70  tff(c_1559, plain, (![B_145, A_146]: (r1_tarski(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(A_146)))), inference(negUnitSimplification, [status(thm)], [c_36, c_1555])).
% 3.73/1.70  tff(c_1571, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1559])).
% 3.73/1.70  tff(c_44, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.73/1.70  tff(c_78, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 3.73/1.70  tff(c_50, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.73/1.70  tff(c_88, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_50])).
% 3.73/1.70  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.73/1.70  tff(c_233, plain, (![A_59, B_60]: (k3_subset_1(A_59, k3_subset_1(A_59, B_60))=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.70  tff(c_246, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_40, c_233])).
% 3.73/1.70  tff(c_326, plain, (![A_63, B_64]: (m1_subset_1(k3_subset_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.70  tff(c_32, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k3_subset_1(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.73/1.70  tff(c_1158, plain, (![A_131, B_132]: (k4_xboole_0(A_131, k3_subset_1(A_131, B_132))=k3_subset_1(A_131, k3_subset_1(A_131, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(resolution, [status(thm)], [c_326, c_32])).
% 3.73/1.70  tff(c_1169, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_1158])).
% 3.73/1.70  tff(c_1176, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_1169])).
% 3.73/1.70  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.70  tff(c_1505, plain, (![A_140]: (r1_xboole_0(A_140, '#skF_5') | ~r1_tarski(A_140, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_8])).
% 3.73/1.70  tff(c_1523, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_88, c_1505])).
% 3.73/1.70  tff(c_1531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1523])).
% 3.73/1.70  tff(c_1533, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 3.73/1.70  tff(c_1678, plain, (![A_161, B_162]: (k4_xboole_0(A_161, B_162)=k3_subset_1(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.73/1.70  tff(c_1695, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_1678])).
% 3.73/1.70  tff(c_1980, plain, (![A_177, B_178, C_179]: (r1_tarski(A_177, k4_xboole_0(B_178, C_179)) | ~r1_xboole_0(A_177, C_179) | ~r1_tarski(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.70  tff(c_2058, plain, (![A_190]: (r1_tarski(A_190, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_190, '#skF_5') | ~r1_tarski(A_190, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_1980])).
% 3.73/1.70  tff(c_1532, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 3.73/1.70  tff(c_2064, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2058, c_1532])).
% 3.73/1.70  tff(c_2069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1571, c_1533, c_2064])).
% 3.73/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.70  
% 3.73/1.70  Inference rules
% 3.73/1.70  ----------------------
% 3.73/1.70  #Ref     : 0
% 3.73/1.70  #Sup     : 536
% 3.73/1.70  #Fact    : 0
% 3.73/1.70  #Define  : 0
% 3.73/1.70  #Split   : 6
% 3.73/1.70  #Chain   : 0
% 3.73/1.70  #Close   : 0
% 3.73/1.70  
% 3.73/1.70  Ordering : KBO
% 3.73/1.70  
% 3.73/1.70  Simplification rules
% 3.73/1.70  ----------------------
% 3.73/1.70  #Subsume      : 92
% 3.73/1.70  #Demod        : 84
% 3.73/1.70  #Tautology    : 198
% 3.73/1.70  #SimpNegUnit  : 15
% 3.73/1.70  #BackRed      : 1
% 3.73/1.70  
% 3.73/1.70  #Partial instantiations: 0
% 3.73/1.70  #Strategies tried      : 1
% 3.73/1.70  
% 3.73/1.70  Timing (in seconds)
% 3.73/1.70  ----------------------
% 3.73/1.70  Preprocessing        : 0.33
% 3.73/1.70  Parsing              : 0.17
% 3.73/1.70  CNF conversion       : 0.02
% 3.73/1.70  Main loop            : 0.61
% 3.73/1.70  Inferencing          : 0.22
% 3.73/1.70  Reduction            : 0.17
% 3.73/1.70  Demodulation         : 0.11
% 3.73/1.70  BG Simplification    : 0.03
% 3.73/1.70  Subsumption          : 0.13
% 3.73/1.70  Abstraction          : 0.03
% 3.73/1.70  MUC search           : 0.00
% 3.73/1.70  Cooper               : 0.00
% 3.73/1.70  Total                : 0.96
% 3.73/1.70  Index Insertion      : 0.00
% 3.73/1.70  Index Deletion       : 0.00
% 3.73/1.70  Index Matching       : 0.00
% 3.73/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
