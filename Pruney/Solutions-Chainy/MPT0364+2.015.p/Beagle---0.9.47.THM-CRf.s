%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 121 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_952,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(A_103,B_104)
      | k4_xboole_0(A_103,B_104) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_97,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_452,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_468,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_452])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,k4_xboole_0(C_15,B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_935,plain,(
    ! [A_102] :
      ( r1_xboole_0(A_102,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_102,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_16])).

tff(c_943,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_935,c_64])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_943])).

tff(c_950,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_963,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_952,c_950])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1009,plain,(
    ! [B_113,A_114] :
      ( r2_hidden(B_113,A_114)
      | ~ m1_subset_1(B_113,A_114)
      | v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1016,plain,(
    ! [B_113,A_16] :
      ( r1_tarski(B_113,A_16)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_1009,c_18])).

tff(c_1021,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_116)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1016])).

tff(c_1038,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1021])).

tff(c_951,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1239,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,B_132) = k3_subset_1(A_131,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1255,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1239])).

tff(c_1304,plain,(
    ! [B_134,A_135,C_136] :
      ( r1_xboole_0(B_134,k4_xboole_0(A_135,C_136))
      | ~ r1_xboole_0(A_135,k4_xboole_0(B_134,C_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4864,plain,(
    ! [A_274] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_274,'#skF_5'))
      | ~ r1_xboole_0(A_274,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_1304])).

tff(c_4913,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_951,c_4864])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4934,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4913,c_12])).

tff(c_1110,plain,(
    ! [A_122,C_123,B_124] :
      ( r1_tarski(k4_xboole_0(A_122,C_123),B_124)
      | ~ r1_tarski(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1135,plain,(
    ! [A_122,C_123,B_7] :
      ( k4_xboole_0(A_122,C_123) = k1_xboole_0
      | ~ r1_tarski(A_122,k4_xboole_0(B_7,k4_xboole_0(A_122,C_123))) ) ),
    inference(resolution,[status(thm)],[c_1110,c_8])).

tff(c_4970,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4934,c_1135])).

tff(c_5044,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_4970])).

tff(c_5046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_963,c_5044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.99  
% 4.98/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.98/1.99  
% 4.98/1.99  %Foreground sorts:
% 4.98/1.99  
% 4.98/1.99  
% 4.98/1.99  %Background operators:
% 4.98/1.99  
% 4.98/1.99  
% 4.98/1.99  %Foreground operators:
% 4.98/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.98/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.98/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.98/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.98/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.98/1.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.98/1.99  tff('#skF_5', type, '#skF_5': $i).
% 4.98/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.98/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.98/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.98/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.98/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.98/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.98/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.98/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.98/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.98/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.98/1.99  
% 4.98/2.00  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.98/2.00  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 4.98/2.00  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.98/2.00  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.98/2.00  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.98/2.00  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.98/2.00  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.98/2.00  tff(f_41, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 4.98/2.00  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.98/2.00  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 4.98/2.00  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.98/2.00  tff(c_952, plain, (![A_103, B_104]: (r1_tarski(A_103, B_104) | k4_xboole_0(A_103, B_104)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.98/2.00  tff(c_46, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.98/2.00  tff(c_64, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.98/2.00  tff(c_52, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.98/2.00  tff(c_97, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_52])).
% 4.98/2.00  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.98/2.00  tff(c_452, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.98/2.00  tff(c_468, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_452])).
% 4.98/2.00  tff(c_16, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, k4_xboole_0(C_15, B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.98/2.00  tff(c_935, plain, (![A_102]: (r1_xboole_0(A_102, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_102, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_16])).
% 4.98/2.00  tff(c_943, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_935, c_64])).
% 4.98/2.00  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_943])).
% 4.98/2.00  tff(c_950, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 4.98/2.00  tff(c_963, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_952, c_950])).
% 4.98/2.00  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.98/2.00  tff(c_40, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.98/2.00  tff(c_1009, plain, (![B_113, A_114]: (r2_hidden(B_113, A_114) | ~m1_subset_1(B_113, A_114) | v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.98/2.00  tff(c_18, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.98/2.00  tff(c_1016, plain, (![B_113, A_16]: (r1_tarski(B_113, A_16) | ~m1_subset_1(B_113, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_1009, c_18])).
% 4.98/2.00  tff(c_1021, plain, (![B_115, A_116]: (r1_tarski(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(A_116)))), inference(negUnitSimplification, [status(thm)], [c_40, c_1016])).
% 4.98/2.00  tff(c_1038, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1021])).
% 4.98/2.00  tff(c_951, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 4.98/2.00  tff(c_1239, plain, (![A_131, B_132]: (k4_xboole_0(A_131, B_132)=k3_subset_1(A_131, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.98/2.00  tff(c_1255, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1239])).
% 4.98/2.00  tff(c_1304, plain, (![B_134, A_135, C_136]: (r1_xboole_0(B_134, k4_xboole_0(A_135, C_136)) | ~r1_xboole_0(A_135, k4_xboole_0(B_134, C_136)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.98/2.00  tff(c_4864, plain, (![A_274]: (r1_xboole_0('#skF_3', k4_xboole_0(A_274, '#skF_5')) | ~r1_xboole_0(A_274, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1255, c_1304])).
% 4.98/2.00  tff(c_4913, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_951, c_4864])).
% 4.98/2.00  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.98/2.00  tff(c_4934, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_4913, c_12])).
% 4.98/2.00  tff(c_1110, plain, (![A_122, C_123, B_124]: (r1_tarski(k4_xboole_0(A_122, C_123), B_124) | ~r1_tarski(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.98/2.00  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k4_xboole_0(B_7, A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.98/2.00  tff(c_1135, plain, (![A_122, C_123, B_7]: (k4_xboole_0(A_122, C_123)=k1_xboole_0 | ~r1_tarski(A_122, k4_xboole_0(B_7, k4_xboole_0(A_122, C_123))))), inference(resolution, [status(thm)], [c_1110, c_8])).
% 4.98/2.00  tff(c_4970, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4934, c_1135])).
% 4.98/2.00  tff(c_5044, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_4970])).
% 4.98/2.00  tff(c_5046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_963, c_5044])).
% 4.98/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/2.00  
% 4.98/2.00  Inference rules
% 4.98/2.00  ----------------------
% 4.98/2.00  #Ref     : 0
% 4.98/2.00  #Sup     : 1233
% 4.98/2.00  #Fact    : 0
% 4.98/2.00  #Define  : 0
% 4.98/2.00  #Split   : 16
% 4.98/2.00  #Chain   : 0
% 4.98/2.00  #Close   : 0
% 4.98/2.00  
% 4.98/2.00  Ordering : KBO
% 4.98/2.00  
% 4.98/2.00  Simplification rules
% 4.98/2.00  ----------------------
% 4.98/2.00  #Subsume      : 461
% 4.98/2.00  #Demod        : 305
% 4.98/2.00  #Tautology    : 353
% 4.98/2.00  #SimpNegUnit  : 83
% 4.98/2.00  #BackRed      : 9
% 4.98/2.00  
% 4.98/2.00  #Partial instantiations: 0
% 4.98/2.00  #Strategies tried      : 1
% 4.98/2.00  
% 4.98/2.00  Timing (in seconds)
% 4.98/2.00  ----------------------
% 4.98/2.00  Preprocessing        : 0.31
% 4.98/2.00  Parsing              : 0.16
% 4.98/2.00  CNF conversion       : 0.02
% 4.98/2.00  Main loop            : 0.88
% 4.98/2.00  Inferencing          : 0.30
% 4.98/2.00  Reduction            : 0.28
% 4.98/2.00  Demodulation         : 0.18
% 4.98/2.00  BG Simplification    : 0.04
% 4.98/2.00  Subsumption          : 0.19
% 4.98/2.00  Abstraction          : 0.04
% 4.98/2.00  MUC search           : 0.00
% 4.98/2.00  Cooper               : 0.00
% 4.98/2.00  Total                : 1.22
% 4.98/2.00  Index Insertion      : 0.00
% 4.98/2.00  Index Deletion       : 0.00
% 4.98/2.00  Index Matching       : 0.00
% 4.98/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
