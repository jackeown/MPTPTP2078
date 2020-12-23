%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 109 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 188 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1174,plain,(
    ! [B_109,A_110] :
      ( r2_hidden(B_109,A_110)
      | ~ m1_subset_1(B_109,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1181,plain,(
    ! [B_109,A_19] :
      ( r1_tarski(B_109,A_19)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1174,c_18])).

tff(c_1186,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1181])).

tff(c_1203,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1186])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_128,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_209,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_52])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_513,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_529,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_513])).

tff(c_256,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_263,plain,(
    ! [B_59,A_19] :
      ( r1_tarski(B_59,A_19)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_256,c_18])).

tff(c_268,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_263])).

tff(c_284,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_268])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_289,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_284,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_309,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_2])).

tff(c_363,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_384,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_363])).

tff(c_542,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_384])).

tff(c_143,plain,(
    ! [A_47,B_48] : r1_xboole_0(k3_xboole_0(A_47,B_48),k5_xboole_0(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_49,B_50] : r1_xboole_0(k5_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) ),
    inference(resolution,[status(thm)],[c_143,c_6])).

tff(c_167,plain,(
    ! [B_2,A_1] : r1_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_297,plain,(
    r1_xboole_0(k5_xboole_0('#skF_3','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_167])).

tff(c_423,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_xboole_0(A_65,C_66)
      | ~ r1_xboole_0(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_440,plain,(
    ! [A_65] :
      ( r1_xboole_0(A_65,'#skF_5')
      | ~ r1_tarski(A_65,k5_xboole_0('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_297,c_423])).

tff(c_1013,plain,(
    ! [A_90] :
      ( r1_xboole_0(A_90,'#skF_5')
      | ~ r1_tarski(A_90,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_440])).

tff(c_1023,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_209,c_1013])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_1023])).

tff(c_1031,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1346,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(A_117,B_118) = k3_subset_1(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1362,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1346])).

tff(c_1385,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski(A_120,k4_xboole_0(B_121,C_122))
      | ~ r1_xboole_0(A_120,C_122)
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1496,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_128,'#skF_5')
      | ~ r1_tarski(A_128,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1362,c_1385])).

tff(c_1030,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1499,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1496,c_1030])).

tff(c_1506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_1031,c_1499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.55  
% 3.38/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.38/1.55  
% 3.38/1.55  %Foreground sorts:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Background operators:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Foreground operators:
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.38/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.55  
% 3.49/1.57  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 3.49/1.57  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.49/1.57  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.49/1.57  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.49/1.57  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.49/1.57  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.49/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.49/1.57  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.49/1.57  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.49/1.57  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.49/1.57  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.49/1.57  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.49/1.57  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.57  tff(c_40, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.49/1.57  tff(c_1174, plain, (![B_109, A_110]: (r2_hidden(B_109, A_110) | ~m1_subset_1(B_109, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.57  tff(c_18, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.57  tff(c_1181, plain, (![B_109, A_19]: (r1_tarski(B_109, A_19) | ~m1_subset_1(B_109, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1174, c_18])).
% 3.49/1.57  tff(c_1186, plain, (![B_111, A_112]: (r1_tarski(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(negUnitSimplification, [status(thm)], [c_40, c_1181])).
% 3.49/1.57  tff(c_1203, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1186])).
% 3.49/1.57  tff(c_46, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.57  tff(c_128, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.49/1.57  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.57  tff(c_209, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_128, c_52])).
% 3.49/1.57  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.57  tff(c_513, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.57  tff(c_529, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_513])).
% 3.49/1.57  tff(c_256, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.57  tff(c_263, plain, (![B_59, A_19]: (r1_tarski(B_59, A_19) | ~m1_subset_1(B_59, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_256, c_18])).
% 3.49/1.57  tff(c_268, plain, (![B_61, A_62]: (r1_tarski(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(negUnitSimplification, [status(thm)], [c_40, c_263])).
% 3.49/1.57  tff(c_284, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_268])).
% 3.49/1.57  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.57  tff(c_289, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_284, c_12])).
% 3.49/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.57  tff(c_309, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_289, c_2])).
% 3.49/1.57  tff(c_363, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.57  tff(c_384, plain, (k5_xboole_0('#skF_3', '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_309, c_363])).
% 3.49/1.57  tff(c_542, plain, (k5_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_529, c_384])).
% 3.49/1.57  tff(c_143, plain, (![A_47, B_48]: (r1_xboole_0(k3_xboole_0(A_47, B_48), k5_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.57  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.49/1.57  tff(c_159, plain, (![A_49, B_50]: (r1_xboole_0(k5_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_143, c_6])).
% 3.49/1.57  tff(c_167, plain, (![B_2, A_1]: (r1_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_159])).
% 3.49/1.57  tff(c_297, plain, (r1_xboole_0(k5_xboole_0('#skF_3', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_289, c_167])).
% 3.49/1.57  tff(c_423, plain, (![A_65, C_66, B_67]: (r1_xboole_0(A_65, C_66) | ~r1_xboole_0(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.57  tff(c_440, plain, (![A_65]: (r1_xboole_0(A_65, '#skF_5') | ~r1_tarski(A_65, k5_xboole_0('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_297, c_423])).
% 3.49/1.57  tff(c_1013, plain, (![A_90]: (r1_xboole_0(A_90, '#skF_5') | ~r1_tarski(A_90, k3_subset_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_440])).
% 3.49/1.57  tff(c_1023, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_209, c_1013])).
% 3.49/1.57  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_1023])).
% 3.49/1.57  tff(c_1031, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.49/1.57  tff(c_1346, plain, (![A_117, B_118]: (k4_xboole_0(A_117, B_118)=k3_subset_1(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.49/1.57  tff(c_1362, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1346])).
% 3.49/1.57  tff(c_1385, plain, (![A_120, B_121, C_122]: (r1_tarski(A_120, k4_xboole_0(B_121, C_122)) | ~r1_xboole_0(A_120, C_122) | ~r1_tarski(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.49/1.57  tff(c_1496, plain, (![A_128]: (r1_tarski(A_128, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_128, '#skF_5') | ~r1_tarski(A_128, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1362, c_1385])).
% 3.49/1.57  tff(c_1030, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 3.49/1.57  tff(c_1499, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1496, c_1030])).
% 3.49/1.57  tff(c_1506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1203, c_1031, c_1499])).
% 3.49/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.57  
% 3.49/1.57  Inference rules
% 3.49/1.57  ----------------------
% 3.49/1.57  #Ref     : 0
% 3.49/1.57  #Sup     : 382
% 3.49/1.57  #Fact    : 0
% 3.49/1.57  #Define  : 0
% 3.49/1.57  #Split   : 1
% 3.49/1.57  #Chain   : 0
% 3.49/1.57  #Close   : 0
% 3.49/1.57  
% 3.49/1.57  Ordering : KBO
% 3.49/1.57  
% 3.49/1.57  Simplification rules
% 3.49/1.57  ----------------------
% 3.49/1.57  #Subsume      : 14
% 3.49/1.57  #Demod        : 212
% 3.49/1.57  #Tautology    : 203
% 3.49/1.57  #SimpNegUnit  : 6
% 3.49/1.57  #BackRed      : 9
% 3.49/1.57  
% 3.49/1.57  #Partial instantiations: 0
% 3.49/1.57  #Strategies tried      : 1
% 3.49/1.57  
% 3.49/1.57  Timing (in seconds)
% 3.49/1.57  ----------------------
% 3.49/1.57  Preprocessing        : 0.31
% 3.49/1.57  Parsing              : 0.16
% 3.49/1.57  CNF conversion       : 0.02
% 3.49/1.57  Main loop            : 0.49
% 3.49/1.57  Inferencing          : 0.16
% 3.49/1.57  Reduction            : 0.19
% 3.49/1.57  Demodulation         : 0.14
% 3.49/1.57  BG Simplification    : 0.02
% 3.49/1.57  Subsumption          : 0.08
% 3.49/1.57  Abstraction          : 0.02
% 3.49/1.57  MUC search           : 0.00
% 3.49/1.57  Cooper               : 0.00
% 3.49/1.57  Total                : 0.84
% 3.49/1.57  Index Insertion      : 0.00
% 3.49/1.57  Index Deletion       : 0.00
% 3.49/1.58  Index Matching       : 0.00
% 3.49/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
