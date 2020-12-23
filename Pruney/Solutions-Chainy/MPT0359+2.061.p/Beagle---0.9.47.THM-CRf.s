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
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 139 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 231 expanded)
%              Number of equality atoms :   28 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_24,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_87,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_38])).

tff(c_157,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k3_subset_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [B_33,A_34] :
      ( r2_hidden(B_33,A_34)
      | ~ m1_subset_1(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [B_33,A_1] :
      ( r1_tarski(B_33,A_1)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_132,plain,(
    ! [B_33,A_1] :
      ( r1_tarski(B_33,A_1)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_128])).

tff(c_192,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k3_subset_1(A_44,B_45),A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_157,c_132])).

tff(c_40,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_98,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_50])).

tff(c_195,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_192,c_98])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_195])).

tff(c_204,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_239,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_246,plain,(
    ! [B_55,A_1] :
      ( r1_tarski(B_55,A_1)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_251,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_246])).

tff(c_264,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_251])).

tff(c_22,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_52,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_49])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_300,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(A_64,k3_subset_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_316,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_300])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k1_subset_1(A_16) = B_17
      | ~ r1_tarski(B_17,k3_subset_1(A_16,B_17))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_389,plain,(
    ! [B_72,A_73] :
      ( k1_xboole_0 = B_72
      | ~ r1_tarski(B_72,k3_subset_1(A_73,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_395,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_389])).

tff(c_400,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_395])).

tff(c_438,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_441,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_438])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_441])).

tff(c_452,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_217,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_220,plain,(
    ! [C_5,A_1] :
      ( m1_subset_1(C_5,k1_zfmisc_1(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_223,plain,(
    ! [C_5,A_1] :
      ( m1_subset_1(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_220])).

tff(c_314,plain,(
    ! [A_1,C_5] :
      ( k3_subset_1(A_1,k3_subset_1(A_1,C_5)) = C_5
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(resolution,[status(thm)],[c_223,c_300])).

tff(c_462,plain,
    ( k3_subset_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_314])).

tff(c_474,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_52,c_462])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.17/1.32  
% 2.17/1.32  %Foreground sorts:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Background operators:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Foreground operators:
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.17/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.17/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.17/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.32  
% 2.39/1.34  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.39/1.34  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.39/1.34  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.39/1.34  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.39/1.34  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.39/1.34  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.39/1.34  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.39/1.34  tff(f_62, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.39/1.34  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.39/1.34  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.39/1.34  tff(c_24, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.39/1.34  tff(c_46, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.34  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 2.39/1.34  tff(c_87, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.39/1.34  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.34  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_38])).
% 2.39/1.34  tff(c_157, plain, (![A_39, B_40]: (m1_subset_1(k3_subset_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.34  tff(c_28, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.39/1.34  tff(c_121, plain, (![B_33, A_34]: (r2_hidden(B_33, A_34) | ~m1_subset_1(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.34  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.34  tff(c_128, plain, (![B_33, A_1]: (r1_tarski(B_33, A_1) | ~m1_subset_1(B_33, k1_zfmisc_1(A_1)) | v1_xboole_0(k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_121, c_2])).
% 2.39/1.34  tff(c_132, plain, (![B_33, A_1]: (r1_tarski(B_33, A_1) | ~m1_subset_1(B_33, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_28, c_128])).
% 2.39/1.34  tff(c_192, plain, (![A_44, B_45]: (r1_tarski(k3_subset_1(A_44, B_45), A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_157, c_132])).
% 2.39/1.34  tff(c_40, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.34  tff(c_50, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40])).
% 2.39/1.34  tff(c_98, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_50])).
% 2.39/1.34  tff(c_195, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_192, c_98])).
% 2.39/1.34  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_195])).
% 2.39/1.34  tff(c_204, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.39/1.34  tff(c_239, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.34  tff(c_246, plain, (![B_55, A_1]: (r1_tarski(B_55, A_1) | ~m1_subset_1(B_55, k1_zfmisc_1(A_1)) | v1_xboole_0(k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_239, c_2])).
% 2.39/1.34  tff(c_251, plain, (![B_57, A_58]: (r1_tarski(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_28, c_246])).
% 2.39/1.34  tff(c_264, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_251])).
% 2.39/1.34  tff(c_22, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.34  tff(c_32, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.34  tff(c_49, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 2.39/1.34  tff(c_52, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_49])).
% 2.39/1.34  tff(c_26, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.34  tff(c_203, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.39/1.34  tff(c_300, plain, (![A_64, B_65]: (k3_subset_1(A_64, k3_subset_1(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.34  tff(c_316, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_38, c_300])).
% 2.39/1.34  tff(c_36, plain, (![A_16, B_17]: (k1_subset_1(A_16)=B_17 | ~r1_tarski(B_17, k3_subset_1(A_16, B_17)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.39/1.34  tff(c_389, plain, (![B_72, A_73]: (k1_xboole_0=B_72 | ~r1_tarski(B_72, k3_subset_1(A_73, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36])).
% 2.39/1.34  tff(c_395, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_389])).
% 2.39/1.34  tff(c_400, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_395])).
% 2.39/1.34  tff(c_438, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_400])).
% 2.39/1.34  tff(c_441, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_438])).
% 2.39/1.34  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_441])).
% 2.39/1.34  tff(c_452, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_400])).
% 2.39/1.34  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.34  tff(c_217, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~r2_hidden(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.34  tff(c_220, plain, (![C_5, A_1]: (m1_subset_1(C_5, k1_zfmisc_1(A_1)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(resolution, [status(thm)], [c_4, c_217])).
% 2.39/1.34  tff(c_223, plain, (![C_5, A_1]: (m1_subset_1(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(negUnitSimplification, [status(thm)], [c_28, c_220])).
% 2.39/1.34  tff(c_314, plain, (![A_1, C_5]: (k3_subset_1(A_1, k3_subset_1(A_1, C_5))=C_5 | ~r1_tarski(C_5, A_1))), inference(resolution, [status(thm)], [c_223, c_300])).
% 2.39/1.34  tff(c_462, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_452, c_314])).
% 2.39/1.34  tff(c_474, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_52, c_462])).
% 2.39/1.34  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_474])).
% 2.39/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  Inference rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Ref     : 0
% 2.39/1.34  #Sup     : 94
% 2.39/1.34  #Fact    : 0
% 2.39/1.34  #Define  : 0
% 2.39/1.34  #Split   : 2
% 2.39/1.34  #Chain   : 0
% 2.39/1.34  #Close   : 0
% 2.39/1.34  
% 2.39/1.34  Ordering : KBO
% 2.39/1.34  
% 2.39/1.34  Simplification rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Subsume      : 27
% 2.39/1.34  #Demod        : 26
% 2.39/1.34  #Tautology    : 40
% 2.39/1.34  #SimpNegUnit  : 5
% 2.39/1.34  #BackRed      : 3
% 2.39/1.34  
% 2.39/1.34  #Partial instantiations: 0
% 2.39/1.34  #Strategies tried      : 1
% 2.39/1.34  
% 2.39/1.34  Timing (in seconds)
% 2.39/1.34  ----------------------
% 2.39/1.34  Preprocessing        : 0.28
% 2.39/1.34  Parsing              : 0.15
% 2.39/1.34  CNF conversion       : 0.02
% 2.39/1.34  Main loop            : 0.25
% 2.39/1.34  Inferencing          : 0.09
% 2.39/1.34  Reduction            : 0.08
% 2.39/1.34  Demodulation         : 0.05
% 2.39/1.34  BG Simplification    : 0.02
% 2.39/1.34  Subsumption          : 0.05
% 2.39/1.34  Abstraction          : 0.01
% 2.39/1.34  MUC search           : 0.00
% 2.39/1.34  Cooper               : 0.00
% 2.39/1.34  Total                : 0.56
% 2.39/1.34  Index Insertion      : 0.00
% 2.39/1.34  Index Deletion       : 0.00
% 2.39/1.34  Index Matching       : 0.00
% 2.39/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
