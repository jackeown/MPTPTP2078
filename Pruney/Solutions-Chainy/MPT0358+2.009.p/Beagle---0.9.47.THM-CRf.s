%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 145 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 238 expanded)
%              Number of equality atoms :   43 (  95 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_226,plain,(
    ! [B_55,A_11] :
      ( r1_tarski(B_55,A_11)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_219,c_18])).

tff(c_246,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_226])).

tff(c_259,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_38,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_55])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = '#skF_4'
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_266,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_259,c_124])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = '#skF_4'
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_129,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_125])).

tff(c_20,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_210,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_213,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_210])).

tff(c_358,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_409,plain,(
    ! [A_73,C_74] :
      ( k4_xboole_0(A_73,C_74) = k3_subset_1(A_73,C_74)
      | ~ r1_tarski(C_74,A_73) ) ),
    inference(resolution,[status(thm)],[c_213,c_358])).

tff(c_421,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_409])).

tff(c_428,plain,(
    ! [B_75] : k3_subset_1(B_75,B_75) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_421])).

tff(c_231,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_239,plain,(
    ! [A_11,C_15] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,C_15)) = C_15
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_213,c_231])).

tff(c_433,plain,(
    ! [B_75] :
      ( k3_subset_1(B_75,'#skF_4') = B_75
      | ~ r1_tarski(B_75,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_239])).

tff(c_438,plain,(
    ! [B_75] : k3_subset_1(B_75,'#skF_4') = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_433])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_168,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_150,c_105])).

tff(c_443,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_168])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_443])).

tff(c_449,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_450,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_452,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_459,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_450,c_452])).

tff(c_668,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_681,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_668])).

tff(c_498,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | k4_xboole_0(A_88,B_89) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_511,plain,(
    ! [A_88,B_10] :
      ( k1_xboole_0 = A_88
      | k4_xboole_0(A_88,k4_xboole_0(B_10,A_88)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_498,c_16])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_511])).

tff(c_693,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_686])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.61/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.41  
% 2.61/1.43  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.61/1.43  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.61/1.43  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.61/1.43  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.61/1.43  tff(f_65, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.61/1.43  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.61/1.43  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.43  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.61/1.43  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.61/1.43  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.61/1.43  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.43  tff(c_42, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.43  tff(c_219, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.43  tff(c_18, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.43  tff(c_226, plain, (![B_55, A_11]: (r1_tarski(B_55, A_11) | ~m1_subset_1(B_55, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_219, c_18])).
% 2.61/1.43  tff(c_246, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_42, c_226])).
% 2.61/1.43  tff(c_259, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_246])).
% 2.61/1.43  tff(c_38, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.61/1.43  tff(c_48, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.43  tff(c_56, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 2.61/1.43  tff(c_105, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.61/1.43  tff(c_54, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.43  tff(c_55, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54])).
% 2.61/1.43  tff(c_111, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_105, c_55])).
% 2.61/1.43  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.43  tff(c_124, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)='#skF_4' | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_12])).
% 2.61/1.43  tff(c_266, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_259, c_124])).
% 2.61/1.43  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.43  tff(c_125, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)='#skF_4' | ~r1_tarski(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_12])).
% 2.61/1.43  tff(c_129, plain, (![B_4]: (k4_xboole_0(B_4, B_4)='#skF_4')), inference(resolution, [status(thm)], [c_8, c_125])).
% 2.61/1.43  tff(c_20, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.43  tff(c_207, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.43  tff(c_210, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_20, c_207])).
% 2.61/1.43  tff(c_213, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_42, c_210])).
% 2.61/1.43  tff(c_358, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.43  tff(c_409, plain, (![A_73, C_74]: (k4_xboole_0(A_73, C_74)=k3_subset_1(A_73, C_74) | ~r1_tarski(C_74, A_73))), inference(resolution, [status(thm)], [c_213, c_358])).
% 2.61/1.43  tff(c_421, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(resolution, [status(thm)], [c_8, c_409])).
% 2.61/1.43  tff(c_428, plain, (![B_75]: (k3_subset_1(B_75, B_75)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_421])).
% 2.61/1.43  tff(c_231, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.61/1.43  tff(c_239, plain, (![A_11, C_15]: (k3_subset_1(A_11, k3_subset_1(A_11, C_15))=C_15 | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_213, c_231])).
% 2.61/1.43  tff(c_433, plain, (![B_75]: (k3_subset_1(B_75, '#skF_4')=B_75 | ~r1_tarski(B_75, B_75))), inference(superposition, [status(thm), theory('equality')], [c_428, c_239])).
% 2.61/1.43  tff(c_438, plain, (![B_75]: (k3_subset_1(B_75, '#skF_4')=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_433])).
% 2.61/1.43  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.43  tff(c_150, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | k4_xboole_0(A_40, B_41)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_10])).
% 2.61/1.43  tff(c_168, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_150, c_105])).
% 2.61/1.43  tff(c_443, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_168])).
% 2.61/1.43  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_443])).
% 2.61/1.43  tff(c_449, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 2.61/1.43  tff(c_450, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 2.61/1.43  tff(c_452, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.43  tff(c_459, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_450, c_452])).
% 2.61/1.43  tff(c_668, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.43  tff(c_681, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_668])).
% 2.61/1.43  tff(c_498, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | k4_xboole_0(A_88, B_89)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.43  tff(c_16, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.43  tff(c_511, plain, (![A_88, B_10]: (k1_xboole_0=A_88 | k4_xboole_0(A_88, k4_xboole_0(B_10, A_88))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_498, c_16])).
% 2.61/1.43  tff(c_686, plain, (k1_xboole_0='#skF_4' | k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_681, c_511])).
% 2.61/1.43  tff(c_693, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_459, c_686])).
% 2.61/1.43  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_693])).
% 2.61/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  Inference rules
% 2.61/1.43  ----------------------
% 2.61/1.43  #Ref     : 0
% 2.61/1.43  #Sup     : 144
% 2.61/1.43  #Fact    : 0
% 2.61/1.43  #Define  : 0
% 2.61/1.43  #Split   : 4
% 2.61/1.43  #Chain   : 0
% 2.61/1.43  #Close   : 0
% 2.61/1.43  
% 2.61/1.43  Ordering : KBO
% 2.61/1.43  
% 2.61/1.43  Simplification rules
% 2.61/1.43  ----------------------
% 2.61/1.43  #Subsume      : 22
% 2.61/1.43  #Demod        : 40
% 2.61/1.43  #Tautology    : 80
% 2.61/1.43  #SimpNegUnit  : 7
% 2.61/1.43  #BackRed      : 7
% 2.61/1.43  
% 2.61/1.43  #Partial instantiations: 0
% 2.61/1.43  #Strategies tried      : 1
% 2.61/1.43  
% 2.61/1.43  Timing (in seconds)
% 2.61/1.43  ----------------------
% 2.61/1.43  Preprocessing        : 0.33
% 2.61/1.43  Parsing              : 0.18
% 2.61/1.43  CNF conversion       : 0.02
% 2.61/1.43  Main loop            : 0.31
% 2.61/1.43  Inferencing          : 0.11
% 2.61/1.43  Reduction            : 0.09
% 2.61/1.43  Demodulation         : 0.07
% 2.61/1.43  BG Simplification    : 0.02
% 2.61/1.43  Subsumption          : 0.06
% 2.61/1.43  Abstraction          : 0.02
% 2.61/1.43  MUC search           : 0.00
% 2.61/1.43  Cooper               : 0.00
% 2.61/1.43  Total                : 0.67
% 2.61/1.43  Index Insertion      : 0.00
% 2.61/1.43  Index Deletion       : 0.00
% 2.61/1.43  Index Matching       : 0.00
% 2.61/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
