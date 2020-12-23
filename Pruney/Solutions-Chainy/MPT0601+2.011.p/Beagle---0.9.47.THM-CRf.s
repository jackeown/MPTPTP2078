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
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 102 expanded)
%              Number of leaves         :   42 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 154 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,
    ( k11_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k1_relat_1('#skF_11'))
    | k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_99,plain,(
    k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_32,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_1'(A_38),A_38)
      | v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_200,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden(k4_tarski(A_131,B_132),C_133)
      | ~ r2_hidden(B_132,k11_relat_1(C_133,A_131))
      | ~ v1_relat_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [C_71,A_56,D_74] :
      ( r2_hidden(C_71,k1_relat_1(A_56))
      | ~ r2_hidden(k4_tarski(C_71,D_74),A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_214,plain,(
    ! [A_134,C_135,B_136] :
      ( r2_hidden(A_134,k1_relat_1(C_135))
      | ~ r2_hidden(B_136,k11_relat_1(C_135,A_134))
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_200,c_36])).

tff(c_230,plain,(
    ! [A_137,C_138] :
      ( r2_hidden(A_137,k1_relat_1(C_138))
      | ~ v1_relat_1(C_138)
      | v1_relat_1(k11_relat_1(C_138,A_137)) ) ),
    inference(resolution,[status(thm)],[c_32,c_214])).

tff(c_244,plain,
    ( ~ v1_relat_1('#skF_11')
    | v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_230,c_98])).

tff(c_250,plain,(
    v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_244])).

tff(c_52,plain,(
    ! [A_80] :
      ( k1_xboole_0 = A_80
      | r2_hidden(k4_tarski('#skF_8'(A_80),'#skF_9'(A_80)),A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_465,plain,(
    ! [A_186,C_187] :
      ( r2_hidden(A_186,k1_relat_1(C_187))
      | ~ v1_relat_1(C_187)
      | k11_relat_1(C_187,A_186) = k1_xboole_0
      | ~ v1_relat_1(k11_relat_1(C_187,A_186)) ) ),
    inference(resolution,[status(thm)],[c_52,c_214])).

tff(c_494,plain,
    ( ~ v1_relat_1('#skF_11')
    | k11_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | ~ v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_465,c_98])).

tff(c_504,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_54,c_494])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_504])).

tff(c_507,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_507])).

tff(c_510,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_26,plain,(
    ! [A_35,B_37] :
      ( k9_relat_1(A_35,k1_tarski(B_37)) = k11_relat_1(A_35,B_37)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_511,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_84,B_85] : k2_xboole_0(k1_tarski(A_84),B_85) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [A_84] : k1_tarski(A_84) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_555,plain,(
    ! [A_208,B_209,C_210] :
      ( r1_tarski(k2_tarski(A_208,B_209),C_210)
      | ~ r2_hidden(B_209,C_210)
      | ~ r2_hidden(A_208,C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_564,plain,(
    ! [A_2,C_210] :
      ( r1_tarski(k1_tarski(A_2),C_210)
      | ~ r2_hidden(A_2,C_210)
      | ~ r2_hidden(A_2,C_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_555])).

tff(c_624,plain,(
    ! [B_227,A_228] :
      ( k9_relat_1(B_227,A_228) != k1_xboole_0
      | ~ r1_tarski(A_228,k1_relat_1(B_227))
      | k1_xboole_0 = A_228
      | ~ v1_relat_1(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_628,plain,(
    ! [B_227,A_2] :
      ( k9_relat_1(B_227,k1_tarski(A_2)) != k1_xboole_0
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_relat_1(B_227)
      | ~ r2_hidden(A_2,k1_relat_1(B_227)) ) ),
    inference(resolution,[status(thm)],[c_564,c_624])).

tff(c_637,plain,(
    ! [B_229,A_230] :
      ( k9_relat_1(B_229,k1_tarski(A_230)) != k1_xboole_0
      | ~ v1_relat_1(B_229)
      | ~ r2_hidden(A_230,k1_relat_1(B_229)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_628])).

tff(c_654,plain,
    ( k9_relat_1('#skF_11',k1_tarski('#skF_10')) != k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_511,c_637])).

tff(c_665,plain,(
    k9_relat_1('#skF_11',k1_tarski('#skF_10')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_654])).

tff(c_678,plain,
    ( k11_relat_1('#skF_11','#skF_10') != k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_665])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_510,c_678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 2.92/1.45  
% 2.92/1.45  %Foreground sorts:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Background operators:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Foreground operators:
% 2.92/1.45  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.92/1.45  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.45  tff('#skF_11', type, '#skF_11': $i).
% 2.92/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.92/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.45  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.92/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.92/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.92/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.92/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.92/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.45  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.92/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.92/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.92/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.92/1.45  
% 3.06/1.46  tff(f_105, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.06/1.46  tff(f_65, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.06/1.46  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.06/1.46  tff(f_73, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.06/1.46  tff(f_97, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.06/1.46  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.06/1.46  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.06/1.46  tff(f_50, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.06/1.46  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.46  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.06/1.46  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 3.06/1.46  tff(c_54, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.06/1.46  tff(c_56, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | ~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.06/1.46  tff(c_98, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.06/1.46  tff(c_62, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11')) | k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.06/1.46  tff(c_99, plain, (k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 3.06/1.46  tff(c_32, plain, (![A_38]: (r2_hidden('#skF_1'(A_38), A_38) | v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.46  tff(c_200, plain, (![A_131, B_132, C_133]: (r2_hidden(k4_tarski(A_131, B_132), C_133) | ~r2_hidden(B_132, k11_relat_1(C_133, A_131)) | ~v1_relat_1(C_133))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.46  tff(c_36, plain, (![C_71, A_56, D_74]: (r2_hidden(C_71, k1_relat_1(A_56)) | ~r2_hidden(k4_tarski(C_71, D_74), A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.06/1.46  tff(c_214, plain, (![A_134, C_135, B_136]: (r2_hidden(A_134, k1_relat_1(C_135)) | ~r2_hidden(B_136, k11_relat_1(C_135, A_134)) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_200, c_36])).
% 3.06/1.46  tff(c_230, plain, (![A_137, C_138]: (r2_hidden(A_137, k1_relat_1(C_138)) | ~v1_relat_1(C_138) | v1_relat_1(k11_relat_1(C_138, A_137)))), inference(resolution, [status(thm)], [c_32, c_214])).
% 3.06/1.46  tff(c_244, plain, (~v1_relat_1('#skF_11') | v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_230, c_98])).
% 3.06/1.46  tff(c_250, plain, (v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_244])).
% 3.06/1.46  tff(c_52, plain, (![A_80]: (k1_xboole_0=A_80 | r2_hidden(k4_tarski('#skF_8'(A_80), '#skF_9'(A_80)), A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.06/1.46  tff(c_465, plain, (![A_186, C_187]: (r2_hidden(A_186, k1_relat_1(C_187)) | ~v1_relat_1(C_187) | k11_relat_1(C_187, A_186)=k1_xboole_0 | ~v1_relat_1(k11_relat_1(C_187, A_186)))), inference(resolution, [status(thm)], [c_52, c_214])).
% 3.06/1.46  tff(c_494, plain, (~v1_relat_1('#skF_11') | k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | ~v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_465, c_98])).
% 3.06/1.46  tff(c_504, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_250, c_54, c_494])).
% 3.06/1.46  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_504])).
% 3.06/1.46  tff(c_507, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_62])).
% 3.06/1.46  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_507])).
% 3.06/1.46  tff(c_510, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.06/1.46  tff(c_26, plain, (![A_35, B_37]: (k9_relat_1(A_35, k1_tarski(B_37))=k11_relat_1(A_35, B_37) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.46  tff(c_511, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_56])).
% 3.06/1.46  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.46  tff(c_72, plain, (![A_84, B_85]: (k2_xboole_0(k1_tarski(A_84), B_85)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.06/1.46  tff(c_76, plain, (![A_84]: (k1_tarski(A_84)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 3.06/1.46  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.46  tff(c_555, plain, (![A_208, B_209, C_210]: (r1_tarski(k2_tarski(A_208, B_209), C_210) | ~r2_hidden(B_209, C_210) | ~r2_hidden(A_208, C_210))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.46  tff(c_564, plain, (![A_2, C_210]: (r1_tarski(k1_tarski(A_2), C_210) | ~r2_hidden(A_2, C_210) | ~r2_hidden(A_2, C_210))), inference(superposition, [status(thm), theory('equality')], [c_4, c_555])).
% 3.06/1.46  tff(c_624, plain, (![B_227, A_228]: (k9_relat_1(B_227, A_228)!=k1_xboole_0 | ~r1_tarski(A_228, k1_relat_1(B_227)) | k1_xboole_0=A_228 | ~v1_relat_1(B_227))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.46  tff(c_628, plain, (![B_227, A_2]: (k9_relat_1(B_227, k1_tarski(A_2))!=k1_xboole_0 | k1_tarski(A_2)=k1_xboole_0 | ~v1_relat_1(B_227) | ~r2_hidden(A_2, k1_relat_1(B_227)))), inference(resolution, [status(thm)], [c_564, c_624])).
% 3.06/1.46  tff(c_637, plain, (![B_229, A_230]: (k9_relat_1(B_229, k1_tarski(A_230))!=k1_xboole_0 | ~v1_relat_1(B_229) | ~r2_hidden(A_230, k1_relat_1(B_229)))), inference(negUnitSimplification, [status(thm)], [c_76, c_628])).
% 3.06/1.46  tff(c_654, plain, (k9_relat_1('#skF_11', k1_tarski('#skF_10'))!=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_511, c_637])).
% 3.06/1.46  tff(c_665, plain, (k9_relat_1('#skF_11', k1_tarski('#skF_10'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_654])).
% 3.06/1.46  tff(c_678, plain, (k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_26, c_665])).
% 3.06/1.46  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_510, c_678])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 1
% 3.06/1.46  #Sup     : 126
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 2
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 9
% 3.06/1.46  #Demod        : 10
% 3.06/1.46  #Tautology    : 42
% 3.06/1.46  #SimpNegUnit  : 4
% 3.06/1.46  #BackRed      : 0
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.36
% 3.06/1.46  Parsing              : 0.18
% 3.06/1.46  CNF conversion       : 0.03
% 3.06/1.46  Main loop            : 0.34
% 3.06/1.46  Inferencing          : 0.14
% 3.06/1.46  Reduction            : 0.08
% 3.06/1.46  Demodulation         : 0.05
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.06
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.73
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
