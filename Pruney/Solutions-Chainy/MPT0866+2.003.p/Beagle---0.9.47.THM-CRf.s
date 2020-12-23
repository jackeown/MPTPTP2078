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
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 394 expanded)
%              Number of leaves         :   29 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 878 expanded)
%              Number of equality atoms :   31 ( 288 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,(
    ! [B_55,A_56] :
      ( v1_xboole_0(B_55)
      | ~ m1_subset_1(B_55,A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_50,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_48,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_43,B_44] : v1_relat_1(k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(B_42,A_41)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [A_66,B_67] :
      ( k4_tarski(k1_mcart_1(A_66),k2_mcart_1(A_66)) = A_66
      | ~ r2_hidden(A_66,B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8884,plain,(
    ! [B_418,A_419] :
      ( k4_tarski(k1_mcart_1(B_418),k2_mcart_1(B_418)) = B_418
      | ~ v1_relat_1(A_419)
      | ~ m1_subset_1(B_418,A_419)
      | v1_xboole_0(A_419) ) ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_8894,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9'))
    | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_50,c_8884])).

tff(c_8901,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8894])).

tff(c_8903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_48,c_8901])).

tff(c_8904,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_32,plain,(
    ! [A_39] : k2_zfmisc_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9118,plain,(
    ! [A_452,B_453,C_454] :
      ( r2_hidden('#skF_4'(A_452,B_453,C_454),B_453)
      | r2_hidden('#skF_5'(A_452,B_453,C_454),C_454)
      | k2_zfmisc_1(A_452,B_453) = C_454 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [B_40] : k2_zfmisc_1(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8968,plain,(
    ! [A_435,B_436,D_437] :
      ( r2_hidden('#skF_7'(A_435,B_436,k2_zfmisc_1(A_435,B_436),D_437),B_436)
      | ~ r2_hidden(D_437,k2_zfmisc_1(A_435,B_436)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8988,plain,(
    ! [B_438,D_439,A_440] :
      ( ~ v1_xboole_0(B_438)
      | ~ r2_hidden(D_439,k2_zfmisc_1(A_440,B_438)) ) ),
    inference(resolution,[status(thm)],[c_8968,c_2])).

tff(c_9009,plain,(
    ! [B_40,D_439] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_hidden(D_439,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8988])).

tff(c_9014,plain,(
    ! [D_439] : ~ r2_hidden(D_439,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9009])).

tff(c_9126,plain,(
    ! [A_452,C_454] :
      ( r2_hidden('#skF_5'(A_452,k1_xboole_0,C_454),C_454)
      | k2_zfmisc_1(A_452,k1_xboole_0) = C_454 ) ),
    inference(resolution,[status(thm)],[c_9118,c_9014])).

tff(c_9169,plain,(
    ! [A_455,C_456] :
      ( r2_hidden('#skF_5'(A_455,k1_xboole_0,C_456),C_456)
      | k1_xboole_0 = C_456 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9126])).

tff(c_9197,plain,(
    ! [C_457] :
      ( ~ v1_xboole_0(C_457)
      | k1_xboole_0 = C_457 ) ),
    inference(resolution,[status(thm)],[c_9169,c_2])).

tff(c_9218,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8904,c_9197])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9227,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9228,plain,(
    '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_54])).

tff(c_9222,plain,(
    ! [D_439] : ~ r2_hidden(D_439,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_9014])).

tff(c_8905,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_9217,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8905,c_9197])).

tff(c_9372,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_9217])).

tff(c_6,plain,(
    ! [E_37,F_38,A_5,B_6] :
      ( r2_hidden(k4_tarski(E_37,F_38),k2_zfmisc_1(A_5,B_6))
      | ~ r2_hidden(F_38,B_6)
      | ~ r2_hidden(E_37,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9397,plain,(
    ! [E_37,F_38] :
      ( r2_hidden(k4_tarski(E_37,F_38),'#skF_10')
      | ~ r2_hidden(F_38,'#skF_9')
      | ~ r2_hidden(E_37,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9372,c_6])).

tff(c_9406,plain,(
    ! [F_38,E_37] :
      ( ~ r2_hidden(F_38,'#skF_9')
      | ~ r2_hidden(E_37,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9222,c_9397])).

tff(c_9520,plain,(
    ! [E_472] : ~ r2_hidden(E_472,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9406])).

tff(c_9559,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_9520])).

tff(c_9196,plain,(
    ! [C_456] :
      ( ~ v1_xboole_0(C_456)
      | k1_xboole_0 = C_456 ) ),
    inference(resolution,[status(thm)],[c_9169,c_2])).

tff(c_9219,plain,(
    ! [C_456] :
      ( ~ v1_xboole_0(C_456)
      | C_456 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_9196])).

tff(c_9566,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9559,c_9219])).

tff(c_9572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9228,c_9566])).

tff(c_9574,plain,(
    ! [F_473] : ~ r2_hidden(F_473,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_9406])).

tff(c_9613,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_9574])).

tff(c_9620,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9613,c_9219])).

tff(c_9626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9227,c_9620])).

tff(c_9627,plain,(
    ! [B_40] : ~ v1_xboole_0(B_40) ),
    inference(splitRight,[status(thm)],[c_9009])).

tff(c_9635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9627,c_8905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.66/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.37  
% 6.66/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.38  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 6.66/2.38  
% 6.66/2.38  %Foreground sorts:
% 6.66/2.38  
% 6.66/2.38  
% 6.66/2.38  %Background operators:
% 6.66/2.38  
% 6.66/2.38  
% 6.66/2.38  %Foreground operators:
% 6.66/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.66/2.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.66/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.66/2.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.66/2.38  tff('#skF_10', type, '#skF_10': $i).
% 6.66/2.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.66/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.66/2.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.66/2.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.66/2.38  tff('#skF_9', type, '#skF_9': $i).
% 6.66/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.66/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.66/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.66/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.66/2.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.66/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.66/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.66/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.38  
% 6.66/2.39  tff(f_84, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 6.66/2.39  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.66/2.39  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.66/2.39  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 6.66/2.39  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.66/2.39  tff(f_43, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.66/2.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.66/2.39  tff(c_50, plain, (m1_subset_1('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.66/2.39  tff(c_89, plain, (![B_55, A_56]: (v1_xboole_0(B_55) | ~m1_subset_1(B_55, A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.66/2.39  tff(c_93, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_89])).
% 6.66/2.39  tff(c_94, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_93])).
% 6.66/2.39  tff(c_48, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.66/2.39  tff(c_44, plain, (![A_43, B_44]: (v1_relat_1(k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.66/2.39  tff(c_38, plain, (![B_42, A_41]: (r2_hidden(B_42, A_41) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.66/2.39  tff(c_130, plain, (![A_66, B_67]: (k4_tarski(k1_mcart_1(A_66), k2_mcart_1(A_66))=A_66 | ~r2_hidden(A_66, B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.66/2.39  tff(c_8884, plain, (![B_418, A_419]: (k4_tarski(k1_mcart_1(B_418), k2_mcart_1(B_418))=B_418 | ~v1_relat_1(A_419) | ~m1_subset_1(B_418, A_419) | v1_xboole_0(A_419))), inference(resolution, [status(thm)], [c_38, c_130])).
% 6.66/2.39  tff(c_8894, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9')) | v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_8884])).
% 6.66/2.39  tff(c_8901, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8894])).
% 6.66/2.39  tff(c_8903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_48, c_8901])).
% 6.66/2.39  tff(c_8904, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_93])).
% 6.66/2.39  tff(c_32, plain, (![A_39]: (k2_zfmisc_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.39  tff(c_9118, plain, (![A_452, B_453, C_454]: (r2_hidden('#skF_4'(A_452, B_453, C_454), B_453) | r2_hidden('#skF_5'(A_452, B_453, C_454), C_454) | k2_zfmisc_1(A_452, B_453)=C_454)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.66/2.39  tff(c_34, plain, (![B_40]: (k2_zfmisc_1(k1_xboole_0, B_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.39  tff(c_8968, plain, (![A_435, B_436, D_437]: (r2_hidden('#skF_7'(A_435, B_436, k2_zfmisc_1(A_435, B_436), D_437), B_436) | ~r2_hidden(D_437, k2_zfmisc_1(A_435, B_436)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.66/2.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.66/2.39  tff(c_8988, plain, (![B_438, D_439, A_440]: (~v1_xboole_0(B_438) | ~r2_hidden(D_439, k2_zfmisc_1(A_440, B_438)))), inference(resolution, [status(thm)], [c_8968, c_2])).
% 6.66/2.39  tff(c_9009, plain, (![B_40, D_439]: (~v1_xboole_0(B_40) | ~r2_hidden(D_439, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_8988])).
% 6.66/2.39  tff(c_9014, plain, (![D_439]: (~r2_hidden(D_439, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_9009])).
% 6.66/2.39  tff(c_9126, plain, (![A_452, C_454]: (r2_hidden('#skF_5'(A_452, k1_xboole_0, C_454), C_454) | k2_zfmisc_1(A_452, k1_xboole_0)=C_454)), inference(resolution, [status(thm)], [c_9118, c_9014])).
% 6.66/2.39  tff(c_9169, plain, (![A_455, C_456]: (r2_hidden('#skF_5'(A_455, k1_xboole_0, C_456), C_456) | k1_xboole_0=C_456)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9126])).
% 6.66/2.39  tff(c_9197, plain, (![C_457]: (~v1_xboole_0(C_457) | k1_xboole_0=C_457)), inference(resolution, [status(thm)], [c_9169, c_2])).
% 6.66/2.39  tff(c_9218, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_8904, c_9197])).
% 6.66/2.39  tff(c_52, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.66/2.39  tff(c_9227, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_52])).
% 6.66/2.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.66/2.39  tff(c_54, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.66/2.39  tff(c_9228, plain, ('#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_54])).
% 6.66/2.39  tff(c_9222, plain, (![D_439]: (~r2_hidden(D_439, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_9014])).
% 6.66/2.39  tff(c_8905, plain, (v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_93])).
% 6.66/2.39  tff(c_9217, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_8905, c_9197])).
% 6.66/2.39  tff(c_9372, plain, (k2_zfmisc_1('#skF_8', '#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_9217])).
% 6.66/2.39  tff(c_6, plain, (![E_37, F_38, A_5, B_6]: (r2_hidden(k4_tarski(E_37, F_38), k2_zfmisc_1(A_5, B_6)) | ~r2_hidden(F_38, B_6) | ~r2_hidden(E_37, A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.66/2.39  tff(c_9397, plain, (![E_37, F_38]: (r2_hidden(k4_tarski(E_37, F_38), '#skF_10') | ~r2_hidden(F_38, '#skF_9') | ~r2_hidden(E_37, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9372, c_6])).
% 6.66/2.39  tff(c_9406, plain, (![F_38, E_37]: (~r2_hidden(F_38, '#skF_9') | ~r2_hidden(E_37, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_9222, c_9397])).
% 6.66/2.39  tff(c_9520, plain, (![E_472]: (~r2_hidden(E_472, '#skF_8'))), inference(splitLeft, [status(thm)], [c_9406])).
% 6.66/2.39  tff(c_9559, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_9520])).
% 6.66/2.39  tff(c_9196, plain, (![C_456]: (~v1_xboole_0(C_456) | k1_xboole_0=C_456)), inference(resolution, [status(thm)], [c_9169, c_2])).
% 6.66/2.39  tff(c_9219, plain, (![C_456]: (~v1_xboole_0(C_456) | C_456='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_9196])).
% 6.66/2.39  tff(c_9566, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_9559, c_9219])).
% 6.66/2.39  tff(c_9572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9228, c_9566])).
% 6.66/2.39  tff(c_9574, plain, (![F_473]: (~r2_hidden(F_473, '#skF_9'))), inference(splitRight, [status(thm)], [c_9406])).
% 6.66/2.39  tff(c_9613, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_9574])).
% 6.66/2.39  tff(c_9620, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_9613, c_9219])).
% 6.66/2.39  tff(c_9626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9227, c_9620])).
% 6.66/2.39  tff(c_9627, plain, (![B_40]: (~v1_xboole_0(B_40))), inference(splitRight, [status(thm)], [c_9009])).
% 6.66/2.39  tff(c_9635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9627, c_8905])).
% 6.66/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.39  
% 6.66/2.39  Inference rules
% 6.66/2.39  ----------------------
% 6.66/2.39  #Ref     : 0
% 6.66/2.39  #Sup     : 2440
% 6.66/2.39  #Fact    : 0
% 6.66/2.39  #Define  : 0
% 6.66/2.39  #Split   : 4
% 6.66/2.39  #Chain   : 0
% 6.66/2.39  #Close   : 0
% 6.66/2.39  
% 6.66/2.39  Ordering : KBO
% 6.66/2.39  
% 6.66/2.39  Simplification rules
% 6.66/2.39  ----------------------
% 6.66/2.39  #Subsume      : 669
% 6.66/2.39  #Demod        : 1806
% 6.66/2.39  #Tautology    : 1008
% 6.66/2.39  #SimpNegUnit  : 34
% 6.66/2.39  #BackRed      : 18
% 6.66/2.39  
% 6.66/2.39  #Partial instantiations: 0
% 6.66/2.39  #Strategies tried      : 1
% 6.66/2.39  
% 6.66/2.39  Timing (in seconds)
% 6.66/2.39  ----------------------
% 6.66/2.39  Preprocessing        : 0.32
% 6.66/2.39  Parsing              : 0.17
% 6.66/2.39  CNF conversion       : 0.03
% 6.66/2.39  Main loop            : 1.26
% 6.66/2.39  Inferencing          : 0.40
% 6.66/2.39  Reduction            : 0.31
% 6.66/2.39  Demodulation         : 0.22
% 6.66/2.39  BG Simplification    : 0.05
% 6.66/2.39  Subsumption          : 0.40
% 6.66/2.39  Abstraction          : 0.08
% 6.66/2.39  MUC search           : 0.00
% 6.66/2.39  Cooper               : 0.00
% 6.66/2.39  Total                : 1.62
% 6.66/2.39  Index Insertion      : 0.00
% 6.66/2.39  Index Deletion       : 0.00
% 6.66/2.39  Index Matching       : 0.00
% 6.66/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
