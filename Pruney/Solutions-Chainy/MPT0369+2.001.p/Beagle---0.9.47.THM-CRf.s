%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 137 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :   99 ( 240 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_85,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_237,plain,(
    ! [B_49,A_50] :
      ( v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_245,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_237])).

tff(c_246,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_50,plain,(
    ! [B_29,A_28] :
      ( r2_hidden(B_29,A_28)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_670,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_683,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_670])).

tff(c_28,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_771,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_303,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,A_65)
      | ~ m1_subset_1(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [C_27,A_23] :
      ( r1_tarski(C_27,A_23)
      | ~ r2_hidden(C_27,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_310,plain,(
    ! [B_64,A_23] :
      ( r1_tarski(B_64,A_23)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_303,c_36])).

tff(c_329,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_310])).

tff(c_342,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_329])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_346,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_342,c_22])).

tff(c_452,plain,(
    ! [A_74,B_75] : k5_xboole_0(k5_xboole_0(A_74,B_75),k2_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_482,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_452])).

tff(c_784,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_3','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_482])).

tff(c_886,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_784])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_258,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_275,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_900,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_275])).

tff(c_906,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_900])).

tff(c_1487,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_906])).

tff(c_896,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_482])).

tff(c_1166,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden(A_92,B_93)
      | ~ r2_hidden(A_92,C_94)
      | r2_hidden(A_92,k5_xboole_0(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1178,plain,(
    ! [A_92] :
      ( r2_hidden(A_92,k5_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(A_92,'#skF_3')
      | r2_hidden(A_92,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_1166])).

tff(c_3166,plain,(
    ! [A_137] :
      ( r2_hidden(A_137,k3_subset_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_137,'#skF_3')
      | r2_hidden(A_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1178])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3175,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3166,c_60])).

tff(c_3182,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3175])).

tff(c_3185,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3182])).

tff(c_3188,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3185])).

tff(c_3190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_3188])).

tff(c_3192,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3199,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3192,c_6])).

tff(c_3203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.77  
% 3.91/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.77  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.23/1.77  
% 4.23/1.77  %Foreground sorts:
% 4.23/1.77  
% 4.23/1.77  
% 4.23/1.77  %Background operators:
% 4.23/1.77  
% 4.23/1.77  
% 4.23/1.77  %Foreground operators:
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.77  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.23/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.23/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.23/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.77  
% 4.27/1.78  tff(f_100, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 4.27/1.78  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.27/1.78  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.27/1.78  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.27/1.78  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.27/1.78  tff(f_56, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.27/1.78  tff(f_54, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.27/1.78  tff(f_85, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.27/1.78  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.27/1.78  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.27/1.78  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.27/1.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.27/1.78  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.27/1.78  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.27/1.78  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.27/1.78  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.78  tff(c_64, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.78  tff(c_237, plain, (![B_49, A_50]: (v1_xboole_0(B_49) | ~m1_subset_1(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.78  tff(c_245, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_237])).
% 4.27/1.78  tff(c_246, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_245])).
% 4.27/1.78  tff(c_50, plain, (![B_29, A_28]: (r2_hidden(B_29, A_28) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.78  tff(c_62, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.78  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.27/1.78  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.78  tff(c_670, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.27/1.78  tff(c_683, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_670])).
% 4.27/1.78  tff(c_28, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.27/1.78  tff(c_32, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.27/1.78  tff(c_771, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.27/1.78  tff(c_58, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.27/1.78  tff(c_303, plain, (![B_64, A_65]: (r2_hidden(B_64, A_65) | ~m1_subset_1(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.78  tff(c_36, plain, (![C_27, A_23]: (r1_tarski(C_27, A_23) | ~r2_hidden(C_27, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.27/1.78  tff(c_310, plain, (![B_64, A_23]: (r1_tarski(B_64, A_23) | ~m1_subset_1(B_64, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_303, c_36])).
% 4.27/1.78  tff(c_329, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_58, c_310])).
% 4.27/1.78  tff(c_342, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_329])).
% 4.27/1.78  tff(c_22, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.27/1.78  tff(c_346, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_342, c_22])).
% 4.27/1.78  tff(c_452, plain, (![A_74, B_75]: (k5_xboole_0(k5_xboole_0(A_74, B_75), k2_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.27/1.78  tff(c_482, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_346, c_452])).
% 4.27/1.78  tff(c_784, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_3', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_771, c_482])).
% 4.27/1.78  tff(c_886, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_784])).
% 4.27/1.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.27/1.78  tff(c_258, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.78  tff(c_275, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_258])).
% 4.27/1.78  tff(c_900, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_886, c_275])).
% 4.27/1.78  tff(c_906, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_683, c_900])).
% 4.27/1.78  tff(c_1487, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_906])).
% 4.27/1.78  tff(c_896, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_886, c_482])).
% 4.27/1.78  tff(c_1166, plain, (![A_92, B_93, C_94]: (r2_hidden(A_92, B_93) | ~r2_hidden(A_92, C_94) | r2_hidden(A_92, k5_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.27/1.78  tff(c_1178, plain, (![A_92]: (r2_hidden(A_92, k5_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(A_92, '#skF_3') | r2_hidden(A_92, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_896, c_1166])).
% 4.27/1.78  tff(c_3166, plain, (![A_137]: (r2_hidden(A_137, k3_subset_1('#skF_3', '#skF_4')) | ~r2_hidden(A_137, '#skF_3') | r2_hidden(A_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1178])).
% 4.27/1.78  tff(c_60, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.78  tff(c_3175, plain, (~r2_hidden('#skF_5', '#skF_3') | r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3166, c_60])).
% 4.27/1.78  tff(c_3182, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_3175])).
% 4.27/1.78  tff(c_3185, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3182])).
% 4.27/1.78  tff(c_3188, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3185])).
% 4.27/1.78  tff(c_3190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_3188])).
% 4.27/1.78  tff(c_3192, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_245])).
% 4.27/1.78  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.27/1.78  tff(c_3199, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3192, c_6])).
% 4.27/1.78  tff(c_3203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3199])).
% 4.27/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.78  
% 4.27/1.78  Inference rules
% 4.27/1.78  ----------------------
% 4.27/1.78  #Ref     : 0
% 4.27/1.78  #Sup     : 813
% 4.27/1.78  #Fact    : 0
% 4.27/1.78  #Define  : 0
% 4.27/1.78  #Split   : 5
% 4.27/1.78  #Chain   : 0
% 4.27/1.78  #Close   : 0
% 4.27/1.78  
% 4.27/1.78  Ordering : KBO
% 4.27/1.78  
% 4.27/1.78  Simplification rules
% 4.27/1.78  ----------------------
% 4.27/1.78  #Subsume      : 14
% 4.27/1.78  #Demod        : 491
% 4.27/1.78  #Tautology    : 464
% 4.27/1.78  #SimpNegUnit  : 6
% 4.27/1.78  #BackRed      : 5
% 4.27/1.78  
% 4.27/1.78  #Partial instantiations: 0
% 4.27/1.78  #Strategies tried      : 1
% 4.27/1.78  
% 4.27/1.78  Timing (in seconds)
% 4.27/1.78  ----------------------
% 4.27/1.79  Preprocessing        : 0.32
% 4.27/1.79  Parsing              : 0.17
% 4.27/1.79  CNF conversion       : 0.02
% 4.27/1.79  Main loop            : 0.66
% 4.27/1.79  Inferencing          : 0.22
% 4.27/1.79  Reduction            : 0.27
% 4.27/1.79  Demodulation         : 0.21
% 4.27/1.79  BG Simplification    : 0.03
% 4.27/1.79  Subsumption          : 0.10
% 4.27/1.79  Abstraction          : 0.03
% 4.27/1.79  MUC search           : 0.00
% 4.27/1.79  Cooper               : 0.00
% 4.27/1.79  Total                : 1.02
% 4.27/1.79  Index Insertion      : 0.00
% 4.27/1.79  Index Deletion       : 0.00
% 4.27/1.79  Index Matching       : 0.00
% 4.27/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
