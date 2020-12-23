%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 130 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 213 expanded)
%              Number of equality atoms :   28 (  48 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_1193,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(A_109,B_110)
      | k4_xboole_0(A_109,B_110) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_78,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_502,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_518,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_502])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1102,plain,(
    ! [A_102] :
      ( r1_xboole_0(A_102,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_102,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_18])).

tff(c_1110,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1102,c_78])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_1110])).

tff(c_1117,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1210,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1193,c_1117])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1139,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = k1_xboole_0
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1143,plain,(
    ! [A_3,B_4] : k4_xboole_0(k4_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1139])).

tff(c_1118,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1731,plain,(
    ! [A_146,B_147] :
      ( k4_xboole_0(A_146,B_147) = k3_subset_1(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1747,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1731])).

tff(c_12,plain,(
    ! [B_11,A_10,C_12] :
      ( r1_xboole_0(B_11,k4_xboole_0(A_10,C_12))
      | ~ r1_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6787,plain,(
    ! [A_291] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_291,'#skF_5'))
      | ~ r1_xboole_0(A_291,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_12])).

tff(c_6872,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1118,c_6787])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6896,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6872,c_14])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1311,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(B_117,A_118)
      | ~ m1_subset_1(B_117,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1315,plain,(
    ! [B_117,A_18] :
      ( r1_tarski(B_117,A_18)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_1311,c_20])).

tff(c_1334,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1315])).

tff(c_1347,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1334])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1486,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_xboole_0(A_132,C_133)
      | ~ r1_xboole_0(B_134,C_133)
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2694,plain,(
    ! [A_181,B_182,A_183] :
      ( r1_xboole_0(A_181,B_182)
      | ~ r1_tarski(A_181,A_183)
      | k4_xboole_0(A_183,B_182) != A_183 ) ),
    inference(resolution,[status(thm)],[c_16,c_1486])).

tff(c_2740,plain,(
    ! [B_186] :
      ( r1_xboole_0('#skF_4',B_186)
      | k4_xboole_0('#skF_3',B_186) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1347,c_2694])).

tff(c_2754,plain,(
    ! [B_186] :
      ( k4_xboole_0('#skF_4',B_186) = '#skF_4'
      | k4_xboole_0('#skF_3',B_186) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2740,c_14])).

tff(c_7020,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6896,c_2754])).

tff(c_1598,plain,(
    ! [B_136,A_137,C_138] :
      ( r1_xboole_0(B_136,k4_xboole_0(A_137,C_138))
      | ~ r1_xboole_0(A_137,k4_xboole_0(B_136,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2053,plain,(
    ! [C_156,A_157,B_158] :
      ( r1_xboole_0(C_156,k4_xboole_0(A_157,B_158))
      | ~ r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_18,c_1598])).

tff(c_2093,plain,(
    ! [C_156,A_3,B_4] :
      ( r1_xboole_0(C_156,k1_xboole_0)
      | ~ r1_tarski(k4_xboole_0(A_3,B_4),A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_2053])).

tff(c_2134,plain,(
    ! [C_161] : r1_xboole_0(C_161,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2093])).

tff(c_2142,plain,(
    ! [C_161] : k4_xboole_0(C_161,k1_xboole_0) = C_161 ),
    inference(resolution,[status(thm)],[c_2134,c_14])).

tff(c_2987,plain,(
    ! [B_193,A_194,C_195] :
      ( r1_xboole_0(B_193,k4_xboole_0(A_194,C_195))
      | k4_xboole_0(A_194,k4_xboole_0(B_193,C_195)) != A_194 ) ),
    inference(resolution,[status(thm)],[c_16,c_1598])).

tff(c_3014,plain,(
    ! [B_193,C_161] :
      ( r1_xboole_0(B_193,C_161)
      | k4_xboole_0(C_161,k4_xboole_0(B_193,k1_xboole_0)) != C_161 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_2987])).

tff(c_3657,plain,(
    ! [B_212,C_213] :
      ( r1_xboole_0(B_212,C_213)
      | k4_xboole_0(C_213,B_212) != C_213 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_3014])).

tff(c_3671,plain,(
    ! [B_212,C_213] :
      ( k4_xboole_0(B_212,C_213) = B_212
      | k4_xboole_0(C_213,B_212) != C_213 ) ),
    inference(resolution,[status(thm)],[c_3657,c_14])).

tff(c_7067,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7020,c_3671])).

tff(c_7161,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_7067])).

tff(c_7163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1210,c_7161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:43:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.24  
% 5.92/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.92/2.25  
% 5.92/2.25  %Foreground sorts:
% 5.92/2.25  
% 5.92/2.25  
% 5.92/2.25  %Background operators:
% 5.92/2.25  
% 5.92/2.25  
% 5.92/2.25  %Foreground operators:
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.92/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.92/2.25  tff('#skF_5', type, '#skF_5': $i).
% 5.92/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.92/2.25  tff('#skF_3', type, '#skF_3': $i).
% 5.92/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.25  tff('#skF_4', type, '#skF_4': $i).
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.92/2.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.25  
% 5.92/2.26  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.92/2.26  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 5.92/2.26  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.92/2.26  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.92/2.26  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.92/2.26  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 5.92/2.26  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.92/2.26  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.92/2.26  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.92/2.26  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.92/2.26  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.92/2.26  tff(c_1193, plain, (![A_109, B_110]: (r1_tarski(A_109, B_110) | k4_xboole_0(A_109, B_110)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.92/2.26  tff(c_48, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.26  tff(c_78, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.92/2.26  tff(c_54, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.26  tff(c_151, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_54])).
% 5.92/2.26  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.26  tff(c_502, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.26  tff(c_518, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_502])).
% 5.92/2.26  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.92/2.26  tff(c_1102, plain, (![A_102]: (r1_xboole_0(A_102, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_102, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_518, c_18])).
% 5.92/2.26  tff(c_1110, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1102, c_78])).
% 5.92/2.26  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_1110])).
% 5.92/2.26  tff(c_1117, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 5.92/2.26  tff(c_1210, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1193, c_1117])).
% 5.92/2.26  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.26  tff(c_1139, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=k1_xboole_0 | ~r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.92/2.26  tff(c_1143, plain, (![A_3, B_4]: (k4_xboole_0(k4_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1139])).
% 5.92/2.26  tff(c_1118, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 5.92/2.26  tff(c_1731, plain, (![A_146, B_147]: (k4_xboole_0(A_146, B_147)=k3_subset_1(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.26  tff(c_1747, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1731])).
% 5.92/2.26  tff(c_12, plain, (![B_11, A_10, C_12]: (r1_xboole_0(B_11, k4_xboole_0(A_10, C_12)) | ~r1_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.26  tff(c_6787, plain, (![A_291]: (r1_xboole_0('#skF_3', k4_xboole_0(A_291, '#skF_5')) | ~r1_xboole_0(A_291, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1747, c_12])).
% 5.92/2.26  tff(c_6872, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1118, c_6787])).
% 5.92/2.26  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.26  tff(c_6896, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_6872, c_14])).
% 5.92/2.26  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.26  tff(c_42, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.92/2.26  tff(c_1311, plain, (![B_117, A_118]: (r2_hidden(B_117, A_118) | ~m1_subset_1(B_117, A_118) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.92/2.26  tff(c_20, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.26  tff(c_1315, plain, (![B_117, A_18]: (r1_tarski(B_117, A_18) | ~m1_subset_1(B_117, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_1311, c_20])).
% 5.92/2.26  tff(c_1334, plain, (![B_120, A_121]: (r1_tarski(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)))), inference(negUnitSimplification, [status(thm)], [c_42, c_1315])).
% 5.92/2.26  tff(c_1347, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1334])).
% 5.92/2.26  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.26  tff(c_1486, plain, (![A_132, C_133, B_134]: (r1_xboole_0(A_132, C_133) | ~r1_xboole_0(B_134, C_133) | ~r1_tarski(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.92/2.26  tff(c_2694, plain, (![A_181, B_182, A_183]: (r1_xboole_0(A_181, B_182) | ~r1_tarski(A_181, A_183) | k4_xboole_0(A_183, B_182)!=A_183)), inference(resolution, [status(thm)], [c_16, c_1486])).
% 5.92/2.26  tff(c_2740, plain, (![B_186]: (r1_xboole_0('#skF_4', B_186) | k4_xboole_0('#skF_3', B_186)!='#skF_3')), inference(resolution, [status(thm)], [c_1347, c_2694])).
% 5.92/2.26  tff(c_2754, plain, (![B_186]: (k4_xboole_0('#skF_4', B_186)='#skF_4' | k4_xboole_0('#skF_3', B_186)!='#skF_3')), inference(resolution, [status(thm)], [c_2740, c_14])).
% 5.92/2.26  tff(c_7020, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6896, c_2754])).
% 5.92/2.26  tff(c_1598, plain, (![B_136, A_137, C_138]: (r1_xboole_0(B_136, k4_xboole_0(A_137, C_138)) | ~r1_xboole_0(A_137, k4_xboole_0(B_136, C_138)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.26  tff(c_2053, plain, (![C_156, A_157, B_158]: (r1_xboole_0(C_156, k4_xboole_0(A_157, B_158)) | ~r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_18, c_1598])).
% 5.92/2.26  tff(c_2093, plain, (![C_156, A_3, B_4]: (r1_xboole_0(C_156, k1_xboole_0) | ~r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_2053])).
% 5.92/2.26  tff(c_2134, plain, (![C_161]: (r1_xboole_0(C_161, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2093])).
% 5.92/2.26  tff(c_2142, plain, (![C_161]: (k4_xboole_0(C_161, k1_xboole_0)=C_161)), inference(resolution, [status(thm)], [c_2134, c_14])).
% 5.92/2.26  tff(c_2987, plain, (![B_193, A_194, C_195]: (r1_xboole_0(B_193, k4_xboole_0(A_194, C_195)) | k4_xboole_0(A_194, k4_xboole_0(B_193, C_195))!=A_194)), inference(resolution, [status(thm)], [c_16, c_1598])).
% 5.92/2.26  tff(c_3014, plain, (![B_193, C_161]: (r1_xboole_0(B_193, C_161) | k4_xboole_0(C_161, k4_xboole_0(B_193, k1_xboole_0))!=C_161)), inference(superposition, [status(thm), theory('equality')], [c_2142, c_2987])).
% 5.92/2.26  tff(c_3657, plain, (![B_212, C_213]: (r1_xboole_0(B_212, C_213) | k4_xboole_0(C_213, B_212)!=C_213)), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_3014])).
% 5.92/2.26  tff(c_3671, plain, (![B_212, C_213]: (k4_xboole_0(B_212, C_213)=B_212 | k4_xboole_0(C_213, B_212)!=C_213)), inference(resolution, [status(thm)], [c_3657, c_14])).
% 5.92/2.26  tff(c_7067, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7020, c_3671])).
% 5.92/2.26  tff(c_7161, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_7067])).
% 5.92/2.26  tff(c_7163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1210, c_7161])).
% 5.92/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.26  
% 5.92/2.26  Inference rules
% 5.92/2.26  ----------------------
% 5.92/2.26  #Ref     : 0
% 5.92/2.26  #Sup     : 1843
% 5.92/2.26  #Fact    : 0
% 5.92/2.26  #Define  : 0
% 5.92/2.26  #Split   : 18
% 5.92/2.26  #Chain   : 0
% 5.92/2.26  #Close   : 0
% 5.92/2.26  
% 5.92/2.26  Ordering : KBO
% 5.92/2.26  
% 5.92/2.26  Simplification rules
% 5.92/2.26  ----------------------
% 5.92/2.26  #Subsume      : 452
% 5.92/2.26  #Demod        : 718
% 5.92/2.26  #Tautology    : 750
% 5.92/2.26  #SimpNegUnit  : 79
% 5.92/2.26  #BackRed      : 3
% 5.92/2.26  
% 5.92/2.26  #Partial instantiations: 0
% 5.92/2.26  #Strategies tried      : 1
% 5.92/2.26  
% 5.92/2.26  Timing (in seconds)
% 5.92/2.26  ----------------------
% 5.92/2.26  Preprocessing        : 0.31
% 5.92/2.26  Parsing              : 0.17
% 5.92/2.26  CNF conversion       : 0.02
% 5.92/2.26  Main loop            : 1.12
% 5.92/2.26  Inferencing          : 0.36
% 5.92/2.26  Reduction            : 0.38
% 5.92/2.26  Demodulation         : 0.26
% 5.92/2.26  BG Simplification    : 0.04
% 5.92/2.26  Subsumption          : 0.25
% 5.92/2.26  Abstraction          : 0.05
% 5.92/2.26  MUC search           : 0.00
% 5.92/2.26  Cooper               : 0.00
% 5.92/2.26  Total                : 1.46
% 5.92/2.26  Index Insertion      : 0.00
% 5.92/2.27  Index Deletion       : 0.00
% 5.92/2.27  Index Matching       : 0.00
% 5.92/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
