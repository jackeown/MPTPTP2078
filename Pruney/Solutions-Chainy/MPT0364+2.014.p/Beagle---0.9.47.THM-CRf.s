%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   74 (  94 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 155 expanded)
%              Number of equality atoms :   26 (  34 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_1752,plain,(
    ! [A_125,B_126] :
      ( r1_tarski(A_125,B_126)
      | k4_xboole_0(A_125,B_126) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_146,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_496,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_512,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_496])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1623,plain,(
    ! [A_118] :
      ( r1_xboole_0(A_118,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_118,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_18])).

tff(c_1631,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1623,c_70])).

tff(c_1639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1631])).

tff(c_1640,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1759,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1752,c_1640])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_1641,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2371,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(A_166,B_167) = k3_subset_1(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2387,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_2371])).

tff(c_12,plain,(
    ! [B_11,A_10,C_12] :
      ( r1_xboole_0(B_11,k4_xboole_0(A_10,C_12))
      | ~ r1_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7549,plain,(
    ! [A_302] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_302,'#skF_5'))
      | ~ r1_xboole_0(A_302,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2387,c_12])).

tff(c_7638,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1641,c_7549])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7660,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7638,c_14])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1970,plain,(
    ! [B_144,A_145] :
      ( r2_hidden(B_144,A_145)
      | ~ m1_subset_1(B_144,A_145)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1977,plain,(
    ! [B_144,A_18] :
      ( r1_tarski(B_144,A_18)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_1970,c_20])).

tff(c_2964,plain,(
    ! [B_191,A_192] :
      ( r1_tarski(B_191,A_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_192)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1977])).

tff(c_2981,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_2964])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2089,plain,(
    ! [A_149,C_150,B_151] :
      ( r1_xboole_0(A_149,C_150)
      | ~ r1_xboole_0(B_151,C_150)
      | ~ r1_tarski(A_149,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4340,plain,(
    ! [A_224,B_225,A_226] :
      ( r1_xboole_0(A_224,B_225)
      | ~ r1_tarski(A_224,A_226)
      | k4_xboole_0(A_226,B_225) != A_226 ) ),
    inference(resolution,[status(thm)],[c_16,c_2089])).

tff(c_4369,plain,(
    ! [B_227] :
      ( r1_xboole_0('#skF_4',B_227)
      | k4_xboole_0('#skF_3',B_227) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2981,c_4340])).

tff(c_4382,plain,(
    ! [B_227] :
      ( k4_xboole_0('#skF_4',B_227) = '#skF_4'
      | k4_xboole_0('#skF_3',B_227) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_4369,c_14])).

tff(c_7778,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7660,c_4382])).

tff(c_1853,plain,(
    ! [A_131,B_132] :
      ( r1_xboole_0(A_131,B_132)
      | k4_xboole_0(A_131,B_132) != A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1861,plain,(
    ! [B_133,A_134] :
      ( r1_xboole_0(B_133,A_134)
      | k4_xboole_0(A_134,B_133) != A_134 ) ),
    inference(resolution,[status(thm)],[c_1853,c_2])).

tff(c_1867,plain,(
    ! [B_133,A_134] :
      ( k4_xboole_0(B_133,A_134) = B_133
      | k4_xboole_0(A_134,B_133) != A_134 ) ),
    inference(resolution,[status(thm)],[c_1861,c_14])).

tff(c_7812,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7778,c_1867])).

tff(c_7894,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_7812])).

tff(c_7896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1759,c_7894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.23  
% 6.34/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.34/2.23  
% 6.34/2.23  %Foreground sorts:
% 6.34/2.23  
% 6.34/2.23  
% 6.34/2.23  %Background operators:
% 6.34/2.23  
% 6.34/2.23  
% 6.34/2.23  %Foreground operators:
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.34/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.34/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.34/2.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.34/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.34/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.34/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.34/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.34/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.34/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.23  
% 6.34/2.24  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.34/2.24  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 6.34/2.24  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.34/2.24  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.34/2.24  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.34/2.24  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 6.34/2.24  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.34/2.24  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.34/2.24  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.34/2.24  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.34/2.24  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.34/2.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.34/2.24  tff(c_1752, plain, (![A_125, B_126]: (r1_tarski(A_125, B_126) | k4_xboole_0(A_125, B_126)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.24  tff(c_48, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.34/2.24  tff(c_70, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.34/2.24  tff(c_54, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.34/2.24  tff(c_146, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_54])).
% 6.34/2.24  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.34/2.24  tff(c_496, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.34/2.24  tff(c_512, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_496])).
% 6.34/2.24  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.34/2.24  tff(c_1623, plain, (![A_118]: (r1_xboole_0(A_118, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_118, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_18])).
% 6.34/2.24  tff(c_1631, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1623, c_70])).
% 6.34/2.24  tff(c_1639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_1631])).
% 6.34/2.24  tff(c_1640, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 6.34/2.24  tff(c_1759, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1752, c_1640])).
% 6.34/2.24  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.24  tff(c_65, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.24  tff(c_69, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_65])).
% 6.34/2.24  tff(c_1641, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 6.34/2.24  tff(c_2371, plain, (![A_166, B_167]: (k4_xboole_0(A_166, B_167)=k3_subset_1(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.34/2.24  tff(c_2387, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_2371])).
% 6.34/2.24  tff(c_12, plain, (![B_11, A_10, C_12]: (r1_xboole_0(B_11, k4_xboole_0(A_10, C_12)) | ~r1_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.24  tff(c_7549, plain, (![A_302]: (r1_xboole_0('#skF_3', k4_xboole_0(A_302, '#skF_5')) | ~r1_xboole_0(A_302, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2387, c_12])).
% 6.34/2.24  tff(c_7638, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1641, c_7549])).
% 6.34/2.24  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.24  tff(c_7660, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_7638, c_14])).
% 6.34/2.24  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.34/2.24  tff(c_42, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.34/2.24  tff(c_1970, plain, (![B_144, A_145]: (r2_hidden(B_144, A_145) | ~m1_subset_1(B_144, A_145) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.34/2.24  tff(c_20, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.34/2.24  tff(c_1977, plain, (![B_144, A_18]: (r1_tarski(B_144, A_18) | ~m1_subset_1(B_144, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_1970, c_20])).
% 6.34/2.24  tff(c_2964, plain, (![B_191, A_192]: (r1_tarski(B_191, A_192) | ~m1_subset_1(B_191, k1_zfmisc_1(A_192)))), inference(negUnitSimplification, [status(thm)], [c_42, c_1977])).
% 6.34/2.24  tff(c_2981, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_2964])).
% 6.34/2.24  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.24  tff(c_2089, plain, (![A_149, C_150, B_151]: (r1_xboole_0(A_149, C_150) | ~r1_xboole_0(B_151, C_150) | ~r1_tarski(A_149, B_151))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.24  tff(c_4340, plain, (![A_224, B_225, A_226]: (r1_xboole_0(A_224, B_225) | ~r1_tarski(A_224, A_226) | k4_xboole_0(A_226, B_225)!=A_226)), inference(resolution, [status(thm)], [c_16, c_2089])).
% 6.34/2.24  tff(c_4369, plain, (![B_227]: (r1_xboole_0('#skF_4', B_227) | k4_xboole_0('#skF_3', B_227)!='#skF_3')), inference(resolution, [status(thm)], [c_2981, c_4340])).
% 6.34/2.24  tff(c_4382, plain, (![B_227]: (k4_xboole_0('#skF_4', B_227)='#skF_4' | k4_xboole_0('#skF_3', B_227)!='#skF_3')), inference(resolution, [status(thm)], [c_4369, c_14])).
% 6.34/2.24  tff(c_7778, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7660, c_4382])).
% 6.34/2.24  tff(c_1853, plain, (![A_131, B_132]: (r1_xboole_0(A_131, B_132) | k4_xboole_0(A_131, B_132)!=A_131)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.24  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.34/2.24  tff(c_1861, plain, (![B_133, A_134]: (r1_xboole_0(B_133, A_134) | k4_xboole_0(A_134, B_133)!=A_134)), inference(resolution, [status(thm)], [c_1853, c_2])).
% 6.34/2.24  tff(c_1867, plain, (![B_133, A_134]: (k4_xboole_0(B_133, A_134)=B_133 | k4_xboole_0(A_134, B_133)!=A_134)), inference(resolution, [status(thm)], [c_1861, c_14])).
% 6.34/2.24  tff(c_7812, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7778, c_1867])).
% 6.34/2.24  tff(c_7894, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_7812])).
% 6.34/2.24  tff(c_7896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1759, c_7894])).
% 6.34/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.24  
% 6.34/2.24  Inference rules
% 6.34/2.24  ----------------------
% 6.34/2.24  #Ref     : 0
% 6.34/2.24  #Sup     : 2071
% 6.34/2.24  #Fact    : 0
% 6.34/2.24  #Define  : 0
% 6.34/2.24  #Split   : 9
% 6.34/2.24  #Chain   : 0
% 6.34/2.24  #Close   : 0
% 6.34/2.24  
% 6.34/2.24  Ordering : KBO
% 6.34/2.24  
% 6.34/2.24  Simplification rules
% 6.34/2.24  ----------------------
% 6.34/2.24  #Subsume      : 399
% 6.34/2.24  #Demod        : 926
% 6.34/2.24  #Tautology    : 997
% 6.34/2.24  #SimpNegUnit  : 58
% 6.34/2.24  #BackRed      : 2
% 6.34/2.24  
% 6.34/2.24  #Partial instantiations: 0
% 6.34/2.24  #Strategies tried      : 1
% 6.34/2.24  
% 6.34/2.24  Timing (in seconds)
% 6.34/2.24  ----------------------
% 6.34/2.25  Preprocessing        : 0.31
% 6.34/2.25  Parsing              : 0.16
% 6.34/2.25  CNF conversion       : 0.02
% 6.34/2.25  Main loop            : 1.17
% 6.34/2.25  Inferencing          : 0.37
% 6.34/2.25  Reduction            : 0.43
% 6.34/2.25  Demodulation         : 0.31
% 6.34/2.25  BG Simplification    : 0.04
% 6.34/2.25  Subsumption          : 0.24
% 6.34/2.25  Abstraction          : 0.05
% 6.34/2.25  MUC search           : 0.00
% 6.34/2.25  Cooper               : 0.00
% 6.34/2.25  Total                : 1.52
% 6.34/2.25  Index Insertion      : 0.00
% 6.34/2.25  Index Deletion       : 0.00
% 6.34/2.25  Index Matching       : 0.00
% 6.34/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
