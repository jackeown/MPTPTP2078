%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 127 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 187 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_920,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,B_111) = k3_subset_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_933,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_920])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [B_42] : k4_xboole_0(B_42,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_18,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [B_42] : r1_xboole_0(k1_xboole_0,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_18])).

tff(c_142,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_142])).

tff(c_119,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_44,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_99,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50])).

tff(c_370,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_380,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_370])).

tff(c_384,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_380])).

tff(c_191,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_161,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_60])).

tff(c_198,plain,(
    k4_xboole_0(k3_subset_1('#skF_4','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_161])).

tff(c_385,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_198])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_385])).

tff(c_390,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_407,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_418,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_390,c_407])).

tff(c_449,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = A_83
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_466,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_18,c_449])).

tff(c_944,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_466])).

tff(c_956,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_418,c_944])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_391,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_48,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_583,plain,(
    ! [B_90,A_91] :
      ( r2_hidden(B_90,A_91)
      | ~ m1_subset_1(B_90,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_587,plain,(
    ! [B_90,A_13] :
      ( r1_tarski(B_90,A_13)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_583,c_24])).

tff(c_628,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_587])).

tff(c_637,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_628])).

tff(c_666,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_668,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_637,c_666])).

tff(c_677,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_668])).

tff(c_687,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_677])).

tff(c_934,plain,(
    k3_subset_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_687])).

tff(c_1033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.44  
% 2.84/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.84/1.44  
% 2.84/1.44  %Foreground sorts:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Background operators:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Foreground operators:
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.84/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.84/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.44  
% 2.84/1.45  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.84/1.45  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.84/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.84/1.45  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.84/1.45  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.84/1.45  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.84/1.45  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.84/1.45  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.84/1.45  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.84/1.45  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.84/1.45  tff(c_920, plain, (![A_110, B_111]: (k4_xboole_0(A_110, B_111)=k3_subset_1(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.45  tff(c_933, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_920])).
% 2.84/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.45  tff(c_115, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_121, plain, (![B_42]: (k4_xboole_0(B_42, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.84/1.45  tff(c_18, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.45  tff(c_126, plain, (![B_42]: (r1_xboole_0(k1_xboole_0, B_42))), inference(superposition, [status(thm), theory('equality')], [c_121, c_18])).
% 2.84/1.45  tff(c_142, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.45  tff(c_155, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_142])).
% 2.84/1.45  tff(c_119, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.84/1.45  tff(c_44, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.84/1.45  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.84/1.45  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 2.84/1.45  tff(c_99, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_59])).
% 2.84/1.45  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_50])).
% 2.84/1.45  tff(c_370, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.45  tff(c_380, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_100, c_370])).
% 2.84/1.45  tff(c_384, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_380])).
% 2.84/1.45  tff(c_191, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.84/1.45  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 2.84/1.45  tff(c_161, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_60])).
% 2.84/1.45  tff(c_198, plain, (k4_xboole_0(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_191, c_161])).
% 2.84/1.45  tff(c_385, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_384, c_198])).
% 2.84/1.45  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_385])).
% 2.84/1.45  tff(c_390, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_59])).
% 2.84/1.45  tff(c_407, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_418, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_390, c_407])).
% 2.84/1.45  tff(c_449, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=A_83 | ~r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.45  tff(c_466, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_18, c_449])).
% 2.84/1.45  tff(c_944, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_933, c_466])).
% 2.84/1.45  tff(c_956, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_933, c_418, c_944])).
% 2.84/1.45  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_391, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 2.84/1.45  tff(c_48, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.45  tff(c_583, plain, (![B_90, A_91]: (r2_hidden(B_90, A_91) | ~m1_subset_1(B_90, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.45  tff(c_24, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.45  tff(c_587, plain, (![B_90, A_13]: (r1_tarski(B_90, A_13) | ~m1_subset_1(B_90, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_583, c_24])).
% 2.84/1.45  tff(c_628, plain, (![B_94, A_95]: (r1_tarski(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)))), inference(negUnitSimplification, [status(thm)], [c_48, c_587])).
% 2.84/1.45  tff(c_637, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_628])).
% 2.84/1.45  tff(c_666, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.45  tff(c_668, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_637, c_666])).
% 2.84/1.45  tff(c_677, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_391, c_668])).
% 2.84/1.45  tff(c_687, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_677])).
% 2.84/1.45  tff(c_934, plain, (k3_subset_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_933, c_687])).
% 2.84/1.45  tff(c_1033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_956, c_934])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 229
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 2
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 14
% 2.84/1.45  #Demod        : 137
% 2.84/1.45  #Tautology    : 165
% 2.84/1.45  #SimpNegUnit  : 8
% 2.84/1.45  #BackRed      : 10
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.46  Preprocessing        : 0.33
% 2.84/1.46  Parsing              : 0.17
% 2.84/1.46  CNF conversion       : 0.02
% 2.84/1.46  Main loop            : 0.34
% 2.84/1.46  Inferencing          : 0.13
% 2.84/1.46  Reduction            : 0.11
% 2.84/1.46  Demodulation         : 0.08
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.06
% 2.84/1.46  Abstraction          : 0.02
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.46  Total                : 0.70
% 2.84/1.46  Index Insertion      : 0.00
% 2.84/1.46  Index Deletion       : 0.00
% 2.84/1.46  Index Matching       : 0.00
% 2.84/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
