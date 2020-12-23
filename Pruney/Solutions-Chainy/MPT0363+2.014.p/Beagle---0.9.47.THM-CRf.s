%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 124 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_553,plain,(
    ! [B_118,A_119] :
      ( r2_hidden(B_118,A_119)
      | ~ m1_subset_1(B_118,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_557,plain,(
    ! [B_118,A_15] :
      ( r1_tarski(B_118,A_15)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_553,c_18])).

tff(c_561,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_557])).

tff(c_574,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_561])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_134,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_377,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_393,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_377])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | ~ r1_xboole_0(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_11,A_10] : r1_xboole_0(B_11,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_14,c_55])).

tff(c_398,plain,(
    r1_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_58])).

tff(c_85,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_85])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_xboole_0(A_7,B_8)
      | ~ r1_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_472,plain,(
    ! [A_102] :
      ( r1_xboole_0(A_102,'#skF_4')
      | ~ r1_xboole_0(A_102,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_488,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_398,c_472])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_494,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_488,c_2])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_494])).

tff(c_499,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_674,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,B_133) = k3_subset_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_686,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_674])).

tff(c_732,plain,(
    ! [A_136,B_137,C_138] :
      ( r1_tarski(A_136,k4_xboole_0(B_137,C_138))
      | ~ r1_xboole_0(A_136,C_138)
      | ~ r1_tarski(A_136,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_788,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_144,'#skF_5')
      | ~ r1_tarski(A_144,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_732])).

tff(c_500,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_794,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_788,c_500])).

tff(c_799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_499,c_794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.44  
% 2.73/1.45  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.73/1.45  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.73/1.45  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.73/1.45  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.73/1.45  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.73/1.45  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.73/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.73/1.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.73/1.45  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.73/1.45  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.73/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.73/1.45  tff(c_40, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.45  tff(c_553, plain, (![B_118, A_119]: (r2_hidden(B_118, A_119) | ~m1_subset_1(B_118, A_119) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.73/1.45  tff(c_18, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.45  tff(c_557, plain, (![B_118, A_15]: (r1_tarski(B_118, A_15) | ~m1_subset_1(B_118, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_553, c_18])).
% 2.73/1.45  tff(c_561, plain, (![B_120, A_121]: (r1_tarski(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)))), inference(negUnitSimplification, [status(thm)], [c_40, c_557])).
% 2.73/1.45  tff(c_574, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_561])).
% 2.73/1.45  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.73/1.45  tff(c_71, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.73/1.45  tff(c_46, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.73/1.45  tff(c_134, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46])).
% 2.73/1.45  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.73/1.45  tff(c_377, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.45  tff(c_393, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_377])).
% 2.73/1.45  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.45  tff(c_55, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | ~r1_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.45  tff(c_58, plain, (![B_11, A_10]: (r1_xboole_0(B_11, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_14, c_55])).
% 2.73/1.45  tff(c_398, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_58])).
% 2.73/1.45  tff(c_85, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.45  tff(c_89, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_71, c_85])).
% 2.73/1.45  tff(c_12, plain, (![A_7, B_8, C_9]: (r1_xboole_0(A_7, B_8) | ~r1_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.45  tff(c_472, plain, (![A_102]: (r1_xboole_0(A_102, '#skF_4') | ~r1_xboole_0(A_102, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 2.73/1.45  tff(c_488, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_398, c_472])).
% 2.73/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.45  tff(c_494, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_488, c_2])).
% 2.73/1.45  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_494])).
% 2.73/1.45  tff(c_499, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.73/1.45  tff(c_674, plain, (![A_132, B_133]: (k4_xboole_0(A_132, B_133)=k3_subset_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.45  tff(c_686, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_674])).
% 2.73/1.45  tff(c_732, plain, (![A_136, B_137, C_138]: (r1_tarski(A_136, k4_xboole_0(B_137, C_138)) | ~r1_xboole_0(A_136, C_138) | ~r1_tarski(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.45  tff(c_788, plain, (![A_144]: (r1_tarski(A_144, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_144, '#skF_5') | ~r1_tarski(A_144, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_686, c_732])).
% 2.73/1.45  tff(c_500, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 2.73/1.45  tff(c_794, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_788, c_500])).
% 2.73/1.45  tff(c_799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_574, c_499, c_794])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 180
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 1
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 11
% 2.73/1.45  #Demod        : 52
% 2.73/1.45  #Tautology    : 84
% 2.73/1.45  #SimpNegUnit  : 5
% 2.73/1.45  #BackRed      : 0
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.33
% 2.73/1.45  Parsing              : 0.18
% 2.73/1.45  CNF conversion       : 0.02
% 2.73/1.45  Main loop            : 0.34
% 2.73/1.46  Inferencing          : 0.13
% 2.73/1.46  Reduction            : 0.11
% 2.73/1.46  Demodulation         : 0.08
% 2.73/1.46  BG Simplification    : 0.02
% 2.73/1.46  Subsumption          : 0.06
% 2.73/1.46  Abstraction          : 0.02
% 2.73/1.46  MUC search           : 0.00
% 2.73/1.46  Cooper               : 0.00
% 2.73/1.46  Total                : 0.71
% 2.73/1.46  Index Insertion      : 0.00
% 2.73/1.46  Index Deletion       : 0.00
% 2.73/1.46  Index Matching       : 0.00
% 2.73/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
