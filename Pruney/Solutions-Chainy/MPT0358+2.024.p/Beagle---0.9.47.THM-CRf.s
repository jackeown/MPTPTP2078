%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_500,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | ~ m1_subset_1(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_507,plain,(
    ! [B_72,A_13] :
      ( r1_tarski(B_72,A_13)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_500,c_18])).

tff(c_512,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_507])).

tff(c_525,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_512])).

tff(c_38,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_164,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_53])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_4') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_14])).

tff(c_636,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_646,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_636])).

tff(c_650,plain,(
    k3_subset_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_646])).

tff(c_651,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_164])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_651])).

tff(c_655,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_658,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_53])).

tff(c_662,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_666,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_658,c_662])).

tff(c_875,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,B_115) = k3_subset_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_888,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_875])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_672,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = k1_xboole_0
      | ~ r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_682,plain,(
    ! [A_90,B_91] : k3_xboole_0(k4_xboole_0(A_90,B_91),B_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_672])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_687,plain,(
    ! [B_91,A_90] : k3_xboole_0(B_91,k4_xboole_0(A_90,B_91)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_2])).

tff(c_898,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_687])).

tff(c_907,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_898])).

tff(c_909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.68/1.38  
% 2.68/1.38  %Foreground sorts:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Background operators:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Foreground operators:
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.68/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.68/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.38  
% 2.68/1.39  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.68/1.39  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.68/1.39  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.68/1.39  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.68/1.39  tff(f_65, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.68/1.39  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.68/1.39  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.68/1.39  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.68/1.39  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.68/1.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.68/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.68/1.39  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.39  tff(c_42, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.39  tff(c_500, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | ~m1_subset_1(B_72, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.39  tff(c_18, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.39  tff(c_507, plain, (![B_72, A_13]: (r1_tarski(B_72, A_13) | ~m1_subset_1(B_72, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_500, c_18])).
% 2.68/1.39  tff(c_512, plain, (![B_74, A_75]: (r1_tarski(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(negUnitSimplification, [status(thm)], [c_42, c_507])).
% 2.68/1.39  tff(c_525, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_512])).
% 2.68/1.39  tff(c_38, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.39  tff(c_46, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.39  tff(c_54, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.68/1.39  tff(c_164, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.68/1.39  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.39  tff(c_53, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.68/1.39  tff(c_236, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_164, c_53])).
% 2.68/1.39  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.39  tff(c_243, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_4')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_14])).
% 2.68/1.39  tff(c_636, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.39  tff(c_646, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_636])).
% 2.68/1.39  tff(c_650, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_646])).
% 2.68/1.39  tff(c_651, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_164])).
% 2.68/1.39  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_651])).
% 2.68/1.39  tff(c_655, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 2.68/1.39  tff(c_658, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_655, c_53])).
% 2.68/1.39  tff(c_662, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.39  tff(c_666, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_658, c_662])).
% 2.68/1.39  tff(c_875, plain, (![A_114, B_115]: (k4_xboole_0(A_114, B_115)=k3_subset_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.39  tff(c_888, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_875])).
% 2.68/1.39  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.39  tff(c_672, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=k1_xboole_0 | ~r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.39  tff(c_682, plain, (![A_90, B_91]: (k3_xboole_0(k4_xboole_0(A_90, B_91), B_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_672])).
% 2.68/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.39  tff(c_687, plain, (![B_91, A_90]: (k3_xboole_0(B_91, k4_xboole_0(A_90, B_91))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_682, c_2])).
% 2.68/1.39  tff(c_898, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_888, c_687])).
% 2.68/1.39  tff(c_907, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_666, c_898])).
% 2.68/1.39  tff(c_909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_907])).
% 2.68/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  Inference rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Ref     : 0
% 2.68/1.39  #Sup     : 199
% 2.68/1.39  #Fact    : 0
% 2.68/1.39  #Define  : 0
% 2.68/1.39  #Split   : 1
% 2.68/1.39  #Chain   : 0
% 2.68/1.39  #Close   : 0
% 2.68/1.39  
% 2.68/1.39  Ordering : KBO
% 2.68/1.39  
% 2.68/1.39  Simplification rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Subsume      : 8
% 2.68/1.39  #Demod        : 87
% 2.68/1.39  #Tautology    : 154
% 2.68/1.39  #SimpNegUnit  : 7
% 2.68/1.39  #BackRed      : 9
% 2.68/1.39  
% 2.68/1.39  #Partial instantiations: 0
% 2.68/1.39  #Strategies tried      : 1
% 2.68/1.39  
% 2.68/1.39  Timing (in seconds)
% 2.68/1.39  ----------------------
% 2.68/1.39  Preprocessing        : 0.30
% 2.68/1.39  Parsing              : 0.15
% 2.68/1.39  CNF conversion       : 0.02
% 2.68/1.39  Main loop            : 0.30
% 2.68/1.39  Inferencing          : 0.11
% 2.68/1.39  Reduction            : 0.10
% 2.68/1.39  Demodulation         : 0.08
% 2.68/1.39  BG Simplification    : 0.02
% 2.68/1.39  Subsumption          : 0.05
% 2.68/1.39  Abstraction          : 0.02
% 2.68/1.39  MUC search           : 0.00
% 2.68/1.39  Cooper               : 0.00
% 2.68/1.39  Total                : 0.63
% 2.68/1.39  Index Insertion      : 0.00
% 2.68/1.39  Index Deletion       : 0.00
% 2.68/1.39  Index Matching       : 0.00
% 2.68/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
