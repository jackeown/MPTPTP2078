%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 141 expanded)
%              Number of equality atoms :   20 (  53 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_34,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_83,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_49,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_84,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_94,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_189,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_201,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_189])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_10])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_215])).

tff(c_221,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_221])).

tff(c_224,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_38,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_234,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(B_62,A_63)
      | ~ m1_subset_1(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [B_62,A_10] :
      ( r1_tarski(B_62,A_10)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_242,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_238])).

tff(c_251,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_242])).

tff(c_252,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_252])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_254])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_292,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_305,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_292])).

tff(c_368,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k2_xboole_0(B_82,C_83))
      | ~ r1_tarski(k4_xboole_0(A_81,B_82),C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_427,plain,(
    ! [C_88] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_4',C_88))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),C_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_368])).

tff(c_441,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_225,c_427])).

tff(c_451,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.06/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.32  
% 2.47/1.34  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.47/1.34  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.47/1.34  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.47/1.34  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.47/1.34  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.47/1.34  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.47/1.34  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.47/1.34  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.47/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.47/1.34  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.47/1.34  tff(c_34, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.34  tff(c_42, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_50, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.47/1.34  tff(c_83, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.47/1.34  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_49, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 2.47/1.34  tff(c_84, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_49])).
% 2.47/1.34  tff(c_94, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83])).
% 2.47/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_40])).
% 2.47/1.34  tff(c_189, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.34  tff(c_201, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_85, c_189])).
% 2.47/1.34  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.34  tff(c_215, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_201, c_10])).
% 2.47/1.34  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_215])).
% 2.47/1.34  tff(c_221, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_49])).
% 2.47/1.34  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_221])).
% 2.47/1.34  tff(c_224, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 2.47/1.34  tff(c_38, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.34  tff(c_234, plain, (![B_62, A_63]: (r2_hidden(B_62, A_63) | ~m1_subset_1(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.34  tff(c_14, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.34  tff(c_238, plain, (![B_62, A_10]: (r1_tarski(B_62, A_10) | ~m1_subset_1(B_62, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_234, c_14])).
% 2.47/1.34  tff(c_242, plain, (![B_64, A_65]: (r1_tarski(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)))), inference(negUnitSimplification, [status(thm)], [c_38, c_238])).
% 2.47/1.34  tff(c_251, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_242])).
% 2.47/1.34  tff(c_252, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.34  tff(c_254, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_251, c_252])).
% 2.47/1.34  tff(c_263, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_224, c_254])).
% 2.47/1.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.34  tff(c_225, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.47/1.34  tff(c_292, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.34  tff(c_305, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_292])).
% 2.47/1.34  tff(c_368, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k2_xboole_0(B_82, C_83)) | ~r1_tarski(k4_xboole_0(A_81, B_82), C_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.34  tff(c_427, plain, (![C_88]: (r1_tarski('#skF_3', k2_xboole_0('#skF_4', C_88)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), C_88))), inference(superposition, [status(thm), theory('equality')], [c_305, c_368])).
% 2.47/1.34  tff(c_441, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_225, c_427])).
% 2.47/1.34  tff(c_451, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 2.47/1.34  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_451])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 87
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 4
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 9
% 2.47/1.34  #Demod        : 19
% 2.47/1.34  #Tautology    : 30
% 2.47/1.34  #SimpNegUnit  : 9
% 2.47/1.34  #BackRed      : 1
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.32
% 2.47/1.34  Parsing              : 0.16
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.27
% 2.47/1.34  Inferencing          : 0.10
% 2.47/1.34  Reduction            : 0.08
% 2.47/1.34  Demodulation         : 0.06
% 2.47/1.34  BG Simplification    : 0.02
% 2.47/1.34  Subsumption          : 0.05
% 2.47/1.34  Abstraction          : 0.02
% 2.47/1.34  MUC search           : 0.00
% 2.47/1.34  Cooper               : 0.00
% 2.47/1.34  Total                : 0.62
% 2.47/1.34  Index Insertion      : 0.00
% 2.47/1.34  Index Deletion       : 0.00
% 2.47/1.34  Index Matching       : 0.00
% 2.47/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
