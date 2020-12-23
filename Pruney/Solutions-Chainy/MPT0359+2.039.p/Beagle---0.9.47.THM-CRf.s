%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 149 expanded)
%              Number of equality atoms :   20 (  54 expanded)
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

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_34,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_83,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_84,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_181,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_193,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_181])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_220,plain,(
    ! [B_59] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_4'),B_59)
      | ~ r1_tarski('#skF_4',B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_10])).

tff(c_94,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83])).

tff(c_225,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_94])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_225])).

tff(c_231,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_231])).

tff(c_234,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_38,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_270,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,A_72)
      | ~ m1_subset_1(B_71,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_277,plain,(
    ! [B_71,A_11] :
      ( r1_tarski(B_71,A_11)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_270,c_14])).

tff(c_282,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_277])).

tff(c_295,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_282])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_297,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_295,c_4])).

tff(c_300,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_297])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_332,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k3_subset_1(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_345,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_332])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k2_xboole_0(B_9,C_10))
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_449,plain,(
    ! [C_94] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_4',C_94))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_12])).

tff(c_467,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_235,c_449])).

tff(c_477,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_467])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.36  
% 2.41/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.41/1.36  
% 2.41/1.36  %Foreground sorts:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Background operators:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Foreground operators:
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.41/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.41/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.36  
% 2.58/1.38  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.58/1.38  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.58/1.38  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.58/1.38  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.58/1.38  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.58/1.38  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.58/1.38  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.58/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.58/1.38  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.58/1.38  tff(c_34, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.38  tff(c_42, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.38  tff(c_50, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.58/1.38  tff(c_83, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.58/1.38  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.38  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.38  tff(c_49, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 2.58/1.38  tff(c_84, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_49])).
% 2.58/1.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.38  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_40])).
% 2.58/1.38  tff(c_181, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.38  tff(c_193, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_85, c_181])).
% 2.58/1.38  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.38  tff(c_220, plain, (![B_59]: (r1_tarski(k3_subset_1('#skF_4', '#skF_4'), B_59) | ~r1_tarski('#skF_4', B_59))), inference(superposition, [status(thm), theory('equality')], [c_193, c_10])).
% 2.58/1.38  tff(c_94, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83])).
% 2.58/1.38  tff(c_225, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_220, c_94])).
% 2.58/1.38  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_225])).
% 2.58/1.38  tff(c_231, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_49])).
% 2.58/1.38  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_231])).
% 2.58/1.38  tff(c_234, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 2.58/1.38  tff(c_38, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.38  tff(c_270, plain, (![B_71, A_72]: (r2_hidden(B_71, A_72) | ~m1_subset_1(B_71, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.38  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.38  tff(c_277, plain, (![B_71, A_11]: (r1_tarski(B_71, A_11) | ~m1_subset_1(B_71, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_270, c_14])).
% 2.58/1.38  tff(c_282, plain, (![B_73, A_74]: (r1_tarski(B_73, A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)))), inference(negUnitSimplification, [status(thm)], [c_38, c_277])).
% 2.58/1.38  tff(c_295, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_282])).
% 2.58/1.38  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.38  tff(c_297, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_295, c_4])).
% 2.58/1.38  tff(c_300, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_234, c_297])).
% 2.58/1.38  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.38  tff(c_235, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.58/1.38  tff(c_332, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k3_subset_1(A_83, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.38  tff(c_345, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_332])).
% 2.58/1.38  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k2_xboole_0(B_9, C_10)) | ~r1_tarski(k4_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.38  tff(c_449, plain, (![C_94]: (r1_tarski('#skF_3', k2_xboole_0('#skF_4', C_94)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), C_94))), inference(superposition, [status(thm), theory('equality')], [c_345, c_12])).
% 2.58/1.38  tff(c_467, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_235, c_449])).
% 2.58/1.38  tff(c_477, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_467])).
% 2.58/1.38  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_477])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 94
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 3
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Subsume      : 9
% 2.58/1.38  #Demod        : 12
% 2.58/1.38  #Tautology    : 29
% 2.58/1.38  #SimpNegUnit  : 8
% 2.58/1.38  #BackRed      : 1
% 2.58/1.38  
% 2.58/1.38  #Partial instantiations: 0
% 2.58/1.38  #Strategies tried      : 1
% 2.58/1.38  
% 2.58/1.38  Timing (in seconds)
% 2.58/1.38  ----------------------
% 2.58/1.38  Preprocessing        : 0.32
% 2.58/1.38  Parsing              : 0.16
% 2.58/1.38  CNF conversion       : 0.02
% 2.58/1.38  Main loop            : 0.28
% 2.58/1.38  Inferencing          : 0.10
% 2.58/1.38  Reduction            : 0.08
% 2.58/1.38  Demodulation         : 0.06
% 2.58/1.38  BG Simplification    : 0.02
% 2.58/1.38  Subsumption          : 0.06
% 2.58/1.38  Abstraction          : 0.02
% 2.58/1.38  MUC search           : 0.00
% 2.58/1.38  Cooper               : 0.00
% 2.58/1.38  Total                : 0.63
% 2.58/1.38  Index Insertion      : 0.00
% 2.58/1.38  Index Deletion       : 0.00
% 2.58/1.38  Index Matching       : 0.00
% 2.58/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
