%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  72 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_37,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    ! [C_68,A_69,B_70] :
      ( r2_hidden(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_298,plain,(
    ! [A_85,B_86,A_87] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_87)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(A_87))
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_230])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_310,plain,(
    ! [A_88,A_89] :
      ( ~ m1_subset_1(A_88,k1_zfmisc_1(A_89))
      | r1_tarski(A_88,A_89) ) ),
    inference(resolution,[status(thm)],[c_298,c_4])).

tff(c_318,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_310])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_322,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_318,c_10])).

tff(c_214,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k3_subset_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_218,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_214])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_222,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_12])).

tff(c_324,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_222])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_248,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_400,plain,(
    ! [A_104,B_105,B_106] :
      ( k4_subset_1(A_104,B_105,k3_subset_1(A_104,B_106)) = k2_xboole_0(B_105,k3_subset_1(A_104,B_106))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_28,c_248])).

tff(c_434,plain,(
    ! [B_110] :
      ( k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2',B_110)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2',B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_400])).

tff(c_441,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_434])).

tff(c_444,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_441])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.67/1.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.67/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.67/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.37  
% 2.67/1.38  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.67/1.38  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.67/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.67/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.67/1.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.67/1.38  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.67/1.38  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.67/1.38  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.67/1.38  tff(f_73, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.67/1.38  tff(c_24, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.38  tff(c_34, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.38  tff(c_37, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 2.67/1.38  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.38  tff(c_230, plain, (![C_68, A_69, B_70]: (r2_hidden(C_68, A_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.38  tff(c_298, plain, (![A_85, B_86, A_87]: (r2_hidden('#skF_1'(A_85, B_86), A_87) | ~m1_subset_1(A_85, k1_zfmisc_1(A_87)) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_6, c_230])).
% 2.67/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.38  tff(c_310, plain, (![A_88, A_89]: (~m1_subset_1(A_88, k1_zfmisc_1(A_89)) | r1_tarski(A_88, A_89))), inference(resolution, [status(thm)], [c_298, c_4])).
% 2.67/1.38  tff(c_318, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_310])).
% 2.67/1.38  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.38  tff(c_322, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_318, c_10])).
% 2.67/1.38  tff(c_214, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k3_subset_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.67/1.38  tff(c_218, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_214])).
% 2.67/1.38  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.38  tff(c_222, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_218, c_12])).
% 2.67/1.38  tff(c_324, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_222])).
% 2.67/1.38  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.38  tff(c_248, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.38  tff(c_400, plain, (![A_104, B_105, B_106]: (k4_subset_1(A_104, B_105, k3_subset_1(A_104, B_106))=k2_xboole_0(B_105, k3_subset_1(A_104, B_106)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_104)))), inference(resolution, [status(thm)], [c_28, c_248])).
% 2.67/1.38  tff(c_434, plain, (![B_110]: (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', B_110))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_400])).
% 2.67/1.38  tff(c_441, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_434])).
% 2.67/1.38  tff(c_444, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_441])).
% 2.67/1.38  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_444])).
% 2.67/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  Inference rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Ref     : 0
% 2.67/1.38  #Sup     : 103
% 2.67/1.38  #Fact    : 0
% 2.67/1.38  #Define  : 0
% 2.67/1.38  #Split   : 0
% 2.67/1.38  #Chain   : 0
% 2.67/1.38  #Close   : 0
% 2.67/1.38  
% 2.67/1.38  Ordering : KBO
% 2.67/1.38  
% 2.67/1.38  Simplification rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Subsume      : 2
% 2.67/1.38  #Demod        : 14
% 2.67/1.38  #Tautology    : 59
% 2.67/1.38  #SimpNegUnit  : 1
% 2.67/1.38  #BackRed      : 2
% 2.67/1.38  
% 2.67/1.38  #Partial instantiations: 0
% 2.67/1.38  #Strategies tried      : 1
% 2.67/1.38  
% 2.67/1.38  Timing (in seconds)
% 2.67/1.38  ----------------------
% 2.67/1.38  Preprocessing        : 0.31
% 2.67/1.38  Parsing              : 0.17
% 2.67/1.38  CNF conversion       : 0.02
% 2.67/1.38  Main loop            : 0.26
% 2.67/1.38  Inferencing          : 0.10
% 2.67/1.38  Reduction            : 0.08
% 2.67/1.38  Demodulation         : 0.06
% 2.67/1.38  BG Simplification    : 0.01
% 2.67/1.38  Subsumption          : 0.05
% 2.67/1.38  Abstraction          : 0.02
% 2.67/1.38  MUC search           : 0.00
% 2.67/1.38  Cooper               : 0.00
% 2.67/1.38  Total                : 0.60
% 2.67/1.38  Index Insertion      : 0.00
% 2.67/1.38  Index Deletion       : 0.00
% 2.67/1.38  Index Matching       : 0.00
% 2.67/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
