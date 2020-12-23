%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 159 expanded)
%              Number of leaves         :   34 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 226 expanded)
%              Number of equality atoms :   43 ( 191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_80,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_78,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_46,plain,(
    ! [B_47] : k2_zfmisc_1(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_110,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_278,plain,(
    ! [B_79,A_80] :
      ( k1_xboole_0 = B_79
      | k1_xboole_0 = A_80
      | k2_zfmisc_1(A_80,B_79) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_281,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_278])).

tff(c_290,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_281])).

tff(c_52,plain,(
    ! [A_48] : k3_tarski(k1_tarski(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_300,plain,(
    k3_tarski(k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_52])).

tff(c_50,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_50])).

tff(c_105,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_317,plain,(
    ! [A_12] : r1_tarski('#skF_5',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_108])).

tff(c_263,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_275,plain,(
    ! [A_12,C_77] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_263])).

tff(c_276,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_312,plain,(
    ! [C_77] : ~ r2_hidden(C_77,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_276])).

tff(c_310,plain,(
    k1_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_290])).

tff(c_48,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_319,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_48])).

tff(c_454,plain,(
    k1_zfmisc_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_319])).

tff(c_32,plain,(
    ! [C_45,A_41] :
      ( r2_hidden(C_45,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_45,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_467,plain,(
    ! [C_45] :
      ( r2_hidden(C_45,'#skF_5')
      | ~ r1_tarski(C_45,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_32])).

tff(c_474,plain,(
    ! [C_88] : ~ r1_tarski(C_88,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_467])).

tff(c_485,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_317,c_474])).

tff(c_504,plain,(
    ! [A_91] : ~ r1_xboole_0(A_91,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_508,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_504])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_508])).

tff(c_513,plain,(
    k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_672,plain,(
    ! [B_110,A_111] :
      ( k1_xboole_0 = B_110
      | k1_xboole_0 = A_111
      | k2_zfmisc_1(A_111,B_110) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_675,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_672])).

tff(c_684,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_675])).

tff(c_514,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_702,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_514])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.48/1.34  
% 2.48/1.34  %Foreground sorts:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Background operators:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Foreground operators:
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.34  
% 2.62/1.35  tff(f_76, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.62/1.35  tff(f_92, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.62/1.35  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.62/1.35  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.62/1.35  tff(f_80, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.62/1.35  tff(f_78, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.62/1.35  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.62/1.35  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.62/1.35  tff(f_77, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.62/1.35  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.62/1.35  tff(c_46, plain, (![B_47]: (k2_zfmisc_1(k1_xboole_0, B_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.35  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.62/1.35  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.35  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.35  tff(c_56, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.62/1.35  tff(c_110, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_278, plain, (![B_79, A_80]: (k1_xboole_0=B_79 | k1_xboole_0=A_80 | k2_zfmisc_1(A_80, B_79)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.35  tff(c_281, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_110, c_278])).
% 2.62/1.35  tff(c_290, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_281])).
% 2.62/1.35  tff(c_52, plain, (![A_48]: (k3_tarski(k1_tarski(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.35  tff(c_300, plain, (k3_tarski(k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_290, c_52])).
% 2.62/1.35  tff(c_50, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.35  tff(c_304, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_50])).
% 2.62/1.35  tff(c_105, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.35  tff(c_108, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 2.62/1.35  tff(c_317, plain, (![A_12]: (r1_tarski('#skF_5', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_108])).
% 2.62/1.35  tff(c_263, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.35  tff(c_275, plain, (![A_12, C_77]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_263])).
% 2.62/1.35  tff(c_276, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_275])).
% 2.62/1.35  tff(c_312, plain, (![C_77]: (~r2_hidden(C_77, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_276])).
% 2.62/1.35  tff(c_310, plain, (k1_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_290])).
% 2.62/1.35  tff(c_48, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.35  tff(c_319, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_48])).
% 2.62/1.35  tff(c_454, plain, (k1_zfmisc_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_319])).
% 2.62/1.35  tff(c_32, plain, (![C_45, A_41]: (r2_hidden(C_45, k1_zfmisc_1(A_41)) | ~r1_tarski(C_45, A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.62/1.35  tff(c_467, plain, (![C_45]: (r2_hidden(C_45, '#skF_5') | ~r1_tarski(C_45, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_454, c_32])).
% 2.62/1.35  tff(c_474, plain, (![C_88]: (~r1_tarski(C_88, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_312, c_467])).
% 2.62/1.35  tff(c_485, plain, $false, inference(resolution, [status(thm)], [c_317, c_474])).
% 2.62/1.35  tff(c_504, plain, (![A_91]: (~r1_xboole_0(A_91, k1_xboole_0))), inference(splitRight, [status(thm)], [c_275])).
% 2.62/1.35  tff(c_508, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_504])).
% 2.62/1.35  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_508])).
% 2.62/1.35  tff(c_513, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_672, plain, (![B_110, A_111]: (k1_xboole_0=B_110 | k1_xboole_0=A_111 | k2_zfmisc_1(A_111, B_110)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.35  tff(c_675, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_513, c_672])).
% 2.62/1.35  tff(c_684, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_675])).
% 2.62/1.35  tff(c_514, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_702, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_684, c_514])).
% 2.62/1.35  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_702])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 160
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 2
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 4
% 2.62/1.35  #Demod        : 71
% 2.62/1.35  #Tautology    : 121
% 2.62/1.35  #SimpNegUnit  : 4
% 2.62/1.35  #BackRed      : 18
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.36  Preprocessing        : 0.33
% 2.62/1.36  Parsing              : 0.17
% 2.62/1.36  CNF conversion       : 0.02
% 2.62/1.36  Main loop            : 0.25
% 2.62/1.36  Inferencing          : 0.08
% 2.62/1.36  Reduction            : 0.09
% 2.62/1.36  Demodulation         : 0.07
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.04
% 2.62/1.36  Abstraction          : 0.01
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.61
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
