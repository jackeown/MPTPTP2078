%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   67 (  91 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 135 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_670,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_692,plain,(
    ! [C_87] :
      ( ~ r2_hidden(C_87,'#skF_4')
      | ~ r2_hidden(C_87,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_670])).

tff(c_706,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_692])).

tff(c_32,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1193,plain,(
    ! [A_124,C_125,B_126] :
      ( r1_xboole_0(k2_tarski(A_124,C_125),B_126)
      | r2_hidden(C_125,B_126)
      | r2_hidden(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3165,plain,(
    ! [A_165,B_166] :
      ( r1_xboole_0(k1_tarski(A_165),B_166)
      | r2_hidden(A_165,B_166)
      | r2_hidden(A_165,B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1193])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [B_50,A_49] :
      ( r1_xboole_0(B_50,A_49)
      | k3_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_57,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_154,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_154])).

tff(c_1403,plain,(
    ! [A_133,B_134,C_135] :
      ( k3_xboole_0(A_133,k2_xboole_0(B_134,C_135)) = k3_xboole_0(A_133,C_135)
      | ~ r1_xboole_0(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_145,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_40])).

tff(c_148,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_145])).

tff(c_1457,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_148])).

tff(c_1490,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1457])).

tff(c_1496,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_1490])).

tff(c_1501,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1496])).

tff(c_183,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | r1_xboole_0(A_55,k3_xboole_0(B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1270,plain,(
    ! [A_130,B_131,C_132] :
      ( k3_xboole_0(A_130,k3_xboole_0(B_131,C_132)) = k1_xboole_0
      | ~ r1_xboole_0(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_183,c_6])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_149,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_153,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_149])).

tff(c_362,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_1311,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_362])).

tff(c_1504,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_1311])).

tff(c_3178,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_3165,c_1504])).

tff(c_3192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_706,c_3178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.81  
% 4.35/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.38/1.81  
% 4.38/1.81  %Foreground sorts:
% 4.38/1.81  
% 4.38/1.81  
% 4.38/1.81  %Background operators:
% 4.38/1.81  
% 4.38/1.81  
% 4.38/1.81  %Foreground operators:
% 4.38/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.38/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.38/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.38/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.38/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.38/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.38/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.38/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.38/1.81  
% 4.38/1.82  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.38/1.82  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.38/1.82  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.38/1.82  tff(f_103, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 4.38/1.82  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.38/1.82  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.38/1.82  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.38/1.82  tff(f_85, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.38/1.82  tff(f_81, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 4.38/1.82  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.38/1.82  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.38/1.82  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.38/1.82  tff(c_670, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.38/1.82  tff(c_692, plain, (![C_87]: (~r2_hidden(C_87, '#skF_4') | ~r2_hidden(C_87, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_670])).
% 4.38/1.82  tff(c_706, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_692])).
% 4.38/1.82  tff(c_32, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.82  tff(c_1193, plain, (![A_124, C_125, B_126]: (r1_xboole_0(k2_tarski(A_124, C_125), B_126) | r2_hidden(C_125, B_126) | r2_hidden(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.38/1.82  tff(c_3165, plain, (![A_165, B_166]: (r1_xboole_0(k1_tarski(A_165), B_166) | r2_hidden(A_165, B_166) | r2_hidden(A_165, B_166))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1193])).
% 4.38/1.82  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.38/1.82  tff(c_140, plain, (![A_49, B_50]: (r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.82  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.82  tff(c_146, plain, (![B_50, A_49]: (r1_xboole_0(B_50, A_49) | k3_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_10])).
% 4.38/1.82  tff(c_57, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.82  tff(c_60, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_57])).
% 4.38/1.82  tff(c_154, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.82  tff(c_165, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_154])).
% 4.38/1.82  tff(c_1403, plain, (![A_133, B_134, C_135]: (k3_xboole_0(A_133, k2_xboole_0(B_134, C_135))=k3_xboole_0(A_133, C_135) | ~r1_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.38/1.82  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.38/1.82  tff(c_145, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_40])).
% 4.38/1.82  tff(c_148, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_145])).
% 4.38/1.82  tff(c_1457, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1403, c_148])).
% 4.38/1.82  tff(c_1490, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1457])).
% 4.38/1.82  tff(c_1496, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_1490])).
% 4.38/1.82  tff(c_1501, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1496])).
% 4.38/1.82  tff(c_183, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | r1_xboole_0(A_55, k3_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.38/1.82  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.82  tff(c_1270, plain, (![A_130, B_131, C_132]: (k3_xboole_0(A_130, k3_xboole_0(B_131, C_132))=k1_xboole_0 | ~r1_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_183, c_6])).
% 4.38/1.82  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.38/1.82  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 4.38/1.82  tff(c_149, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.38/1.82  tff(c_153, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_47, c_149])).
% 4.38/1.82  tff(c_362, plain, (k3_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_153])).
% 4.38/1.82  tff(c_1311, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_362])).
% 4.38/1.82  tff(c_1504, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1501, c_1311])).
% 4.38/1.82  tff(c_3178, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_3165, c_1504])).
% 4.38/1.82  tff(c_3192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_706, c_706, c_3178])).
% 4.38/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.82  
% 4.38/1.82  Inference rules
% 4.38/1.82  ----------------------
% 4.38/1.82  #Ref     : 0
% 4.38/1.82  #Sup     : 806
% 4.38/1.82  #Fact    : 0
% 4.38/1.82  #Define  : 0
% 4.38/1.82  #Split   : 0
% 4.38/1.82  #Chain   : 0
% 4.38/1.82  #Close   : 0
% 4.38/1.82  
% 4.38/1.82  Ordering : KBO
% 4.38/1.82  
% 4.38/1.82  Simplification rules
% 4.38/1.82  ----------------------
% 4.38/1.82  #Subsume      : 171
% 4.38/1.82  #Demod        : 368
% 4.38/1.82  #Tautology    : 446
% 4.38/1.82  #SimpNegUnit  : 41
% 4.38/1.82  #BackRed      : 0
% 4.38/1.82  
% 4.38/1.82  #Partial instantiations: 0
% 4.38/1.82  #Strategies tried      : 1
% 4.38/1.82  
% 4.38/1.82  Timing (in seconds)
% 4.38/1.82  ----------------------
% 4.38/1.83  Preprocessing        : 0.33
% 4.38/1.83  Parsing              : 0.18
% 4.38/1.83  CNF conversion       : 0.02
% 4.38/1.83  Main loop            : 0.68
% 4.38/1.83  Inferencing          : 0.20
% 4.38/1.83  Reduction            : 0.27
% 4.38/1.83  Demodulation         : 0.22
% 4.38/1.83  BG Simplification    : 0.03
% 4.38/1.83  Subsumption          : 0.13
% 4.38/1.83  Abstraction          : 0.03
% 4.38/1.83  MUC search           : 0.00
% 4.38/1.83  Cooper               : 0.00
% 4.38/1.83  Total                : 1.04
% 4.38/1.83  Index Insertion      : 0.00
% 4.38/1.83  Index Deletion       : 0.00
% 4.38/1.83  Index Matching       : 0.00
% 4.38/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
