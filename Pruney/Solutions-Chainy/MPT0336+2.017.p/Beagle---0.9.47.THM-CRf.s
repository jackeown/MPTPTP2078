%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 (  90 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    ! [B_45,A_46] :
      ( r1_xboole_0(B_45,A_46)
      | ~ r1_xboole_0(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_1216,plain,(
    ! [A_127,B_128,C_129] :
      ( k3_xboole_0(A_127,k2_xboole_0(B_128,C_129)) = k3_xboole_0(A_127,C_129)
      | ~ r1_xboole_0(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_354,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_362,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_354,c_50])).

tff(c_366,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_362])).

tff(c_1246,plain,
    ( k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_366])).

tff(c_1293,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1246])).

tff(c_389,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | r1_xboole_0(A_78,k3_xboole_0(B_79,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1399,plain,(
    ! [A_133,B_134,C_135] :
      ( k3_xboole_0(A_133,k3_xboole_0(B_134,C_135)) = k1_xboole_0
      | ~ r1_xboole_0(A_133,B_134) ) ),
    inference(resolution,[status(thm)],[c_389,c_6])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_347,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_351,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_347])).

tff(c_444,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_351])).

tff(c_1419,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_444])).

tff(c_1521,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_1419])).

tff(c_1569,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1521])).

tff(c_941,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,B_103)
      | ~ r2_hidden(C_104,A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_980,plain,(
    ! [C_104] :
      ( ~ r2_hidden(C_104,'#skF_3')
      | ~ r2_hidden(C_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_941])).

tff(c_1574,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1569,c_980])).

tff(c_1579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:38:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.48  
% 3.19/1.50  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.19/1.50  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.19/1.50  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.19/1.50  tff(f_75, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.19/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.19/1.50  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.19/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.19/1.50  tff(f_71, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.19/1.50  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.19/1.50  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.19/1.50  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.19/1.50  tff(c_40, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.50  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.19/1.50  tff(c_75, plain, (![B_45, A_46]: (r1_xboole_0(B_45, A_46) | ~r1_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.50  tff(c_84, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_75])).
% 3.19/1.50  tff(c_1216, plain, (![A_127, B_128, C_129]: (k3_xboole_0(A_127, k2_xboole_0(B_128, C_129))=k3_xboole_0(A_127, C_129) | ~r1_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.50  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.50  tff(c_354, plain, (![A_68, B_69]: (r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.50  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.19/1.50  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 3.19/1.50  tff(c_362, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_354, c_50])).
% 3.19/1.50  tff(c_366, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_362])).
% 3.19/1.50  tff(c_1246, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1216, c_366])).
% 3.19/1.50  tff(c_1293, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1246])).
% 3.19/1.50  tff(c_389, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | r1_xboole_0(A_78, k3_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.50  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.50  tff(c_1399, plain, (![A_133, B_134, C_135]: (k3_xboole_0(A_133, k3_xboole_0(B_134, C_135))=k1_xboole_0 | ~r1_xboole_0(A_133, B_134))), inference(resolution, [status(thm)], [c_389, c_6])).
% 3.19/1.50  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.19/1.50  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_48])).
% 3.19/1.50  tff(c_347, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.50  tff(c_351, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_49, c_347])).
% 3.19/1.50  tff(c_444, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_351])).
% 3.19/1.50  tff(c_1419, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1399, c_444])).
% 3.19/1.50  tff(c_1521, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1293, c_1419])).
% 3.19/1.50  tff(c_1569, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_1521])).
% 3.19/1.50  tff(c_941, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, B_103) | ~r2_hidden(C_104, A_102))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.50  tff(c_980, plain, (![C_104]: (~r2_hidden(C_104, '#skF_3') | ~r2_hidden(C_104, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_941])).
% 3.19/1.50  tff(c_1574, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1569, c_980])).
% 3.19/1.50  tff(c_1579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1574])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 389
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 0
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 47
% 3.19/1.50  #Demod        : 173
% 3.19/1.50  #Tautology    : 234
% 3.19/1.50  #SimpNegUnit  : 2
% 3.19/1.50  #BackRed      : 0
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.50  Preprocessing        : 0.31
% 3.19/1.50  Parsing              : 0.16
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.44
% 3.19/1.50  Inferencing          : 0.15
% 3.19/1.50  Reduction            : 0.16
% 3.19/1.50  Demodulation         : 0.13
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.07
% 3.19/1.50  Abstraction          : 0.02
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.78
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
