%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 162 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 260 expanded)
%              Number of equality atoms :   30 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_55,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_865,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ r1_xboole_0(A_103,C_104)
      | ~ r1_xboole_0(A_103,B_105)
      | r1_xboole_0(A_103,k2_xboole_0(B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3993,plain,(
    ! [B_244,C_245,A_246] :
      ( r1_xboole_0(k2_xboole_0(B_244,C_245),A_246)
      | ~ r1_xboole_0(A_246,C_245)
      | ~ r1_xboole_0(A_246,B_244) ) ),
    inference(resolution,[status(thm)],[c_865,c_4])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4011,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3993,c_38])).

tff(c_4019,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4011])).

tff(c_4031,plain,(
    k4_xboole_0('#skF_3','#skF_2') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_4019])).

tff(c_96,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = A_35
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_384,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,k1_tarski(B_72)) = A_71
      | r2_hidden(B_72,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,k4_xboole_0(C_19,B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3265,plain,(
    ! [A_209,A_210,B_211] :
      ( r1_xboole_0(A_209,A_210)
      | ~ r1_tarski(A_209,k1_tarski(B_211))
      | r2_hidden(B_211,A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_24])).

tff(c_3269,plain,(
    ! [A_212] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_212)
      | r2_hidden('#skF_5',A_212) ) ),
    inference(resolution,[status(thm)],[c_45,c_3265])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9873,plain,(
    ! [A_370] :
      ( k4_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_370) = k3_xboole_0('#skF_3','#skF_2')
      | r2_hidden('#skF_5',A_370) ) ),
    inference(resolution,[status(thm)],[c_3269,c_20])).

tff(c_122,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_148,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | k4_xboole_0(A_44,B_43) != A_44 ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_157,plain,(
    ! [B_43,A_44] :
      ( k4_xboole_0(B_43,A_44) = B_43
      | k4_xboole_0(A_44,B_43) != A_44 ) ),
    inference(resolution,[status(thm)],[c_148,c_20])).

tff(c_10602,plain,(
    ! [A_392] :
      ( k4_xboole_0(A_392,k3_xboole_0('#skF_3','#skF_2')) = A_392
      | r2_hidden('#skF_5',A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9873,c_157])).

tff(c_298,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_301,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,k4_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_12])).

tff(c_10670,plain,
    ( k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10602,c_301])).

tff(c_10829,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10670])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_132,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,A_39)
      | k4_xboole_0(A_39,B_40) != A_39 ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_671,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,B_93)
      | ~ r2_hidden(C_94,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10324,plain,(
    ! [C_377,A_378,B_379] :
      ( ~ r2_hidden(C_377,A_378)
      | ~ r2_hidden(C_377,B_379)
      | k4_xboole_0(A_378,B_379) != A_378 ) ),
    inference(resolution,[status(thm)],[c_132,c_671])).

tff(c_10345,plain,(
    ! [B_379] :
      ( ~ r2_hidden('#skF_5',B_379)
      | k4_xboole_0('#skF_4',B_379) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_42,c_10324])).

tff(c_10833,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10829,c_10345])).

tff(c_10854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_10833])).

tff(c_10855,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10670])).

tff(c_134,plain,(
    ! [A_41,B_42] : r1_xboole_0(k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)),B_42) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_41,B_42] : k4_xboole_0(k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)),B_42) = k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) ),
    inference(resolution,[status(thm)],[c_134,c_20])).

tff(c_5129,plain,(
    ! [A_41,B_42] : k4_xboole_0(k3_xboole_0(A_41,k4_xboole_0(A_41,B_42)),B_42) = k3_xboole_0(A_41,k4_xboole_0(A_41,B_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_301,c_146])).

tff(c_10881,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10855,c_5129])).

tff(c_10908,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10855,c_10881])).

tff(c_10910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4031,c_10908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/2.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.86  
% 8.29/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.29/2.86  
% 8.29/2.86  %Foreground sorts:
% 8.29/2.86  
% 8.29/2.86  
% 8.29/2.86  %Background operators:
% 8.29/2.86  
% 8.29/2.86  
% 8.29/2.86  %Foreground operators:
% 8.29/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.29/2.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.29/2.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.29/2.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.29/2.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.29/2.86  tff('#skF_5', type, '#skF_5': $i).
% 8.29/2.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.29/2.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.29/2.86  tff('#skF_2', type, '#skF_2': $i).
% 8.29/2.86  tff('#skF_3', type, '#skF_3': $i).
% 8.29/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/2.86  tff('#skF_4', type, '#skF_4': $i).
% 8.29/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/2.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/2.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.29/2.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.29/2.86  
% 8.29/2.87  tff(f_71, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.29/2.87  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.29/2.87  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.29/2.87  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.29/2.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.29/2.87  tff(f_88, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.29/2.87  tff(f_75, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 8.29/2.87  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.29/2.87  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.29/2.87  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 8.29/2.87  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.29/2.87  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.29/2.87  tff(c_55, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/2.87  tff(c_58, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_55])).
% 8.29/2.87  tff(c_865, plain, (![A_103, C_104, B_105]: (~r1_xboole_0(A_103, C_104) | ~r1_xboole_0(A_103, B_105) | r1_xboole_0(A_103, k2_xboole_0(B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.29/2.87  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/2.87  tff(c_3993, plain, (![B_244, C_245, A_246]: (r1_xboole_0(k2_xboole_0(B_244, C_245), A_246) | ~r1_xboole_0(A_246, C_245) | ~r1_xboole_0(A_246, B_244))), inference(resolution, [status(thm)], [c_865, c_4])).
% 8.29/2.87  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.29/2.87  tff(c_4011, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3993, c_38])).
% 8.29/2.87  tff(c_4019, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4011])).
% 8.29/2.87  tff(c_4031, plain, (k4_xboole_0('#skF_3', '#skF_2')!='#skF_3'), inference(resolution, [status(thm)], [c_22, c_4019])).
% 8.29/2.87  tff(c_96, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=A_35 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.29/2.87  tff(c_104, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_96])).
% 8.29/2.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.87  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.29/2.87  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 8.29/2.87  tff(c_384, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k1_tarski(B_72))=A_71 | r2_hidden(B_72, A_71))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.29/2.87  tff(c_24, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, k4_xboole_0(C_19, B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.87  tff(c_3265, plain, (![A_209, A_210, B_211]: (r1_xboole_0(A_209, A_210) | ~r1_tarski(A_209, k1_tarski(B_211)) | r2_hidden(B_211, A_210))), inference(superposition, [status(thm), theory('equality')], [c_384, c_24])).
% 8.29/2.87  tff(c_3269, plain, (![A_212]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_212) | r2_hidden('#skF_5', A_212))), inference(resolution, [status(thm)], [c_45, c_3265])).
% 8.29/2.87  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.29/2.87  tff(c_9873, plain, (![A_370]: (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_370)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', A_370))), inference(resolution, [status(thm)], [c_3269, c_20])).
% 8.29/2.87  tff(c_122, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k4_xboole_0(A_39, B_40)!=A_39)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.29/2.87  tff(c_148, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | k4_xboole_0(A_44, B_43)!=A_44)), inference(resolution, [status(thm)], [c_122, c_4])).
% 8.29/2.87  tff(c_157, plain, (![B_43, A_44]: (k4_xboole_0(B_43, A_44)=B_43 | k4_xboole_0(A_44, B_43)!=A_44)), inference(resolution, [status(thm)], [c_148, c_20])).
% 8.29/2.87  tff(c_10602, plain, (![A_392]: (k4_xboole_0(A_392, k3_xboole_0('#skF_3', '#skF_2'))=A_392 | r2_hidden('#skF_5', A_392))), inference(superposition, [status(thm), theory('equality')], [c_9873, c_157])).
% 8.29/2.87  tff(c_298, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/2.87  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/2.87  tff(c_301, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k3_xboole_0(A_69, k4_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_298, c_12])).
% 8.29/2.88  tff(c_10670, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10602, c_301])).
% 8.29/2.88  tff(c_10829, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_10670])).
% 8.29/2.88  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.29/2.88  tff(c_132, plain, (![B_40, A_39]: (r1_xboole_0(B_40, A_39) | k4_xboole_0(A_39, B_40)!=A_39)), inference(resolution, [status(thm)], [c_122, c_4])).
% 8.29/2.88  tff(c_671, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, B_93) | ~r2_hidden(C_94, A_92))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.29/2.88  tff(c_10324, plain, (![C_377, A_378, B_379]: (~r2_hidden(C_377, A_378) | ~r2_hidden(C_377, B_379) | k4_xboole_0(A_378, B_379)!=A_378)), inference(resolution, [status(thm)], [c_132, c_671])).
% 8.29/2.88  tff(c_10345, plain, (![B_379]: (~r2_hidden('#skF_5', B_379) | k4_xboole_0('#skF_4', B_379)!='#skF_4')), inference(resolution, [status(thm)], [c_42, c_10324])).
% 8.29/2.88  tff(c_10833, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_10829, c_10345])).
% 8.29/2.88  tff(c_10854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_10833])).
% 8.29/2.88  tff(c_10855, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(splitRight, [status(thm)], [c_10670])).
% 8.29/2.88  tff(c_134, plain, (![A_41, B_42]: (r1_xboole_0(k4_xboole_0(A_41, k3_xboole_0(A_41, B_42)), B_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.29/2.88  tff(c_146, plain, (![A_41, B_42]: (k4_xboole_0(k4_xboole_0(A_41, k3_xboole_0(A_41, B_42)), B_42)=k4_xboole_0(A_41, k3_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_134, c_20])).
% 8.29/2.88  tff(c_5129, plain, (![A_41, B_42]: (k4_xboole_0(k3_xboole_0(A_41, k4_xboole_0(A_41, B_42)), B_42)=k3_xboole_0(A_41, k4_xboole_0(A_41, B_42)))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_301, c_146])).
% 8.29/2.88  tff(c_10881, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10855, c_5129])).
% 8.29/2.88  tff(c_10908, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10855, c_10881])).
% 8.29/2.88  tff(c_10910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4031, c_10908])).
% 8.29/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.88  
% 8.29/2.88  Inference rules
% 8.29/2.88  ----------------------
% 8.29/2.88  #Ref     : 0
% 8.29/2.88  #Sup     : 2745
% 8.29/2.88  #Fact    : 0
% 8.29/2.88  #Define  : 0
% 8.29/2.88  #Split   : 5
% 8.29/2.88  #Chain   : 0
% 8.29/2.88  #Close   : 0
% 8.29/2.88  
% 8.29/2.88  Ordering : KBO
% 8.29/2.88  
% 8.29/2.88  Simplification rules
% 8.29/2.88  ----------------------
% 8.29/2.88  #Subsume      : 376
% 8.29/2.88  #Demod        : 1842
% 8.29/2.88  #Tautology    : 1193
% 8.29/2.88  #SimpNegUnit  : 55
% 8.29/2.88  #BackRed      : 79
% 8.29/2.88  
% 8.29/2.88  #Partial instantiations: 0
% 8.29/2.88  #Strategies tried      : 1
% 8.29/2.88  
% 8.29/2.88  Timing (in seconds)
% 8.29/2.88  ----------------------
% 8.54/2.88  Preprocessing        : 0.31
% 8.54/2.88  Parsing              : 0.17
% 8.54/2.88  CNF conversion       : 0.02
% 8.54/2.88  Main loop            : 1.79
% 8.54/2.88  Inferencing          : 0.49
% 8.54/2.88  Reduction            : 0.75
% 8.54/2.88  Demodulation         : 0.59
% 8.54/2.88  BG Simplification    : 0.06
% 8.54/2.88  Subsumption          : 0.36
% 8.54/2.88  Abstraction          : 0.07
% 8.54/2.88  MUC search           : 0.00
% 8.54/2.88  Cooper               : 0.00
% 8.54/2.88  Total                : 2.14
% 8.54/2.88  Index Insertion      : 0.00
% 8.54/2.88  Index Deletion       : 0.00
% 8.54/2.88  Index Matching       : 0.00
% 8.54/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
