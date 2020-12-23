%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 14.39s
% Output     : CNFRefutation 14.51s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 284 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_46,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_1617,plain,(
    ! [A_134,C_135,B_136] :
      ( ~ r1_xboole_0(A_134,C_135)
      | ~ r1_xboole_0(A_134,B_136)
      | r1_xboole_0(A_134,k2_xboole_0(B_136,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5377,plain,(
    ! [B_264,C_265,A_266] :
      ( r1_xboole_0(k2_xboole_0(B_264,C_265),A_266)
      | ~ r1_xboole_0(A_266,C_265)
      | ~ r1_xboole_0(A_266,B_264) ) ),
    inference(resolution,[status(thm)],[c_1617,c_2])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5399,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5377,c_44])).

tff(c_5411,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5399])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_67,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_78,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_134,plain,(
    ! [B_48,A_49] : k4_xboole_0(B_48,k4_xboole_0(A_49,B_48)) = B_48 ),
    inference(resolution,[status(thm)],[c_67,c_78])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,(
    ! [B_48] : r1_tarski(B_48,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_14])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_68,c_78])).

tff(c_32,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_171,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_180,plain,(
    ! [A_25] : k3_tarski(k1_tarski(A_25)) = k2_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_25261,plain,(
    ! [A_585,A_586] :
      ( ~ r1_xboole_0(A_585,A_586)
      | ~ r1_xboole_0(A_585,A_586)
      | r1_xboole_0(A_585,k3_tarski(k1_tarski(A_586))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_1617])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_25277,plain,(
    ! [A_585,A_586] :
      ( k4_xboole_0(A_585,k3_tarski(k1_tarski(A_586))) = A_585
      | ~ r1_xboole_0(A_585,A_586) ) ),
    inference(resolution,[status(thm)],[c_25261,c_28])).

tff(c_246,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,k1_tarski(B_64)) = A_63
      | r2_hidden(B_64,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_261,plain,(
    ! [B_64,A_63] :
      ( r1_xboole_0(k1_tarski(B_64),A_63)
      | r2_hidden(B_64,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_67])).

tff(c_324,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_xboole_0(A_74,B_75)
      | ~ r1_xboole_0(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6449,plain,(
    ! [A_302,A_303] :
      ( r1_xboole_0(A_302,A_303)
      | ~ r1_xboole_0(A_302,k3_tarski(k1_tarski(A_303))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_324])).

tff(c_32538,plain,(
    ! [B_717,A_718] :
      ( r1_xboole_0(k1_tarski(B_717),A_718)
      | r2_hidden(B_717,k3_tarski(k1_tarski(A_718))) ) ),
    inference(resolution,[status(thm)],[c_261,c_6449])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_183,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(A_53,B_54)
      | k4_xboole_0(A_53,B_54) != A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_193,plain,(
    ! [B_54,A_53] :
      ( r1_xboole_0(B_54,A_53)
      | k4_xboole_0(A_53,B_54) != A_53 ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_1062,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,B_113)
      | ~ r2_hidden(C_114,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21827,plain,(
    ! [C_517,A_518,B_519] :
      ( ~ r2_hidden(C_517,A_518)
      | ~ r2_hidden(C_517,B_519)
      | k4_xboole_0(A_518,B_519) != A_518 ) ),
    inference(resolution,[status(thm)],[c_193,c_1062])).

tff(c_21836,plain,(
    ! [B_519] :
      ( ~ r2_hidden('#skF_5',B_519)
      | k4_xboole_0('#skF_4',B_519) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_48,c_21827])).

tff(c_33982,plain,(
    ! [A_734] :
      ( k4_xboole_0('#skF_4',k3_tarski(k1_tarski(A_734))) != '#skF_4'
      | r1_xboole_0(k1_tarski('#skF_5'),A_734) ) ),
    inference(resolution,[status(thm)],[c_32538,c_21836])).

tff(c_33991,plain,(
    ! [A_735] :
      ( r1_xboole_0(k1_tarski('#skF_5'),A_735)
      | ~ r1_xboole_0('#skF_4',A_735) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25277,c_33982])).

tff(c_25960,plain,(
    ! [A_616,A_617] :
      ( k4_xboole_0(A_616,k3_tarski(k1_tarski(A_617))) = A_616
      | ~ r1_xboole_0(A_616,A_617) ) ),
    inference(resolution,[status(thm)],[c_25261,c_28])).

tff(c_348,plain,(
    ! [A_77,B_78,C_79] : r1_xboole_0(k4_xboole_0(A_77,k2_xboole_0(B_78,C_79)),B_78) ),
    inference(resolution,[status(thm)],[c_26,c_324])).

tff(c_364,plain,(
    ! [B_80,A_81,C_82] : r1_xboole_0(B_80,k4_xboole_0(A_81,k2_xboole_0(B_80,C_82))) ),
    inference(resolution,[status(thm)],[c_348,c_2])).

tff(c_7800,plain,(
    ! [B_347,A_348,C_349] : k4_xboole_0(B_347,k4_xboole_0(A_348,k2_xboole_0(B_347,C_349))) = B_347 ),
    inference(resolution,[status(thm)],[c_364,c_28])).

tff(c_8127,plain,(
    ! [A_25,A_348] : k4_xboole_0(A_25,k4_xboole_0(A_348,k3_tarski(k1_tarski(A_25)))) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_7800])).

tff(c_26140,plain,(
    ! [A_617,A_616] :
      ( k4_xboole_0(A_617,A_616) = A_617
      | ~ r1_xboole_0(A_616,A_617) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25960,c_8127])).

tff(c_34187,plain,(
    ! [A_741] :
      ( k4_xboole_0(A_741,k1_tarski('#skF_5')) = A_741
      | ~ r1_xboole_0('#skF_4',A_741) ) ),
    inference(resolution,[status(thm)],[c_33991,c_26140])).

tff(c_376,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_xboole_0(A_83,C_84)
      | ~ r1_tarski(A_83,k4_xboole_0(B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_451,plain,(
    ! [B_90,C_91,B_92] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_90,C_91),B_92),C_91) ),
    inference(resolution,[status(thm)],[c_14,c_376])).

tff(c_507,plain,(
    ! [B_94] : r1_xboole_0(k4_xboole_0('#skF_3',B_94),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_451])).

tff(c_523,plain,(
    ! [B_94] : k4_xboole_0(k4_xboole_0('#skF_3',B_94),'#skF_4') = k4_xboole_0('#skF_3',B_94) ),
    inference(resolution,[status(thm)],[c_507,c_28])).

tff(c_34464,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = k4_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34187,c_523])).

tff(c_34907,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_92,c_34464])).

tff(c_91,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_67,c_78])).

tff(c_10178,plain,(
    ! [A_367,A_368,B_369] :
      ( r1_xboole_0(A_367,k4_xboole_0(A_368,B_369))
      | ~ r1_tarski(A_367,B_369) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_376])).

tff(c_10254,plain,(
    ! [A_368,B_369,A_367] :
      ( r1_xboole_0(k4_xboole_0(A_368,B_369),A_367)
      | ~ r1_tarski(A_367,B_369) ) ),
    inference(resolution,[status(thm)],[c_10178,c_2])).

tff(c_39911,plain,(
    ! [A_778] :
      ( r1_xboole_0('#skF_3',A_778)
      | ~ r1_tarski(A_778,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34907,c_10254])).

tff(c_39981,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_39911])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_xboole_0(A_18,k3_xboole_0(B_19,C_20))
      | ~ r1_tarski(A_18,C_20)
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39989,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_39981,c_24])).

tff(c_40000,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_39989])).

tff(c_40002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5411,c_40000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.39/6.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.39/6.62  
% 14.39/6.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.39/6.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.39/6.62  
% 14.39/6.62  %Foreground sorts:
% 14.39/6.62  
% 14.39/6.62  
% 14.39/6.62  %Background operators:
% 14.39/6.62  
% 14.39/6.62  
% 14.39/6.62  %Foreground operators:
% 14.39/6.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.39/6.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.39/6.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.39/6.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.39/6.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.39/6.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.39/6.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.39/6.62  tff('#skF_5', type, '#skF_5': $i).
% 14.39/6.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.39/6.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.39/6.62  tff('#skF_2', type, '#skF_2': $i).
% 14.39/6.62  tff('#skF_3', type, '#skF_3': $i).
% 14.39/6.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.39/6.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.39/6.62  tff('#skF_4', type, '#skF_4': $i).
% 14.39/6.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.39/6.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.39/6.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.39/6.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.39/6.62  
% 14.51/6.63  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 14.51/6.63  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.51/6.63  tff(f_73, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 14.51/6.63  tff(f_83, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 14.51/6.63  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 14.51/6.63  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.51/6.63  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.51/6.63  tff(f_95, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.51/6.63  tff(f_100, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 14.51/6.63  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.51/6.63  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 14.51/6.63  tff(f_81, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 14.51/6.63  tff(c_46, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.51/6.63  tff(c_62, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.51/6.63  tff(c_68, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_62])).
% 14.51/6.63  tff(c_1617, plain, (![A_134, C_135, B_136]: (~r1_xboole_0(A_134, C_135) | ~r1_xboole_0(A_134, B_136) | r1_xboole_0(A_134, k2_xboole_0(B_136, C_135)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.51/6.63  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.51/6.63  tff(c_5377, plain, (![B_264, C_265, A_266]: (r1_xboole_0(k2_xboole_0(B_264, C_265), A_266) | ~r1_xboole_0(A_266, C_265) | ~r1_xboole_0(A_266, B_264))), inference(resolution, [status(thm)], [c_1617, c_2])).
% 14.51/6.63  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.51/6.63  tff(c_5399, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5377, c_44])).
% 14.51/6.63  tff(c_5411, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5399])).
% 14.51/6.63  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.51/6.63  tff(c_67, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_26, c_62])).
% 14.51/6.63  tff(c_78, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.51/6.63  tff(c_134, plain, (![B_48, A_49]: (k4_xboole_0(B_48, k4_xboole_0(A_49, B_48))=B_48)), inference(resolution, [status(thm)], [c_67, c_78])).
% 14.51/6.63  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.51/6.63  tff(c_149, plain, (![B_48]: (r1_tarski(B_48, B_48))), inference(superposition, [status(thm), theory('equality')], [c_134, c_14])).
% 14.51/6.63  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.51/6.63  tff(c_92, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_68, c_78])).
% 14.51/6.63  tff(c_32, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.51/6.63  tff(c_171, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.51/6.63  tff(c_180, plain, (![A_25]: (k3_tarski(k1_tarski(A_25))=k2_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_32, c_171])).
% 14.51/6.63  tff(c_25261, plain, (![A_585, A_586]: (~r1_xboole_0(A_585, A_586) | ~r1_xboole_0(A_585, A_586) | r1_xboole_0(A_585, k3_tarski(k1_tarski(A_586))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_1617])).
% 14.51/6.63  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.51/6.63  tff(c_25277, plain, (![A_585, A_586]: (k4_xboole_0(A_585, k3_tarski(k1_tarski(A_586)))=A_585 | ~r1_xboole_0(A_585, A_586))), inference(resolution, [status(thm)], [c_25261, c_28])).
% 14.51/6.63  tff(c_246, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k1_tarski(B_64))=A_63 | r2_hidden(B_64, A_63))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.51/6.63  tff(c_261, plain, (![B_64, A_63]: (r1_xboole_0(k1_tarski(B_64), A_63) | r2_hidden(B_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_246, c_67])).
% 14.51/6.63  tff(c_324, plain, (![A_74, B_75, C_76]: (r1_xboole_0(A_74, B_75) | ~r1_xboole_0(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.51/6.63  tff(c_6449, plain, (![A_302, A_303]: (r1_xboole_0(A_302, A_303) | ~r1_xboole_0(A_302, k3_tarski(k1_tarski(A_303))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_324])).
% 14.51/6.63  tff(c_32538, plain, (![B_717, A_718]: (r1_xboole_0(k1_tarski(B_717), A_718) | r2_hidden(B_717, k3_tarski(k1_tarski(A_718))))), inference(resolution, [status(thm)], [c_261, c_6449])).
% 14.51/6.63  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.51/6.63  tff(c_183, plain, (![A_53, B_54]: (r1_xboole_0(A_53, B_54) | k4_xboole_0(A_53, B_54)!=A_53)), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.51/6.63  tff(c_193, plain, (![B_54, A_53]: (r1_xboole_0(B_54, A_53) | k4_xboole_0(A_53, B_54)!=A_53)), inference(resolution, [status(thm)], [c_183, c_2])).
% 14.51/6.63  tff(c_1062, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, B_113) | ~r2_hidden(C_114, A_112))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.51/6.63  tff(c_21827, plain, (![C_517, A_518, B_519]: (~r2_hidden(C_517, A_518) | ~r2_hidden(C_517, B_519) | k4_xboole_0(A_518, B_519)!=A_518)), inference(resolution, [status(thm)], [c_193, c_1062])).
% 14.51/6.63  tff(c_21836, plain, (![B_519]: (~r2_hidden('#skF_5', B_519) | k4_xboole_0('#skF_4', B_519)!='#skF_4')), inference(resolution, [status(thm)], [c_48, c_21827])).
% 14.51/6.63  tff(c_33982, plain, (![A_734]: (k4_xboole_0('#skF_4', k3_tarski(k1_tarski(A_734)))!='#skF_4' | r1_xboole_0(k1_tarski('#skF_5'), A_734))), inference(resolution, [status(thm)], [c_32538, c_21836])).
% 14.51/6.63  tff(c_33991, plain, (![A_735]: (r1_xboole_0(k1_tarski('#skF_5'), A_735) | ~r1_xboole_0('#skF_4', A_735))), inference(superposition, [status(thm), theory('equality')], [c_25277, c_33982])).
% 14.51/6.63  tff(c_25960, plain, (![A_616, A_617]: (k4_xboole_0(A_616, k3_tarski(k1_tarski(A_617)))=A_616 | ~r1_xboole_0(A_616, A_617))), inference(resolution, [status(thm)], [c_25261, c_28])).
% 14.51/6.63  tff(c_348, plain, (![A_77, B_78, C_79]: (r1_xboole_0(k4_xboole_0(A_77, k2_xboole_0(B_78, C_79)), B_78))), inference(resolution, [status(thm)], [c_26, c_324])).
% 14.51/6.63  tff(c_364, plain, (![B_80, A_81, C_82]: (r1_xboole_0(B_80, k4_xboole_0(A_81, k2_xboole_0(B_80, C_82))))), inference(resolution, [status(thm)], [c_348, c_2])).
% 14.51/6.63  tff(c_7800, plain, (![B_347, A_348, C_349]: (k4_xboole_0(B_347, k4_xboole_0(A_348, k2_xboole_0(B_347, C_349)))=B_347)), inference(resolution, [status(thm)], [c_364, c_28])).
% 14.51/6.63  tff(c_8127, plain, (![A_25, A_348]: (k4_xboole_0(A_25, k4_xboole_0(A_348, k3_tarski(k1_tarski(A_25))))=A_25)), inference(superposition, [status(thm), theory('equality')], [c_180, c_7800])).
% 14.51/6.63  tff(c_26140, plain, (![A_617, A_616]: (k4_xboole_0(A_617, A_616)=A_617 | ~r1_xboole_0(A_616, A_617))), inference(superposition, [status(thm), theory('equality')], [c_25960, c_8127])).
% 14.51/6.63  tff(c_34187, plain, (![A_741]: (k4_xboole_0(A_741, k1_tarski('#skF_5'))=A_741 | ~r1_xboole_0('#skF_4', A_741))), inference(resolution, [status(thm)], [c_33991, c_26140])).
% 14.51/6.63  tff(c_376, plain, (![A_83, C_84, B_85]: (r1_xboole_0(A_83, C_84) | ~r1_tarski(A_83, k4_xboole_0(B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.51/6.63  tff(c_451, plain, (![B_90, C_91, B_92]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_90, C_91), B_92), C_91))), inference(resolution, [status(thm)], [c_14, c_376])).
% 14.51/6.63  tff(c_507, plain, (![B_94]: (r1_xboole_0(k4_xboole_0('#skF_3', B_94), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_451])).
% 14.51/6.63  tff(c_523, plain, (![B_94]: (k4_xboole_0(k4_xboole_0('#skF_3', B_94), '#skF_4')=k4_xboole_0('#skF_3', B_94))), inference(resolution, [status(thm)], [c_507, c_28])).
% 14.51/6.63  tff(c_34464, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))=k4_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34187, c_523])).
% 14.51/6.63  tff(c_34907, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_92, c_34464])).
% 14.51/6.63  tff(c_91, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_67, c_78])).
% 14.51/6.63  tff(c_10178, plain, (![A_367, A_368, B_369]: (r1_xboole_0(A_367, k4_xboole_0(A_368, B_369)) | ~r1_tarski(A_367, B_369))), inference(superposition, [status(thm), theory('equality')], [c_91, c_376])).
% 14.51/6.63  tff(c_10254, plain, (![A_368, B_369, A_367]: (r1_xboole_0(k4_xboole_0(A_368, B_369), A_367) | ~r1_tarski(A_367, B_369))), inference(resolution, [status(thm)], [c_10178, c_2])).
% 14.51/6.63  tff(c_39911, plain, (![A_778]: (r1_xboole_0('#skF_3', A_778) | ~r1_tarski(A_778, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34907, c_10254])).
% 14.51/6.63  tff(c_39981, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_39911])).
% 14.51/6.63  tff(c_24, plain, (![A_18, B_19, C_20]: (~r1_xboole_0(A_18, k3_xboole_0(B_19, C_20)) | ~r1_tarski(A_18, C_20) | r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.51/6.63  tff(c_39989, plain, (~r1_tarski('#skF_3', '#skF_3') | r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_39981, c_24])).
% 14.51/6.63  tff(c_40000, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_39989])).
% 14.51/6.63  tff(c_40002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5411, c_40000])).
% 14.51/6.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.51/6.63  
% 14.51/6.63  Inference rules
% 14.51/6.63  ----------------------
% 14.51/6.63  #Ref     : 0
% 14.51/6.63  #Sup     : 10037
% 14.51/6.63  #Fact    : 0
% 14.51/6.63  #Define  : 0
% 14.51/6.63  #Split   : 4
% 14.51/6.63  #Chain   : 0
% 14.51/6.63  #Close   : 0
% 14.51/6.63  
% 14.51/6.63  Ordering : KBO
% 14.51/6.63  
% 14.51/6.63  Simplification rules
% 14.51/6.63  ----------------------
% 14.51/6.63  #Subsume      : 1250
% 14.51/6.63  #Demod        : 5962
% 14.51/6.63  #Tautology    : 5055
% 14.51/6.63  #SimpNegUnit  : 10
% 14.51/6.63  #BackRed      : 14
% 14.51/6.63  
% 14.51/6.63  #Partial instantiations: 0
% 14.51/6.63  #Strategies tried      : 1
% 14.51/6.63  
% 14.51/6.63  Timing (in seconds)
% 14.51/6.63  ----------------------
% 14.51/6.64  Preprocessing        : 0.31
% 14.51/6.64  Parsing              : 0.16
% 14.51/6.64  CNF conversion       : 0.02
% 14.51/6.64  Main loop            : 5.56
% 14.51/6.64  Inferencing          : 0.96
% 14.51/6.64  Reduction            : 2.75
% 14.51/6.64  Demodulation         : 2.32
% 14.51/6.64  BG Simplification    : 0.10
% 14.51/6.64  Subsumption          : 1.42
% 14.51/6.64  Abstraction          : 0.13
% 14.51/6.64  MUC search           : 0.00
% 14.51/6.64  Cooper               : 0.00
% 14.51/6.64  Total                : 5.91
% 14.51/6.64  Index Insertion      : 0.00
% 14.51/6.64  Index Deletion       : 0.00
% 14.51/6.64  Index Matching       : 0.00
% 14.51/6.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
