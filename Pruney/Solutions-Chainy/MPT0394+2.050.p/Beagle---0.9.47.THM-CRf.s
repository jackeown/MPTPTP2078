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
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 125 expanded)
%              Number of equality atoms :   47 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,B_61)
      | ~ r2_hidden(C_62,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_162])).

tff(c_204,plain,(
    ! [A_68] : r1_xboole_0(A_68,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ! [A_70] : k4_xboole_0(A_70,k1_xboole_0) = A_70 ),
    inference(resolution,[status(thm)],[c_204,c_16])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_254,plain,(
    ! [A_70] : k4_xboole_0(A_70,A_70) = k3_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_10])).

tff(c_268,plain,(
    ! [A_70] : k4_xboole_0(A_70,A_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_254])).

tff(c_91,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [B_34] : ~ r1_xboole_0(k1_tarski(B_34),k1_tarski(B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    ! [B_34] : k4_xboole_0(k1_tarski(B_34),k1_tarski(B_34)) != k1_tarski(B_34) ),
    inference(resolution,[status(thm)],[c_91,c_34])).

tff(c_315,plain,(
    ! [B_34] : k1_tarski(B_34) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_104])).

tff(c_38,plain,(
    ! [A_37] : k1_setfam_1(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_273,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_enumset1(A_71,B_72,C_73),k1_tarski(D_74)) = k2_enumset1(A_71,B_72,C_73,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_282,plain,(
    ! [A_26,B_27,D_74] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_74)) = k2_enumset1(A_26,A_26,B_27,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_273])).

tff(c_376,plain,(
    ! [A_83,B_84,D_85] : k2_xboole_0(k2_tarski(A_83,B_84),k1_tarski(D_85)) = k1_enumset1(A_83,B_84,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_282])).

tff(c_385,plain,(
    ! [A_25,D_85] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_85)) = k1_enumset1(A_25,A_25,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_376])).

tff(c_388,plain,(
    ! [A_25,D_85] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_85)) = k2_tarski(A_25,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_385])).

tff(c_408,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(k1_setfam_1(A_88),k1_setfam_1(B_89)) = k1_setfam_1(k2_xboole_0(A_88,B_89))
      | k1_xboole_0 = B_89
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_428,plain,(
    ! [A_88,A_37] :
      ( k1_setfam_1(k2_xboole_0(A_88,k1_tarski(A_37))) = k3_xboole_0(k1_setfam_1(A_88),A_37)
      | k1_tarski(A_37) = k1_xboole_0
      | k1_xboole_0 = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_408])).

tff(c_791,plain,(
    ! [A_120,A_121] :
      ( k1_setfam_1(k2_xboole_0(A_120,k1_tarski(A_121))) = k3_xboole_0(k1_setfam_1(A_120),A_121)
      | k1_xboole_0 = A_120 ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_428])).

tff(c_814,plain,(
    ! [A_25,D_85] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_25)),D_85) = k1_setfam_1(k2_tarski(A_25,D_85))
      | k1_tarski(A_25) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_791])).

tff(c_831,plain,(
    ! [A_25,D_85] :
      ( k1_setfam_1(k2_tarski(A_25,D_85)) = k3_xboole_0(A_25,D_85)
      | k1_tarski(A_25) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_814])).

tff(c_832,plain,(
    ! [A_25,D_85] : k1_setfam_1(k2_tarski(A_25,D_85)) = k3_xboole_0(A_25,D_85) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_831])).

tff(c_40,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.37  
% 2.73/1.37  %Foreground sorts:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Background operators:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Foreground operators:
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.37  
% 2.73/1.38  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.73/1.38  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.73/1.38  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.73/1.38  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.73/1.38  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.73/1.38  tff(f_82, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.73/1.38  tff(f_94, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.73/1.38  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.73/1.38  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.73/1.38  tff(f_75, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.73/1.38  tff(f_67, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.73/1.38  tff(f_92, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.73/1.38  tff(f_97, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.73/1.38  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.38  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.38  tff(c_162, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, B_61) | ~r2_hidden(C_62, A_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_178, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_162])).
% 2.73/1.38  tff(c_204, plain, (![A_68]: (r1_xboole_0(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_178])).
% 2.73/1.38  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.38  tff(c_244, plain, (![A_70]: (k4_xboole_0(A_70, k1_xboole_0)=A_70)), inference(resolution, [status(thm)], [c_204, c_16])).
% 2.73/1.38  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.38  tff(c_254, plain, (![A_70]: (k4_xboole_0(A_70, A_70)=k3_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_10])).
% 2.73/1.38  tff(c_268, plain, (![A_70]: (k4_xboole_0(A_70, A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_254])).
% 2.73/1.38  tff(c_91, plain, (![A_47, B_48]: (r1_xboole_0(A_47, B_48) | k4_xboole_0(A_47, B_48)!=A_47)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.38  tff(c_34, plain, (![B_34]: (~r1_xboole_0(k1_tarski(B_34), k1_tarski(B_34)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.38  tff(c_104, plain, (![B_34]: (k4_xboole_0(k1_tarski(B_34), k1_tarski(B_34))!=k1_tarski(B_34))), inference(resolution, [status(thm)], [c_91, c_34])).
% 2.73/1.38  tff(c_315, plain, (![B_34]: (k1_tarski(B_34)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_268, c_104])).
% 2.73/1.38  tff(c_38, plain, (![A_37]: (k1_setfam_1(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.73/1.38  tff(c_28, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.73/1.38  tff(c_26, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.73/1.38  tff(c_30, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.38  tff(c_273, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_enumset1(A_71, B_72, C_73), k1_tarski(D_74))=k2_enumset1(A_71, B_72, C_73, D_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.38  tff(c_282, plain, (![A_26, B_27, D_74]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_74))=k2_enumset1(A_26, A_26, B_27, D_74))), inference(superposition, [status(thm), theory('equality')], [c_28, c_273])).
% 2.73/1.39  tff(c_376, plain, (![A_83, B_84, D_85]: (k2_xboole_0(k2_tarski(A_83, B_84), k1_tarski(D_85))=k1_enumset1(A_83, B_84, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_282])).
% 2.73/1.39  tff(c_385, plain, (![A_25, D_85]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_85))=k1_enumset1(A_25, A_25, D_85))), inference(superposition, [status(thm), theory('equality')], [c_26, c_376])).
% 2.73/1.39  tff(c_388, plain, (![A_25, D_85]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_85))=k2_tarski(A_25, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_385])).
% 2.73/1.39  tff(c_408, plain, (![A_88, B_89]: (k3_xboole_0(k1_setfam_1(A_88), k1_setfam_1(B_89))=k1_setfam_1(k2_xboole_0(A_88, B_89)) | k1_xboole_0=B_89 | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.73/1.39  tff(c_428, plain, (![A_88, A_37]: (k1_setfam_1(k2_xboole_0(A_88, k1_tarski(A_37)))=k3_xboole_0(k1_setfam_1(A_88), A_37) | k1_tarski(A_37)=k1_xboole_0 | k1_xboole_0=A_88)), inference(superposition, [status(thm), theory('equality')], [c_38, c_408])).
% 2.73/1.39  tff(c_791, plain, (![A_120, A_121]: (k1_setfam_1(k2_xboole_0(A_120, k1_tarski(A_121)))=k3_xboole_0(k1_setfam_1(A_120), A_121) | k1_xboole_0=A_120)), inference(negUnitSimplification, [status(thm)], [c_315, c_428])).
% 2.73/1.39  tff(c_814, plain, (![A_25, D_85]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_25)), D_85)=k1_setfam_1(k2_tarski(A_25, D_85)) | k1_tarski(A_25)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_388, c_791])).
% 2.73/1.39  tff(c_831, plain, (![A_25, D_85]: (k1_setfam_1(k2_tarski(A_25, D_85))=k3_xboole_0(A_25, D_85) | k1_tarski(A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_814])).
% 2.73/1.39  tff(c_832, plain, (![A_25, D_85]: (k1_setfam_1(k2_tarski(A_25, D_85))=k3_xboole_0(A_25, D_85))), inference(negUnitSimplification, [status(thm)], [c_315, c_831])).
% 2.73/1.39  tff(c_40, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.39  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_40])).
% 2.73/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.39  
% 2.73/1.39  Inference rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Ref     : 0
% 2.73/1.39  #Sup     : 188
% 2.73/1.39  #Fact    : 0
% 2.73/1.39  #Define  : 0
% 2.73/1.39  #Split   : 0
% 2.73/1.39  #Chain   : 0
% 2.73/1.39  #Close   : 0
% 2.73/1.39  
% 2.73/1.39  Ordering : KBO
% 2.73/1.39  
% 2.73/1.39  Simplification rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Subsume      : 8
% 2.73/1.39  #Demod        : 72
% 2.73/1.39  #Tautology    : 128
% 2.73/1.39  #SimpNegUnit  : 8
% 2.73/1.39  #BackRed      : 2
% 2.73/1.39  
% 2.73/1.39  #Partial instantiations: 0
% 2.73/1.39  #Strategies tried      : 1
% 2.73/1.39  
% 2.73/1.39  Timing (in seconds)
% 2.73/1.39  ----------------------
% 2.73/1.39  Preprocessing        : 0.31
% 2.73/1.39  Parsing              : 0.16
% 2.73/1.39  CNF conversion       : 0.02
% 2.73/1.39  Main loop            : 0.32
% 2.73/1.39  Inferencing          : 0.13
% 2.73/1.39  Reduction            : 0.10
% 2.73/1.39  Demodulation         : 0.08
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.05
% 2.73/1.39  Abstraction          : 0.02
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.66
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
