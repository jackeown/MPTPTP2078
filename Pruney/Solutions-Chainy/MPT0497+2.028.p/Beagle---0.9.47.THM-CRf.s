%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_24,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_90,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [C_59] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_90])).

tff(c_95,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_93])).

tff(c_116,plain,(
    ! [B_66,A_67] :
      ( k3_xboole_0(k1_relat_1(B_66),A_67) = k1_relat_1(k7_relat_1(B_66,A_67))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_128,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_85])).

tff(c_140,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_164,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | r2_hidden(k4_tarski('#skF_2'(A_78),'#skF_3'(A_78)),A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_39,C_41,B_40] :
      ( r2_hidden(A_39,k1_relat_1(C_41))
      | ~ r2_hidden(k4_tarski(A_39,B_40),C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_183,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_2'(A_79),k1_relat_1(A_79))
      | k1_xboole_0 = A_79
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_164,c_28])).

tff(c_186,plain,
    ( r2_hidden('#skF_2'(k7_relat_1('#skF_5','#skF_4')),k1_xboole_0)
    | k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_183])).

tff(c_190,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_95,c_186])).

tff(c_194,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_190])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_194])).

tff(c_199,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_199])).

tff(c_203,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_229,plain,(
    ! [B_86,A_87] :
      ( k3_xboole_0(k1_relat_1(B_86),A_87) = k1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_202,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_207,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_238,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_207])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_203,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:46:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.21/1.26  
% 2.21/1.26  %Foreground sorts:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Background operators:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Foreground operators:
% 2.21/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.26  
% 2.21/1.27  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.21/1.27  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.21/1.27  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.21/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.21/1.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.21/1.27  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.21/1.27  tff(f_77, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 2.21/1.27  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.21/1.27  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.27  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.27  tff(c_40, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.27  tff(c_80, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.21/1.27  tff(c_24, plain, (![A_37, B_38]: (v1_relat_1(k7_relat_1(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.27  tff(c_46, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.27  tff(c_81, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 2.21/1.27  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.27  tff(c_85, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.21/1.27  tff(c_90, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.27  tff(c_93, plain, (![C_59]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_85, c_90])).
% 2.21/1.27  tff(c_95, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_93])).
% 2.21/1.27  tff(c_116, plain, (![B_66, A_67]: (k3_xboole_0(k1_relat_1(B_66), A_67)=k1_relat_1(k7_relat_1(B_66, A_67)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.21/1.27  tff(c_128, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_116, c_85])).
% 2.21/1.27  tff(c_140, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128])).
% 2.21/1.27  tff(c_164, plain, (![A_78]: (k1_xboole_0=A_78 | r2_hidden(k4_tarski('#skF_2'(A_78), '#skF_3'(A_78)), A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.27  tff(c_28, plain, (![A_39, C_41, B_40]: (r2_hidden(A_39, k1_relat_1(C_41)) | ~r2_hidden(k4_tarski(A_39, B_40), C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.27  tff(c_183, plain, (![A_79]: (r2_hidden('#skF_2'(A_79), k1_relat_1(A_79)) | k1_xboole_0=A_79 | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_164, c_28])).
% 2.21/1.27  tff(c_186, plain, (r2_hidden('#skF_2'(k7_relat_1('#skF_5', '#skF_4')), k1_xboole_0) | k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_183])).
% 2.21/1.27  tff(c_190, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_95, c_186])).
% 2.21/1.27  tff(c_194, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_190])).
% 2.21/1.27  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_194])).
% 2.21/1.27  tff(c_199, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.21/1.27  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_199])).
% 2.21/1.27  tff(c_203, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.21/1.27  tff(c_229, plain, (![B_86, A_87]: (k3_xboole_0(k1_relat_1(B_86), A_87)=k1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.21/1.27  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.27  tff(c_202, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.21/1.27  tff(c_207, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_202])).
% 2.21/1.27  tff(c_238, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_229, c_207])).
% 2.21/1.27  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_203, c_238])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 47
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 3
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.27  Ordering : KBO
% 2.21/1.27  
% 2.21/1.27  Simplification rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Subsume      : 3
% 2.21/1.27  #Demod        : 11
% 2.21/1.27  #Tautology    : 30
% 2.21/1.27  #SimpNegUnit  : 5
% 2.21/1.27  #BackRed      : 0
% 2.21/1.27  
% 2.21/1.27  #Partial instantiations: 0
% 2.21/1.27  #Strategies tried      : 1
% 2.21/1.27  
% 2.21/1.27  Timing (in seconds)
% 2.21/1.27  ----------------------
% 2.21/1.28  Preprocessing        : 0.33
% 2.21/1.28  Parsing              : 0.17
% 2.21/1.28  CNF conversion       : 0.02
% 2.21/1.28  Main loop            : 0.17
% 2.21/1.28  Inferencing          : 0.07
% 2.21/1.28  Reduction            : 0.05
% 2.21/1.28  Demodulation         : 0.03
% 2.21/1.28  BG Simplification    : 0.01
% 2.21/1.28  Subsumption          : 0.02
% 2.21/1.28  Abstraction          : 0.01
% 2.21/1.28  MUC search           : 0.00
% 2.21/1.28  Cooper               : 0.00
% 2.21/1.28  Total                : 0.52
% 2.21/1.28  Index Insertion      : 0.00
% 2.21/1.28  Index Deletion       : 0.00
% 2.21/1.28  Index Matching       : 0.00
% 2.21/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
