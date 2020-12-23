%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 122 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 186 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8')
    | k7_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    k7_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( k7_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    k3_xboole_0(k1_relat_1('#skF_9'),'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_88,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [C_50] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8')
      | ~ r2_hidden(C_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_88])).

tff(c_93,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_91])).

tff(c_26,plain,(
    ! [A_31,B_32] :
      ( v1_relat_1(k7_relat_1(A_31,B_32))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_105,plain,
    ( k1_relat_1(k7_relat_1('#skF_9','#skF_8')) = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_83])).

tff(c_117,plain,(
    k1_relat_1(k7_relat_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_105])).

tff(c_34,plain,(
    ! [B_37,A_36] :
      ( k3_xboole_0(k1_relat_1(B_37),A_36) = k1_relat_1(k7_relat_1(B_37,A_36))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [A_36] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_8'),A_36)) = k3_xboole_0(k1_xboole_0,A_36)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_34])).

tff(c_129,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_132,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_138,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_165,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | r2_hidden(k4_tarski('#skF_6'(A_60),'#skF_7'(A_60)),A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_180,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_6'(A_61),k1_relat_1(A_61))
      | k1_xboole_0 = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_165,c_16])).

tff(c_186,plain,
    ( r2_hidden('#skF_6'(k7_relat_1('#skF_9','#skF_8')),k1_xboole_0)
    | k7_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_180])).

tff(c_191,plain,
    ( r2_hidden('#skF_6'(k7_relat_1('#skF_9','#skF_8')),k1_xboole_0)
    | k7_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_186])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93,c_191])).

tff(c_194,plain,(
    k7_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_194])).

tff(c_198,plain,(
    k7_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_221,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(k1_relat_1(B_70),A_71) = k1_relat_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_197,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_202,plain,(
    k3_xboole_0(k1_relat_1('#skF_9'),'#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_233,plain,
    ( k1_relat_1(k7_relat_1('#skF_9','#skF_8')) != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_202])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_198,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#skF_7', type, '#skF_7': $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.98/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.98/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.22  tff('#skF_9', type, '#skF_9': $i).
% 1.98/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.22  tff('#skF_6', type, '#skF_6': $i > $i).
% 1.98/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.98/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.22  
% 1.98/1.23  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.98/1.23  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.98/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.23  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.98/1.23  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.98/1.23  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.98/1.23  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.98/1.23  tff(c_36, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.98/1.23  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.23  tff(c_38, plain, (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8') | k7_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.98/1.23  tff(c_78, plain, (k7_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 1.98/1.23  tff(c_44, plain, (k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.98/1.23  tff(c_79, plain, (r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 1.98/1.23  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.23  tff(c_83, plain, (k3_xboole_0(k1_relat_1('#skF_9'), '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_2])).
% 1.98/1.23  tff(c_88, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.23  tff(c_91, plain, (![C_50]: (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8') | ~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_88])).
% 1.98/1.23  tff(c_93, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_91])).
% 1.98/1.23  tff(c_26, plain, (![A_31, B_32]: (v1_relat_1(k7_relat_1(A_31, B_32)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.23  tff(c_96, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_105, plain, (k1_relat_1(k7_relat_1('#skF_9', '#skF_8'))=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_96, c_83])).
% 1.98/1.23  tff(c_117, plain, (k1_relat_1(k7_relat_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_105])).
% 1.98/1.23  tff(c_34, plain, (![B_37, A_36]: (k3_xboole_0(k1_relat_1(B_37), A_36)=k1_relat_1(k7_relat_1(B_37, A_36)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_124, plain, (![A_36]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_9', '#skF_8'), A_36))=k3_xboole_0(k1_xboole_0, A_36) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_117, c_34])).
% 1.98/1.23  tff(c_129, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_124])).
% 1.98/1.23  tff(c_132, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_129])).
% 1.98/1.23  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_132])).
% 1.98/1.23  tff(c_138, plain, (v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_124])).
% 1.98/1.23  tff(c_165, plain, (![A_60]: (k1_xboole_0=A_60 | r2_hidden(k4_tarski('#skF_6'(A_60), '#skF_7'(A_60)), A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.23  tff(c_16, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.98/1.23  tff(c_180, plain, (![A_61]: (r2_hidden('#skF_6'(A_61), k1_relat_1(A_61)) | k1_xboole_0=A_61 | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_165, c_16])).
% 1.98/1.23  tff(c_186, plain, (r2_hidden('#skF_6'(k7_relat_1('#skF_9', '#skF_8')), k1_xboole_0) | k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_180])).
% 1.98/1.23  tff(c_191, plain, (r2_hidden('#skF_6'(k7_relat_1('#skF_9', '#skF_8')), k1_xboole_0) | k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_186])).
% 1.98/1.23  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_93, c_191])).
% 1.98/1.23  tff(c_194, plain, (k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 1.98/1.23  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_194])).
% 1.98/1.23  tff(c_198, plain, (k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 1.98/1.23  tff(c_221, plain, (![B_70, A_71]: (k3_xboole_0(k1_relat_1(B_70), A_71)=k1_relat_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.23  tff(c_197, plain, (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 1.98/1.23  tff(c_202, plain, (k3_xboole_0(k1_relat_1('#skF_9'), '#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_197])).
% 1.98/1.23  tff(c_233, plain, (k1_relat_1(k7_relat_1('#skF_9', '#skF_8'))!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_221, c_202])).
% 1.98/1.23  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_198, c_233])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 46
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 4
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 2
% 1.98/1.23  #Demod        : 12
% 1.98/1.23  #Tautology    : 27
% 1.98/1.23  #SimpNegUnit  : 4
% 1.98/1.23  #BackRed      : 0
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 1.98/1.23  Preprocessing        : 0.31
% 1.98/1.23  Parsing              : 0.16
% 2.18/1.23  CNF conversion       : 0.02
% 2.18/1.23  Main loop            : 0.16
% 2.18/1.23  Inferencing          : 0.06
% 2.18/1.23  Reduction            : 0.05
% 2.18/1.23  Demodulation         : 0.03
% 2.18/1.23  BG Simplification    : 0.01
% 2.18/1.23  Subsumption          : 0.02
% 2.18/1.23  Abstraction          : 0.01
% 2.18/1.23  MUC search           : 0.00
% 2.18/1.23  Cooper               : 0.00
% 2.18/1.23  Total                : 0.49
% 2.18/1.23  Index Insertion      : 0.00
% 2.18/1.23  Index Deletion       : 0.00
% 2.18/1.23  Index Matching       : 0.00
% 2.18/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
