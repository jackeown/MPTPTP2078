%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   71 (  89 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 121 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_102,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_65,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_52,plain,(
    ! [A_41] :
      ( v1_relat_1(k4_relat_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_30,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_5'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_255,plain,(
    ! [C_90,A_91] :
      ( r2_hidden(k4_tarski(C_90,'#skF_9'(A_91,k1_relat_1(A_91),C_90)),A_91)
      | ~ r2_hidden(C_90,k1_relat_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [A_19,C_60] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_135,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_131])).

tff(c_282,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_255,c_135])).

tff(c_294,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_282])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_294])).

tff(c_302,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_56,plain,(
    ! [A_45] :
      ( k2_relat_1(k4_relat_1(A_45)) = k1_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_301,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_501,plain,(
    ! [A_139,B_140] :
      ( k2_xboole_0(k2_relat_1(A_139),k2_relat_1(B_140)) = k2_relat_1(k2_xboole_0(A_139,B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3090,plain,(
    ! [D_243,B_244,A_245] :
      ( ~ r2_hidden(D_243,k2_relat_1(B_244))
      | r2_hidden(D_243,k2_relat_1(k2_xboole_0(A_245,B_244)))
      | ~ v1_relat_1(B_244)
      | ~ v1_relat_1(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_8])).

tff(c_3132,plain,(
    ! [D_243,A_18] :
      ( ~ r2_hidden(D_243,k2_relat_1(k1_xboole_0))
      | r2_hidden(D_243,k2_relat_1(A_18))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3090])).

tff(c_3244,plain,(
    ! [D_257,A_258] :
      ( ~ r2_hidden(D_257,k2_relat_1(k1_xboole_0))
      | r2_hidden(D_257,k2_relat_1(A_258))
      | ~ v1_relat_1(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3132])).

tff(c_3284,plain,(
    ! [A_258] :
      ( r2_hidden('#skF_5'(k2_relat_1(k1_xboole_0)),k2_relat_1(A_258))
      | ~ v1_relat_1(A_258)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_3244])).

tff(c_3302,plain,(
    ! [A_259] :
      ( r2_hidden('#skF_5'(k2_relat_1(k1_xboole_0)),k2_relat_1(A_259))
      | ~ v1_relat_1(A_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_3284])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3321,plain,(
    ! [A_261] :
      ( ~ v1_xboole_0(k2_relat_1(A_261))
      | ~ v1_relat_1(A_261) ) ),
    inference(resolution,[status(thm)],[c_3302,c_2])).

tff(c_3325,plain,(
    ! [A_262] :
      ( ~ v1_xboole_0(k1_relat_1(A_262))
      | ~ v1_relat_1(k4_relat_1(A_262))
      | ~ v1_relat_1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3321])).

tff(c_3367,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_3325])).

tff(c_3387,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24,c_3367])).

tff(c_3442,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_3387])).

tff(c_3446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.88  
% 4.32/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.88  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_4
% 4.32/1.88  
% 4.32/1.88  %Foreground sorts:
% 4.32/1.88  
% 4.32/1.88  
% 4.32/1.88  %Background operators:
% 4.32/1.88  
% 4.32/1.88  
% 4.32/1.88  %Foreground operators:
% 4.32/1.88  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.32/1.88  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.32/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.32/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.32/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.32/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.32/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.32/1.88  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.32/1.88  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.32/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.32/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.32/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.32/1.88  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.32/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.32/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.88  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.32/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.32/1.88  
% 4.32/1.90  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.32/1.90  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.32/1.90  tff(f_85, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.32/1.90  tff(f_102, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.32/1.90  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.32/1.90  tff(f_81, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.32/1.90  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.32/1.90  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.32/1.90  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.32/1.90  tff(f_98, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.32/1.90  tff(f_65, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.32/1.90  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 4.32/1.90  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.32/1.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.32/1.90  tff(c_24, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.32/1.90  tff(c_62, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.32/1.90  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_62])).
% 4.32/1.90  tff(c_52, plain, (![A_41]: (v1_relat_1(k4_relat_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.32/1.90  tff(c_60, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.32/1.90  tff(c_90, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 4.32/1.90  tff(c_30, plain, (![A_16]: (r2_hidden('#skF_5'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.32/1.90  tff(c_255, plain, (![C_90, A_91]: (r2_hidden(k4_tarski(C_90, '#skF_9'(A_91, k1_relat_1(A_91), C_90)), A_91) | ~r2_hidden(C_90, k1_relat_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.32/1.90  tff(c_36, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.32/1.90  tff(c_34, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.32/1.90  tff(c_120, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.32/1.90  tff(c_131, plain, (![A_19, C_60]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_120])).
% 4.32/1.90  tff(c_135, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_131])).
% 4.32/1.90  tff(c_282, plain, (![C_92]: (~r2_hidden(C_92, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_255, c_135])).
% 4.32/1.90  tff(c_294, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_282])).
% 4.32/1.90  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_294])).
% 4.32/1.90  tff(c_302, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 4.32/1.90  tff(c_56, plain, (![A_45]: (k2_relat_1(k4_relat_1(A_45))=k1_relat_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.32/1.90  tff(c_301, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 4.32/1.90  tff(c_32, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.32/1.90  tff(c_501, plain, (![A_139, B_140]: (k2_xboole_0(k2_relat_1(A_139), k2_relat_1(B_140))=k2_relat_1(k2_xboole_0(A_139, B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.32/1.90  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.32/1.90  tff(c_3090, plain, (![D_243, B_244, A_245]: (~r2_hidden(D_243, k2_relat_1(B_244)) | r2_hidden(D_243, k2_relat_1(k2_xboole_0(A_245, B_244))) | ~v1_relat_1(B_244) | ~v1_relat_1(A_245))), inference(superposition, [status(thm), theory('equality')], [c_501, c_8])).
% 4.32/1.90  tff(c_3132, plain, (![D_243, A_18]: (~r2_hidden(D_243, k2_relat_1(k1_xboole_0)) | r2_hidden(D_243, k2_relat_1(A_18)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3090])).
% 4.32/1.90  tff(c_3244, plain, (![D_257, A_258]: (~r2_hidden(D_257, k2_relat_1(k1_xboole_0)) | r2_hidden(D_257, k2_relat_1(A_258)) | ~v1_relat_1(A_258))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3132])).
% 4.32/1.90  tff(c_3284, plain, (![A_258]: (r2_hidden('#skF_5'(k2_relat_1(k1_xboole_0)), k2_relat_1(A_258)) | ~v1_relat_1(A_258) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_3244])).
% 4.32/1.90  tff(c_3302, plain, (![A_259]: (r2_hidden('#skF_5'(k2_relat_1(k1_xboole_0)), k2_relat_1(A_259)) | ~v1_relat_1(A_259))), inference(negUnitSimplification, [status(thm)], [c_301, c_3284])).
% 4.32/1.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.32/1.90  tff(c_3321, plain, (![A_261]: (~v1_xboole_0(k2_relat_1(A_261)) | ~v1_relat_1(A_261))), inference(resolution, [status(thm)], [c_3302, c_2])).
% 4.32/1.90  tff(c_3325, plain, (![A_262]: (~v1_xboole_0(k1_relat_1(A_262)) | ~v1_relat_1(k4_relat_1(A_262)) | ~v1_relat_1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3321])).
% 4.32/1.90  tff(c_3367, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_302, c_3325])).
% 4.32/1.90  tff(c_3387, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24, c_3367])).
% 4.32/1.90  tff(c_3442, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_3387])).
% 4.32/1.90  tff(c_3446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3442])).
% 4.32/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.90  
% 4.32/1.90  Inference rules
% 4.32/1.90  ----------------------
% 4.32/1.90  #Ref     : 0
% 4.32/1.90  #Sup     : 772
% 4.32/1.90  #Fact    : 6
% 4.32/1.90  #Define  : 0
% 4.32/1.90  #Split   : 2
% 4.32/1.90  #Chain   : 0
% 4.32/1.90  #Close   : 0
% 4.32/1.90  
% 4.32/1.90  Ordering : KBO
% 4.32/1.90  
% 4.32/1.90  Simplification rules
% 4.32/1.90  ----------------------
% 4.32/1.90  #Subsume      : 147
% 4.32/1.90  #Demod        : 529
% 4.32/1.90  #Tautology    : 275
% 4.32/1.90  #SimpNegUnit  : 15
% 4.32/1.90  #BackRed      : 0
% 4.32/1.90  
% 4.32/1.90  #Partial instantiations: 0
% 4.32/1.90  #Strategies tried      : 1
% 4.32/1.90  
% 4.32/1.90  Timing (in seconds)
% 4.32/1.90  ----------------------
% 4.32/1.90  Preprocessing        : 0.37
% 4.32/1.90  Parsing              : 0.18
% 4.32/1.90  CNF conversion       : 0.03
% 4.32/1.90  Main loop            : 0.73
% 4.32/1.90  Inferencing          : 0.26
% 4.32/1.90  Reduction            : 0.20
% 4.32/1.90  Demodulation         : 0.14
% 4.32/1.90  BG Simplification    : 0.04
% 4.32/1.90  Subsumption          : 0.18
% 4.32/1.90  Abstraction          : 0.04
% 4.32/1.90  MUC search           : 0.00
% 4.32/1.90  Cooper               : 0.00
% 4.32/1.90  Total                : 1.13
% 4.32/1.90  Index Insertion      : 0.00
% 4.32/1.90  Index Deletion       : 0.00
% 4.32/1.90  Index Matching       : 0.00
% 4.32/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
