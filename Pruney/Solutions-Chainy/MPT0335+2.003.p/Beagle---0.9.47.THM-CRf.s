%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 38.18s
% Output     : CNFRefutation 38.18s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 286 expanded)
%              Number of leaves         :   28 ( 111 expanded)
%              Depth                    :   20
%              Number of atoms          :  109 ( 559 expanded)
%              Number of equality atoms :   26 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    k3_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_231,plain,(
    ! [D_61,B_62,A_63] :
      ( r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k3_xboole_0(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_277,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,'#skF_10')
      | ~ r2_hidden(D_68,k1_tarski('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_231])).

tff(c_286,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_11'),B_4),'#skF_10')
      | r1_tarski(k1_tarski('#skF_11'),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_277])).

tff(c_393,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_419,plain,(
    ! [A_3,B_4,B_75] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_75)
      | ~ r1_tarski(A_3,B_75)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_652,plain,(
    ! [D_98,A_99,B_100] :
      ( r2_hidden(D_98,k3_xboole_0(A_99,B_100))
      | ~ r2_hidden(D_98,B_100)
      | ~ r2_hidden(D_98,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35632,plain,(
    ! [A_28769,A_28770,B_28771] :
      ( r1_tarski(A_28769,k3_xboole_0(A_28770,B_28771))
      | ~ r2_hidden('#skF_1'(A_28769,k3_xboole_0(A_28770,B_28771)),B_28771)
      | ~ r2_hidden('#skF_1'(A_28769,k3_xboole_0(A_28770,B_28771)),A_28770) ) ),
    inference(resolution,[status(thm)],[c_652,c_6])).

tff(c_129108,plain,(
    ! [A_60319,A_60320,B_60321] :
      ( ~ r2_hidden('#skF_1'(A_60319,k3_xboole_0(A_60320,B_60321)),A_60320)
      | ~ r1_tarski(A_60319,B_60321)
      | r1_tarski(A_60319,k3_xboole_0(A_60320,B_60321)) ) ),
    inference(resolution,[status(thm)],[c_419,c_35632])).

tff(c_129663,plain,(
    ! [B_60412] :
      ( ~ r1_tarski(k1_tarski('#skF_11'),B_60412)
      | r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_10',B_60412)) ) ),
    inference(resolution,[status(thm)],[c_286,c_129108])).

tff(c_129800,plain,(
    ! [A_1] :
      ( ~ r1_tarski(k1_tarski('#skF_11'),A_1)
      | r1_tarski(k1_tarski('#skF_11'),k3_xboole_0(A_1,'#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129663])).

tff(c_72,plain,(
    k3_xboole_0('#skF_8','#skF_10') != k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_153,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_160,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_199,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,A_58)
      | ~ r2_hidden(D_57,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1777,plain,(
    ! [A_173,B_174,B_175] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_173,B_174),B_175),A_173)
      | r1_tarski(k3_xboole_0(A_173,B_174),B_175) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_78,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_161,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_78,c_153])).

tff(c_252,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_231])).

tff(c_257,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_3,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_252,c_6])).

tff(c_2095,plain,(
    ! [B_185] : r1_tarski(k3_xboole_0('#skF_8',B_185),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1777,c_257])).

tff(c_2135,plain,(
    ! [B_186] : r1_tarski(k3_xboole_0(B_186,'#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2095])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5932,plain,(
    ! [B_8319] : k3_xboole_0(k3_xboole_0(B_8319,'#skF_8'),'#skF_9') = k3_xboole_0(B_8319,'#skF_8') ),
    inference(resolution,[status(thm)],[c_2135,c_34])).

tff(c_1889,plain,(
    ! [A_179,B_180] : r1_tarski(k3_xboole_0(A_179,B_180),A_179) ),
    inference(resolution,[status(thm)],[c_1777,c_6])).

tff(c_2504,plain,(
    ! [A_196,B_197] : k3_xboole_0(k3_xboole_0(A_196,B_197),A_196) = k3_xboole_0(A_196,B_197) ),
    inference(resolution,[status(thm)],[c_1889,c_34])).

tff(c_2619,plain,(
    ! [A_1,B_197] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_197)) = k3_xboole_0(A_1,B_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2504])).

tff(c_5967,plain,(
    ! [B_8319] : k3_xboole_0(k3_xboole_0(B_8319,'#skF_8'),k3_xboole_0(B_8319,'#skF_8')) = k3_xboole_0(k3_xboole_0(B_8319,'#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_5932,c_2619])).

tff(c_6089,plain,(
    ! [B_8319] : k3_xboole_0('#skF_9',k3_xboole_0(B_8319,'#skF_8')) = k3_xboole_0(B_8319,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_2,c_5967])).

tff(c_2170,plain,(
    ! [B_186] : k3_xboole_0(k3_xboole_0(B_186,'#skF_8'),'#skF_9') = k3_xboole_0(B_186,'#skF_8') ),
    inference(resolution,[status(thm)],[c_2135,c_34])).

tff(c_7852,plain,(
    ! [A_9616,B_9617,B_9618] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_9616,B_9617),B_9618),B_9617)
      | r1_tarski(k3_xboole_0(A_9616,B_9617),B_9618) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_7923,plain,(
    ! [B_186,B_9618] :
      ( r2_hidden('#skF_1'(k3_xboole_0(B_186,'#skF_8'),B_9618),'#skF_9')
      | r1_tarski(k3_xboole_0(k3_xboole_0(B_186,'#skF_8'),'#skF_9'),B_9618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2170,c_7852])).

tff(c_8018,plain,(
    ! [B_186,B_9618] :
      ( r2_hidden('#skF_1'(k3_xboole_0(B_186,'#skF_8'),B_9618),'#skF_9')
      | r1_tarski(k3_xboole_0(B_186,'#skF_8'),B_9618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6089,c_2,c_7923])).

tff(c_219,plain,(
    ! [A_58,B_59,B_4] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_58,B_59),B_4),A_58)
      | r1_tarski(k3_xboole_0(A_58,B_59),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_149677,plain,(
    ! [A_67570,B_67571,A_67572] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_67570,B_67571),k3_xboole_0(A_67572,A_67570)),A_67572)
      | r1_tarski(k3_xboole_0(A_67570,B_67571),k3_xboole_0(A_67572,A_67570)) ) ),
    inference(resolution,[status(thm)],[c_219,c_35632])).

tff(c_150476,plain,(
    ! [B_67663] : r1_tarski(k3_xboole_0(B_67663,'#skF_8'),k3_xboole_0('#skF_9',B_67663)) ),
    inference(resolution,[status(thm)],[c_8018,c_149677])).

tff(c_150652,plain,(
    r1_tarski(k3_xboole_0('#skF_10','#skF_8'),k1_tarski('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_150476])).

tff(c_150707,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_10'),k1_tarski('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_150652])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150758,plain,
    ( k3_xboole_0('#skF_8','#skF_10') = k1_tarski('#skF_11')
    | ~ r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_150707,c_28])).

tff(c_150843,plain,(
    ~ r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_150758])).

tff(c_150875,plain,(
    ~ r1_tarski(k1_tarski('#skF_11'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_129800,c_150843])).

tff(c_74,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_175,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_180,plain,(
    ! [A_18,B_52] :
      ( '#skF_1'(k1_tarski(A_18),B_52) = A_18
      | r1_tarski(k1_tarski(A_18),B_52) ) ),
    inference(resolution,[status(thm)],[c_175,c_36])).

tff(c_150893,plain,(
    '#skF_1'(k1_tarski('#skF_11'),'#skF_8') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_180,c_150875])).

tff(c_150930,plain,
    ( ~ r2_hidden('#skF_11','#skF_8')
    | r1_tarski(k1_tarski('#skF_11'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_150893,c_6])).

tff(c_151009,plain,(
    r1_tarski(k1_tarski('#skF_11'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_150930])).

tff(c_151011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150875,c_151009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:23:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.18/27.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.18/27.23  
% 38.18/27.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.18/27.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 38.18/27.23  
% 38.18/27.23  %Foreground sorts:
% 38.18/27.23  
% 38.18/27.23  
% 38.18/27.23  %Background operators:
% 38.18/27.23  
% 38.18/27.23  
% 38.18/27.23  %Foreground operators:
% 38.18/27.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.18/27.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.18/27.23  tff('#skF_11', type, '#skF_11': $i).
% 38.18/27.23  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 38.18/27.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.18/27.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.18/27.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.18/27.23  tff('#skF_10', type, '#skF_10': $i).
% 38.18/27.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.18/27.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 38.18/27.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.18/27.23  tff('#skF_9', type, '#skF_9': $i).
% 38.18/27.23  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 38.18/27.23  tff('#skF_8', type, '#skF_8': $i).
% 38.18/27.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.18/27.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 38.18/27.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.18/27.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.18/27.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 38.18/27.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 38.18/27.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 38.18/27.23  
% 38.18/27.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 38.18/27.24  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 38.18/27.24  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 38.18/27.24  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 38.18/27.24  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.18/27.24  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.18/27.24  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 38.18/27.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.18/27.24  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.18/27.24  tff(c_76, plain, (k3_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.18/27.24  tff(c_231, plain, (![D_61, B_62, A_63]: (r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k3_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 38.18/27.24  tff(c_277, plain, (![D_68]: (r2_hidden(D_68, '#skF_10') | ~r2_hidden(D_68, k1_tarski('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_231])).
% 38.18/27.24  tff(c_286, plain, (![B_4]: (r2_hidden('#skF_1'(k1_tarski('#skF_11'), B_4), '#skF_10') | r1_tarski(k1_tarski('#skF_11'), B_4))), inference(resolution, [status(thm)], [c_8, c_277])).
% 38.18/27.24  tff(c_393, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.18/27.24  tff(c_419, plain, (![A_3, B_4, B_75]: (r2_hidden('#skF_1'(A_3, B_4), B_75) | ~r1_tarski(A_3, B_75) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_393])).
% 38.18/27.24  tff(c_652, plain, (![D_98, A_99, B_100]: (r2_hidden(D_98, k3_xboole_0(A_99, B_100)) | ~r2_hidden(D_98, B_100) | ~r2_hidden(D_98, A_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 38.18/27.24  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.18/27.24  tff(c_35632, plain, (![A_28769, A_28770, B_28771]: (r1_tarski(A_28769, k3_xboole_0(A_28770, B_28771)) | ~r2_hidden('#skF_1'(A_28769, k3_xboole_0(A_28770, B_28771)), B_28771) | ~r2_hidden('#skF_1'(A_28769, k3_xboole_0(A_28770, B_28771)), A_28770))), inference(resolution, [status(thm)], [c_652, c_6])).
% 38.18/27.24  tff(c_129108, plain, (![A_60319, A_60320, B_60321]: (~r2_hidden('#skF_1'(A_60319, k3_xboole_0(A_60320, B_60321)), A_60320) | ~r1_tarski(A_60319, B_60321) | r1_tarski(A_60319, k3_xboole_0(A_60320, B_60321)))), inference(resolution, [status(thm)], [c_419, c_35632])).
% 38.18/27.24  tff(c_129663, plain, (![B_60412]: (~r1_tarski(k1_tarski('#skF_11'), B_60412) | r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_10', B_60412)))), inference(resolution, [status(thm)], [c_286, c_129108])).
% 38.18/27.24  tff(c_129800, plain, (![A_1]: (~r1_tarski(k1_tarski('#skF_11'), A_1) | r1_tarski(k1_tarski('#skF_11'), k3_xboole_0(A_1, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_129663])).
% 38.18/27.24  tff(c_72, plain, (k3_xboole_0('#skF_8', '#skF_10')!=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.18/27.24  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 38.18/27.24  tff(c_153, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.18/27.24  tff(c_160, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_153])).
% 38.18/27.24  tff(c_199, plain, (![D_57, A_58, B_59]: (r2_hidden(D_57, A_58) | ~r2_hidden(D_57, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 38.18/27.24  tff(c_1777, plain, (![A_173, B_174, B_175]: (r2_hidden('#skF_1'(k3_xboole_0(A_173, B_174), B_175), A_173) | r1_tarski(k3_xboole_0(A_173, B_174), B_175))), inference(resolution, [status(thm)], [c_8, c_199])).
% 38.18/27.24  tff(c_78, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.18/27.24  tff(c_161, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_78, c_153])).
% 38.18/27.24  tff(c_252, plain, (![D_64]: (r2_hidden(D_64, '#skF_9') | ~r2_hidden(D_64, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_231])).
% 38.18/27.24  tff(c_257, plain, (![A_3]: (r1_tarski(A_3, '#skF_9') | ~r2_hidden('#skF_1'(A_3, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_252, c_6])).
% 38.18/27.24  tff(c_2095, plain, (![B_185]: (r1_tarski(k3_xboole_0('#skF_8', B_185), '#skF_9'))), inference(resolution, [status(thm)], [c_1777, c_257])).
% 38.18/27.24  tff(c_2135, plain, (![B_186]: (r1_tarski(k3_xboole_0(B_186, '#skF_8'), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2095])).
% 38.18/27.24  tff(c_34, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.18/27.24  tff(c_5932, plain, (![B_8319]: (k3_xboole_0(k3_xboole_0(B_8319, '#skF_8'), '#skF_9')=k3_xboole_0(B_8319, '#skF_8'))), inference(resolution, [status(thm)], [c_2135, c_34])).
% 38.18/27.24  tff(c_1889, plain, (![A_179, B_180]: (r1_tarski(k3_xboole_0(A_179, B_180), A_179))), inference(resolution, [status(thm)], [c_1777, c_6])).
% 38.18/27.24  tff(c_2504, plain, (![A_196, B_197]: (k3_xboole_0(k3_xboole_0(A_196, B_197), A_196)=k3_xboole_0(A_196, B_197))), inference(resolution, [status(thm)], [c_1889, c_34])).
% 38.18/27.24  tff(c_2619, plain, (![A_1, B_197]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_197))=k3_xboole_0(A_1, B_197))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2504])).
% 38.18/27.24  tff(c_5967, plain, (![B_8319]: (k3_xboole_0(k3_xboole_0(B_8319, '#skF_8'), k3_xboole_0(B_8319, '#skF_8'))=k3_xboole_0(k3_xboole_0(B_8319, '#skF_8'), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5932, c_2619])).
% 38.18/27.24  tff(c_6089, plain, (![B_8319]: (k3_xboole_0('#skF_9', k3_xboole_0(B_8319, '#skF_8'))=k3_xboole_0(B_8319, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_2, c_5967])).
% 38.18/27.24  tff(c_2170, plain, (![B_186]: (k3_xboole_0(k3_xboole_0(B_186, '#skF_8'), '#skF_9')=k3_xboole_0(B_186, '#skF_8'))), inference(resolution, [status(thm)], [c_2135, c_34])).
% 38.18/27.24  tff(c_7852, plain, (![A_9616, B_9617, B_9618]: (r2_hidden('#skF_1'(k3_xboole_0(A_9616, B_9617), B_9618), B_9617) | r1_tarski(k3_xboole_0(A_9616, B_9617), B_9618))), inference(resolution, [status(thm)], [c_8, c_231])).
% 38.18/27.24  tff(c_7923, plain, (![B_186, B_9618]: (r2_hidden('#skF_1'(k3_xboole_0(B_186, '#skF_8'), B_9618), '#skF_9') | r1_tarski(k3_xboole_0(k3_xboole_0(B_186, '#skF_8'), '#skF_9'), B_9618))), inference(superposition, [status(thm), theory('equality')], [c_2170, c_7852])).
% 38.18/27.24  tff(c_8018, plain, (![B_186, B_9618]: (r2_hidden('#skF_1'(k3_xboole_0(B_186, '#skF_8'), B_9618), '#skF_9') | r1_tarski(k3_xboole_0(B_186, '#skF_8'), B_9618))), inference(demodulation, [status(thm), theory('equality')], [c_6089, c_2, c_7923])).
% 38.18/27.24  tff(c_219, plain, (![A_58, B_59, B_4]: (r2_hidden('#skF_1'(k3_xboole_0(A_58, B_59), B_4), A_58) | r1_tarski(k3_xboole_0(A_58, B_59), B_4))), inference(resolution, [status(thm)], [c_8, c_199])).
% 38.18/27.24  tff(c_149677, plain, (![A_67570, B_67571, A_67572]: (~r2_hidden('#skF_1'(k3_xboole_0(A_67570, B_67571), k3_xboole_0(A_67572, A_67570)), A_67572) | r1_tarski(k3_xboole_0(A_67570, B_67571), k3_xboole_0(A_67572, A_67570)))), inference(resolution, [status(thm)], [c_219, c_35632])).
% 38.18/27.24  tff(c_150476, plain, (![B_67663]: (r1_tarski(k3_xboole_0(B_67663, '#skF_8'), k3_xboole_0('#skF_9', B_67663)))), inference(resolution, [status(thm)], [c_8018, c_149677])).
% 38.18/27.24  tff(c_150652, plain, (r1_tarski(k3_xboole_0('#skF_10', '#skF_8'), k1_tarski('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_150476])).
% 38.18/27.24  tff(c_150707, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_10'), k1_tarski('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_150652])).
% 38.18/27.24  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 38.18/27.24  tff(c_150758, plain, (k3_xboole_0('#skF_8', '#skF_10')=k1_tarski('#skF_11') | ~r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_150707, c_28])).
% 38.18/27.24  tff(c_150843, plain, (~r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_72, c_150758])).
% 38.18/27.24  tff(c_150875, plain, (~r1_tarski(k1_tarski('#skF_11'), '#skF_8')), inference(resolution, [status(thm)], [c_129800, c_150843])).
% 38.18/27.24  tff(c_74, plain, (r2_hidden('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.18/27.24  tff(c_175, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.18/27.24  tff(c_36, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 38.18/27.24  tff(c_180, plain, (![A_18, B_52]: ('#skF_1'(k1_tarski(A_18), B_52)=A_18 | r1_tarski(k1_tarski(A_18), B_52))), inference(resolution, [status(thm)], [c_175, c_36])).
% 38.18/27.24  tff(c_150893, plain, ('#skF_1'(k1_tarski('#skF_11'), '#skF_8')='#skF_11'), inference(resolution, [status(thm)], [c_180, c_150875])).
% 38.18/27.24  tff(c_150930, plain, (~r2_hidden('#skF_11', '#skF_8') | r1_tarski(k1_tarski('#skF_11'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_150893, c_6])).
% 38.18/27.24  tff(c_151009, plain, (r1_tarski(k1_tarski('#skF_11'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_150930])).
% 38.18/27.24  tff(c_151011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150875, c_151009])).
% 38.18/27.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.18/27.24  
% 38.18/27.24  Inference rules
% 38.18/27.24  ----------------------
% 38.18/27.24  #Ref     : 0
% 38.18/27.24  #Sup     : 31865
% 38.18/27.24  #Fact    : 242
% 38.18/27.24  #Define  : 0
% 38.18/27.24  #Split   : 10
% 38.18/27.24  #Chain   : 0
% 38.18/27.24  #Close   : 0
% 38.18/27.24  
% 38.18/27.24  Ordering : KBO
% 38.18/27.24  
% 38.18/27.24  Simplification rules
% 38.18/27.24  ----------------------
% 38.18/27.24  #Subsume      : 11857
% 38.18/27.24  #Demod        : 17481
% 38.18/27.24  #Tautology    : 7003
% 38.18/27.24  #SimpNegUnit  : 283
% 38.18/27.24  #BackRed      : 1
% 38.18/27.24  
% 38.18/27.24  #Partial instantiations: 35664
% 38.18/27.24  #Strategies tried      : 1
% 38.18/27.24  
% 38.18/27.24  Timing (in seconds)
% 38.18/27.24  ----------------------
% 38.18/27.25  Preprocessing        : 0.32
% 38.18/27.25  Parsing              : 0.17
% 38.18/27.25  CNF conversion       : 0.02
% 38.18/27.25  Main loop            : 26.18
% 38.18/27.25  Inferencing          : 4.37
% 38.18/27.25  Reduction            : 9.36
% 38.18/27.25  Demodulation         : 7.73
% 38.18/27.25  BG Simplification    : 0.49
% 38.18/27.25  Subsumption          : 10.65
% 38.18/27.25  Abstraction          : 0.87
% 38.18/27.25  MUC search           : 0.00
% 38.18/27.25  Cooper               : 0.00
% 38.18/27.25  Total                : 26.53
% 38.18/27.25  Index Insertion      : 0.00
% 38.18/27.25  Index Deletion       : 0.00
% 38.18/27.25  Index Matching       : 0.00
% 38.18/27.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
