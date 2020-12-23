%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 189 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_268,plain,(
    ! [B_76,A_77] :
      ( r1_xboole_0(k1_relat_1(B_76),A_77)
      | k7_relat_1(B_76,A_77) != k1_xboole_0
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_110,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_61,c_110])).

tff(c_120,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_131,plain,(
    k9_relat_1('#skF_5','#skF_4') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_124])).

tff(c_32,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_65,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_32])).

tff(c_145,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_65])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_3'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_204,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_3'(A_59,B_60,C_61),k1_relat_1(C_61))
      | ~ r2_hidden(A_59,k9_relat_1(C_61,B_60))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,B_33)
      | ~ r2_hidden(C_34,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [C_34] :
      ( ~ r2_hidden(C_34,'#skF_4')
      | ~ r2_hidden(C_34,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_61,c_75])).

tff(c_210,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden('#skF_3'(A_59,B_60,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_59,k9_relat_1('#skF_5',B_60))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_204,c_78])).

tff(c_215,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_3'(A_62,B_63,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_62,k9_relat_1('#skF_5',B_63)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_210])).

tff(c_219,plain,(
    ! [A_10] :
      ( ~ r2_hidden(A_10,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_215])).

tff(c_223,plain,(
    ! [A_64] : ~ r2_hidden(A_64,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_131,c_219])).

tff(c_239,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_239])).

tff(c_247,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_254,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_32])).

tff(c_276,plain,
    ( k7_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_268,c_254])).

tff(c_281,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_276])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_284,plain,(
    ! [A_83,B_84] :
      ( k2_relat_1(k7_relat_1(A_83,B_84)) != k1_xboole_0
      | k7_relat_1(A_83,B_84) = k1_xboole_0
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_288,plain,(
    ! [B_85,A_86] :
      ( k9_relat_1(B_85,A_86) != k1_xboole_0
      | k7_relat_1(B_85,A_86) = k1_xboole_0
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_284])).

tff(c_290,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_288])).

tff(c_293,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_290])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.24/1.33  
% 2.24/1.33  %Foreground sorts:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Background operators:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Foreground operators:
% 2.24/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.24/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.24/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.33  
% 2.24/1.34  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.24/1.34  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.24/1.34  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.24/1.34  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.24/1.34  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.24/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.24/1.34  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.24/1.34  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.24/1.34  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_268, plain, (![B_76, A_77]: (r1_xboole_0(k1_relat_1(B_76), A_77) | k7_relat_1(B_76, A_77)!=k1_xboole_0 | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.34  tff(c_38, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_61, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 2.24/1.34  tff(c_110, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.34  tff(c_116, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_61, c_110])).
% 2.24/1.34  tff(c_120, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116])).
% 2.24/1.34  tff(c_20, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.24/1.34  tff(c_124, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_120, c_20])).
% 2.24/1.34  tff(c_131, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_124])).
% 2.24/1.34  tff(c_32, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_65, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61, c_32])).
% 2.24/1.34  tff(c_145, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131, c_65])).
% 2.24/1.34  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.34  tff(c_14, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_3'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.34  tff(c_204, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_3'(A_59, B_60, C_61), k1_relat_1(C_61)) | ~r2_hidden(A_59, k9_relat_1(C_61, B_60)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.34  tff(c_75, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, B_33) | ~r2_hidden(C_34, A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.34  tff(c_78, plain, (![C_34]: (~r2_hidden(C_34, '#skF_4') | ~r2_hidden(C_34, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_61, c_75])).
% 2.24/1.34  tff(c_210, plain, (![A_59, B_60]: (~r2_hidden('#skF_3'(A_59, B_60, '#skF_5'), '#skF_4') | ~r2_hidden(A_59, k9_relat_1('#skF_5', B_60)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_204, c_78])).
% 2.24/1.34  tff(c_215, plain, (![A_62, B_63]: (~r2_hidden('#skF_3'(A_62, B_63, '#skF_5'), '#skF_4') | ~r2_hidden(A_62, k9_relat_1('#skF_5', B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_210])).
% 2.24/1.34  tff(c_219, plain, (![A_10]: (~r2_hidden(A_10, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_215])).
% 2.24/1.34  tff(c_223, plain, (![A_64]: (~r2_hidden(A_64, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_131, c_219])).
% 2.24/1.34  tff(c_239, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_223])).
% 2.24/1.34  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_239])).
% 2.24/1.34  tff(c_247, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.24/1.34  tff(c_254, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_32])).
% 2.24/1.34  tff(c_276, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_268, c_254])).
% 2.24/1.34  tff(c_281, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_276])).
% 2.24/1.34  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.34  tff(c_51, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.24/1.34  tff(c_284, plain, (![A_83, B_84]: (k2_relat_1(k7_relat_1(A_83, B_84))!=k1_xboole_0 | k7_relat_1(A_83, B_84)=k1_xboole_0 | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_10, c_51])).
% 2.24/1.34  tff(c_288, plain, (![B_85, A_86]: (k9_relat_1(B_85, A_86)!=k1_xboole_0 | k7_relat_1(B_85, A_86)=k1_xboole_0 | ~v1_relat_1(B_85) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_20, c_284])).
% 2.24/1.34  tff(c_290, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_247, c_288])).
% 2.24/1.34  tff(c_293, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_290])).
% 2.24/1.34  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_293])).
% 2.24/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  Inference rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Ref     : 0
% 2.24/1.34  #Sup     : 50
% 2.24/1.34  #Fact    : 0
% 2.24/1.34  #Define  : 0
% 2.24/1.34  #Split   : 3
% 2.24/1.34  #Chain   : 0
% 2.24/1.34  #Close   : 0
% 2.24/1.34  
% 2.24/1.34  Ordering : KBO
% 2.24/1.34  
% 2.24/1.34  Simplification rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Subsume      : 4
% 2.24/1.34  #Demod        : 19
% 2.24/1.34  #Tautology    : 18
% 2.24/1.34  #SimpNegUnit  : 3
% 2.24/1.34  #BackRed      : 1
% 2.24/1.34  
% 2.24/1.34  #Partial instantiations: 0
% 2.24/1.34  #Strategies tried      : 1
% 2.24/1.34  
% 2.24/1.34  Timing (in seconds)
% 2.24/1.34  ----------------------
% 2.24/1.34  Preprocessing        : 0.29
% 2.24/1.34  Parsing              : 0.16
% 2.24/1.34  CNF conversion       : 0.02
% 2.24/1.34  Main loop            : 0.23
% 2.24/1.34  Inferencing          : 0.10
% 2.24/1.34  Reduction            : 0.06
% 2.24/1.34  Demodulation         : 0.04
% 2.24/1.34  BG Simplification    : 0.01
% 2.24/1.34  Subsumption          : 0.04
% 2.24/1.35  Abstraction          : 0.01
% 2.24/1.35  MUC search           : 0.00
% 2.24/1.35  Cooper               : 0.00
% 2.24/1.35  Total                : 0.55
% 2.24/1.35  Index Insertion      : 0.00
% 2.24/1.35  Index Deletion       : 0.00
% 2.24/1.35  Index Matching       : 0.00
% 2.24/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
