%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 29.15s
% Output     : CNFRefutation 29.28s
% Verified   : 
% Statistics : Number of formulae       :   68 (  93 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 151 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_58,plain,
    ( k9_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_94,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8')
    | k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_95,plain,(
    k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_193,plain,
    ( k7_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_183])).

tff(c_205,plain,(
    k7_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_193])).

tff(c_40,plain,(
    ! [B_43,A_42] :
      ( k2_relat_1(k7_relat_1(B_43,A_42)) = k9_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_212,plain,
    ( k9_relat_1('#skF_9','#skF_8') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_40])).

tff(c_216,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_212])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_216])).

tff(c_219,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_219])).

tff(c_227,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_234,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_235,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [A_11,C_82] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_245,plain,(
    ! [C_82] : ~ r2_hidden(C_82,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_242])).

tff(c_20,plain,(
    ! [C_32,A_17] :
      ( r2_hidden(k4_tarski(C_32,'#skF_6'(A_17,k1_relat_1(A_17),C_32)),A_17)
      | ~ r2_hidden(C_32,k1_relat_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_986,plain,(
    ! [A_177,C_178,B_179,D_180] :
      ( r2_hidden(A_177,k9_relat_1(C_178,B_179))
      | ~ r2_hidden(D_180,B_179)
      | ~ r2_hidden(k4_tarski(D_180,A_177),C_178)
      | ~ r2_hidden(D_180,k1_relat_1(C_178))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8876,plain,(
    ! [A_400,C_401,B_402,A_403] :
      ( r2_hidden(A_400,k9_relat_1(C_401,B_402))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_403,B_402),A_400),C_401)
      | ~ r2_hidden('#skF_1'(A_403,B_402),k1_relat_1(C_401))
      | ~ v1_relat_1(C_401)
      | r1_xboole_0(A_403,B_402) ) ),
    inference(resolution,[status(thm)],[c_4,c_986])).

tff(c_110623,plain,(
    ! [A_13611,A_13612,B_13613] :
      ( r2_hidden('#skF_6'(A_13611,k1_relat_1(A_13611),'#skF_1'(A_13612,B_13613)),k9_relat_1(A_13611,B_13613))
      | ~ v1_relat_1(A_13611)
      | r1_xboole_0(A_13612,B_13613)
      | ~ r2_hidden('#skF_1'(A_13612,B_13613),k1_relat_1(A_13611)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8876])).

tff(c_111010,plain,(
    ! [A_13612] :
      ( r2_hidden('#skF_6'('#skF_9',k1_relat_1('#skF_9'),'#skF_1'(A_13612,'#skF_8')),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_13612,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_13612,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_110623])).

tff(c_111051,plain,(
    ! [A_13612] :
      ( r2_hidden('#skF_6'('#skF_9',k1_relat_1('#skF_9'),'#skF_1'(A_13612,'#skF_8')),k1_xboole_0)
      | r1_xboole_0(A_13612,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_13612,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_111010])).

tff(c_111054,plain,(
    ! [A_13646] :
      ( r1_xboole_0(A_13646,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_13646,'#skF_8'),k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_111051])).

tff(c_111061,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_111054])).

tff(c_111065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_234,c_111061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.15/18.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.15/18.17  
% 29.15/18.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.15/18.17  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 29.15/18.17  
% 29.15/18.17  %Foreground sorts:
% 29.15/18.17  
% 29.15/18.17  
% 29.15/18.17  %Background operators:
% 29.15/18.17  
% 29.15/18.17  
% 29.15/18.17  %Foreground operators:
% 29.15/18.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.15/18.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.15/18.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 29.15/18.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.15/18.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 29.15/18.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.15/18.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 29.15/18.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.15/18.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.15/18.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.15/18.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 29.15/18.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.15/18.17  tff('#skF_9', type, '#skF_9': $i).
% 29.15/18.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 29.15/18.17  tff('#skF_8', type, '#skF_8': $i).
% 29.15/18.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.15/18.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.15/18.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.15/18.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.15/18.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.15/18.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.15/18.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 29.15/18.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.15/18.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 29.15/18.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 29.15/18.17  
% 29.28/18.19  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 29.28/18.19  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 29.28/18.19  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 29.28/18.19  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 29.28/18.19  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 29.28/18.19  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 29.28/18.19  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 29.28/18.19  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 29.28/18.19  tff(f_73, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 29.28/18.19  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 29.28/18.19  tff(c_58, plain, (k9_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 29.28/18.19  tff(c_94, plain, (r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_58])).
% 29.28/18.19  tff(c_52, plain, (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8') | k9_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 29.28/18.19  tff(c_95, plain, (k9_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 29.28/18.19  tff(c_50, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 29.28/18.19  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.28/18.19  tff(c_183, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_97])).
% 29.28/18.19  tff(c_193, plain, (k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_94, c_183])).
% 29.28/18.19  tff(c_205, plain, (k7_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_193])).
% 29.28/18.19  tff(c_40, plain, (![B_43, A_42]: (k2_relat_1(k7_relat_1(B_43, A_42))=k9_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.28/18.19  tff(c_212, plain, (k9_relat_1('#skF_9', '#skF_8')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_205, c_40])).
% 29.28/18.19  tff(c_216, plain, (k9_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_212])).
% 29.28/18.19  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_216])).
% 29.28/18.19  tff(c_219, plain, (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 29.28/18.19  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_219])).
% 29.28/18.19  tff(c_227, plain, (k9_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 29.28/18.19  tff(c_234, plain, (~r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_52])).
% 29.28/18.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.28/18.19  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.28/18.19  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 29.28/18.19  tff(c_235, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 29.28/18.19  tff(c_242, plain, (![A_11, C_82]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 29.28/18.19  tff(c_245, plain, (![C_82]: (~r2_hidden(C_82, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_242])).
% 29.28/18.19  tff(c_20, plain, (![C_32, A_17]: (r2_hidden(k4_tarski(C_32, '#skF_6'(A_17, k1_relat_1(A_17), C_32)), A_17) | ~r2_hidden(C_32, k1_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 29.28/18.19  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.28/18.19  tff(c_986, plain, (![A_177, C_178, B_179, D_180]: (r2_hidden(A_177, k9_relat_1(C_178, B_179)) | ~r2_hidden(D_180, B_179) | ~r2_hidden(k4_tarski(D_180, A_177), C_178) | ~r2_hidden(D_180, k1_relat_1(C_178)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_84])).
% 29.28/18.19  tff(c_8876, plain, (![A_400, C_401, B_402, A_403]: (r2_hidden(A_400, k9_relat_1(C_401, B_402)) | ~r2_hidden(k4_tarski('#skF_1'(A_403, B_402), A_400), C_401) | ~r2_hidden('#skF_1'(A_403, B_402), k1_relat_1(C_401)) | ~v1_relat_1(C_401) | r1_xboole_0(A_403, B_402))), inference(resolution, [status(thm)], [c_4, c_986])).
% 29.28/18.19  tff(c_110623, plain, (![A_13611, A_13612, B_13613]: (r2_hidden('#skF_6'(A_13611, k1_relat_1(A_13611), '#skF_1'(A_13612, B_13613)), k9_relat_1(A_13611, B_13613)) | ~v1_relat_1(A_13611) | r1_xboole_0(A_13612, B_13613) | ~r2_hidden('#skF_1'(A_13612, B_13613), k1_relat_1(A_13611)))), inference(resolution, [status(thm)], [c_20, c_8876])).
% 29.28/18.19  tff(c_111010, plain, (![A_13612]: (r2_hidden('#skF_6'('#skF_9', k1_relat_1('#skF_9'), '#skF_1'(A_13612, '#skF_8')), k1_xboole_0) | ~v1_relat_1('#skF_9') | r1_xboole_0(A_13612, '#skF_8') | ~r2_hidden('#skF_1'(A_13612, '#skF_8'), k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_227, c_110623])).
% 29.28/18.19  tff(c_111051, plain, (![A_13612]: (r2_hidden('#skF_6'('#skF_9', k1_relat_1('#skF_9'), '#skF_1'(A_13612, '#skF_8')), k1_xboole_0) | r1_xboole_0(A_13612, '#skF_8') | ~r2_hidden('#skF_1'(A_13612, '#skF_8'), k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_111010])).
% 29.28/18.19  tff(c_111054, plain, (![A_13646]: (r1_xboole_0(A_13646, '#skF_8') | ~r2_hidden('#skF_1'(A_13646, '#skF_8'), k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_245, c_111051])).
% 29.28/18.19  tff(c_111061, plain, (r1_xboole_0(k1_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6, c_111054])).
% 29.28/18.19  tff(c_111065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_234, c_111061])).
% 29.28/18.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.28/18.19  
% 29.28/18.19  Inference rules
% 29.28/18.19  ----------------------
% 29.28/18.19  #Ref     : 0
% 29.28/18.19  #Sup     : 27406
% 29.28/18.19  #Fact    : 0
% 29.28/18.19  #Define  : 0
% 29.28/18.19  #Split   : 14
% 29.28/18.19  #Chain   : 0
% 29.28/18.19  #Close   : 0
% 29.28/18.19  
% 29.28/18.19  Ordering : KBO
% 29.28/18.19  
% 29.28/18.19  Simplification rules
% 29.28/18.19  ----------------------
% 29.28/18.19  #Subsume      : 11379
% 29.28/18.19  #Demod        : 24021
% 29.28/18.19  #Tautology    : 9445
% 29.28/18.19  #SimpNegUnit  : 331
% 29.28/18.19  #BackRed      : 0
% 29.28/18.19  
% 29.28/18.19  #Partial instantiations: 7391
% 29.28/18.19  #Strategies tried      : 1
% 29.28/18.19  
% 29.28/18.19  Timing (in seconds)
% 29.28/18.19  ----------------------
% 29.28/18.19  Preprocessing        : 0.33
% 29.28/18.19  Parsing              : 0.17
% 29.28/18.19  CNF conversion       : 0.03
% 29.28/18.19  Main loop            : 17.11
% 29.28/18.19  Inferencing          : 2.19
% 29.28/18.19  Reduction            : 2.60
% 29.28/18.19  Demodulation         : 1.81
% 29.28/18.19  BG Simplification    : 0.19
% 29.28/18.19  Subsumption          : 11.65
% 29.28/18.19  Abstraction          : 0.35
% 29.28/18.19  MUC search           : 0.00
% 29.28/18.19  Cooper               : 0.00
% 29.28/18.19  Total                : 17.46
% 29.28/18.19  Index Insertion      : 0.00
% 29.28/18.19  Index Deletion       : 0.00
% 29.28/18.19  Index Matching       : 0.00
% 29.28/18.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
