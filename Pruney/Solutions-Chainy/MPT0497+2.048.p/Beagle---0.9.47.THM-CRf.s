%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 165 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_92,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_119,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_42])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_192,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_xboole_0 = A_53
      | ~ r1_xboole_0(B_54,C_55)
      | ~ r1_tarski(A_53,C_55)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,'#skF_2')
      | ~ r1_tarski(A_58,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_92,c_192])).

tff(c_214,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_23)) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_23)),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_210])).

tff(c_245,plain,(
    ! [A_65] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_65)) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_65)),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_214])).

tff(c_249,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_245])).

tff(c_252,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_249])).

tff(c_24,plain,(
    ! [A_17] :
      ( k3_xboole_0(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_265,plain,
    ( k3_xboole_0(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_3','#skF_2')))) = k7_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_24])).

tff(c_282,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_265])).

tff(c_283,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_282])).

tff(c_291,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_283])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_291])).

tff(c_297,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_296,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_572,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,k1_relat_1(k7_relat_1(C_106,B_107)))
      | ~ r2_hidden(A_105,k1_relat_1(C_106))
      | ~ r2_hidden(A_105,B_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_584,plain,(
    ! [A_105] :
      ( r2_hidden(A_105,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_105,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_105,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_572])).

tff(c_591,plain,(
    ! [A_108] :
      ( r2_hidden(A_108,k1_xboole_0)
      | ~ r2_hidden(A_108,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_108,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_584])).

tff(c_923,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_126),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_126),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_126) ) ),
    inference(resolution,[status(thm)],[c_8,c_591])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_333,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,B_76)
      | ~ r2_hidden(C_77,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_339,plain,(
    ! [C_77,A_9] :
      ( ~ r2_hidden(C_77,k1_xboole_0)
      | ~ r2_hidden(C_77,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_333])).

tff(c_1399,plain,(
    ! [B_161,A_162] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_161),A_162)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_161),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_161) ) ),
    inference(resolution,[status(thm)],[c_923,c_339])).

tff(c_1431,plain,(
    ! [B_163] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_163),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_163) ) ),
    inference(resolution,[status(thm)],[c_8,c_1399])).

tff(c_1439,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1431])).

tff(c_1444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_297,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.52  
% 3.43/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.43/1.53  
% 3.43/1.53  %Foreground sorts:
% 3.43/1.53  
% 3.43/1.53  
% 3.43/1.53  %Background operators:
% 3.43/1.53  
% 3.43/1.53  
% 3.43/1.53  %Foreground operators:
% 3.43/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.43/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.53  
% 3.47/1.54  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.47/1.54  tff(f_69, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.47/1.54  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.47/1.54  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.47/1.54  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.47/1.54  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.47/1.54  tff(f_59, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.47/1.54  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.47/1.54  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.47/1.54  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.47/1.54  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.47/1.54  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.47/1.54  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.47/1.54  tff(c_48, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_92, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.47/1.54  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_119, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_42])).
% 3.47/1.54  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.47/1.54  tff(c_20, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.54  tff(c_36, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.54  tff(c_38, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.47/1.54  tff(c_192, plain, (![A_53, B_54, C_55]: (k1_xboole_0=A_53 | ~r1_xboole_0(B_54, C_55) | ~r1_tarski(A_53, C_55) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.54  tff(c_210, plain, (![A_58]: (k1_xboole_0=A_58 | ~r1_tarski(A_58, '#skF_2') | ~r1_tarski(A_58, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_92, c_192])).
% 3.47/1.54  tff(c_214, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_3', A_23))=k1_xboole_0 | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_23)), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_210])).
% 3.47/1.54  tff(c_245, plain, (![A_65]: (k1_relat_1(k7_relat_1('#skF_3', A_65))=k1_xboole_0 | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_65)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_214])).
% 3.47/1.54  tff(c_249, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_245])).
% 3.47/1.54  tff(c_252, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_249])).
% 3.47/1.54  tff(c_24, plain, (![A_17]: (k3_xboole_0(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.47/1.54  tff(c_265, plain, (k3_xboole_0(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))))=k7_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_24])).
% 3.47/1.54  tff(c_282, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_265])).
% 3.47/1.54  tff(c_283, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_119, c_282])).
% 3.47/1.54  tff(c_291, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_283])).
% 3.47/1.54  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_291])).
% 3.47/1.54  tff(c_297, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.47/1.54  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.47/1.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.47/1.54  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.47/1.54  tff(c_296, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.47/1.54  tff(c_572, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, k1_relat_1(k7_relat_1(C_106, B_107))) | ~r2_hidden(A_105, k1_relat_1(C_106)) | ~r2_hidden(A_105, B_107) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.47/1.54  tff(c_584, plain, (![A_105]: (r2_hidden(A_105, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_105, k1_relat_1('#skF_3')) | ~r2_hidden(A_105, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_572])).
% 3.47/1.54  tff(c_591, plain, (![A_108]: (r2_hidden(A_108, k1_xboole_0) | ~r2_hidden(A_108, k1_relat_1('#skF_3')) | ~r2_hidden(A_108, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_584])).
% 3.47/1.54  tff(c_923, plain, (![B_126]: (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_126), k1_xboole_0) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_126), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_126))), inference(resolution, [status(thm)], [c_8, c_591])).
% 3.47/1.54  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.54  tff(c_333, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, B_76) | ~r2_hidden(C_77, A_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.47/1.54  tff(c_339, plain, (![C_77, A_9]: (~r2_hidden(C_77, k1_xboole_0) | ~r2_hidden(C_77, A_9))), inference(resolution, [status(thm)], [c_12, c_333])).
% 3.47/1.54  tff(c_1399, plain, (![B_161, A_162]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_161), A_162) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_161), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_161))), inference(resolution, [status(thm)], [c_923, c_339])).
% 3.47/1.54  tff(c_1431, plain, (![B_163]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_163), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_163))), inference(resolution, [status(thm)], [c_8, c_1399])).
% 3.47/1.54  tff(c_1439, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_1431])).
% 3.47/1.54  tff(c_1444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_297, c_1439])).
% 3.47/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.54  
% 3.47/1.54  Inference rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Ref     : 0
% 3.47/1.54  #Sup     : 305
% 3.47/1.54  #Fact    : 0
% 3.47/1.54  #Define  : 0
% 3.47/1.54  #Split   : 2
% 3.47/1.54  #Chain   : 0
% 3.47/1.54  #Close   : 0
% 3.47/1.54  
% 3.47/1.54  Ordering : KBO
% 3.47/1.54  
% 3.47/1.54  Simplification rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Subsume      : 62
% 3.47/1.54  #Demod        : 355
% 3.47/1.54  #Tautology    : 147
% 3.47/1.54  #SimpNegUnit  : 2
% 3.47/1.54  #BackRed      : 2
% 3.47/1.54  
% 3.47/1.54  #Partial instantiations: 0
% 3.47/1.54  #Strategies tried      : 1
% 3.47/1.54  
% 3.47/1.54  Timing (in seconds)
% 3.47/1.54  ----------------------
% 3.47/1.54  Preprocessing        : 0.31
% 3.47/1.54  Parsing              : 0.17
% 3.47/1.54  CNF conversion       : 0.02
% 3.47/1.54  Main loop            : 0.46
% 3.47/1.54  Inferencing          : 0.17
% 3.47/1.54  Reduction            : 0.14
% 3.47/1.54  Demodulation         : 0.10
% 3.47/1.54  BG Simplification    : 0.02
% 3.47/1.54  Subsumption          : 0.10
% 3.47/1.54  Abstraction          : 0.02
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.80
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
