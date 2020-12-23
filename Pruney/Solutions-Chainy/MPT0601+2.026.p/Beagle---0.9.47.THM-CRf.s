%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   67 (  86 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 154 expanded)
%              Number of equality atoms :   48 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_77,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [A_40,B_41] :
      ( k7_relat_1(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(B_41,k1_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_197,plain,(
    ! [A_56,A_57] :
      ( k7_relat_1(A_56,k1_tarski(A_57)) = k1_xboole_0
      | ~ v1_relat_1(A_56)
      | r2_hidden(A_57,k1_relat_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_36,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_36])).

tff(c_200,plain,
    ( k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_197,c_92])).

tff(c_206,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_200])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_xboole_0(k1_relat_1(B_22),A_21)
      | k7_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_129,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,A_45) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_44),A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,(
    ! [B_48,A_49] :
      ( k9_relat_1(B_48,A_49) = k1_xboole_0
      | k7_relat_1(B_48,A_49) != k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_32,c_129])).

tff(c_158,plain,(
    ! [A_50] :
      ( k9_relat_1('#skF_2',A_50) = k1_xboole_0
      | k7_relat_1('#skF_2',A_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_165,plain,(
    ! [B_13] :
      ( k11_relat_1('#skF_2',B_13) = k1_xboole_0
      | ~ v1_relat_1('#skF_2')
      | k7_relat_1('#skF_2',k1_tarski(B_13)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_16])).

tff(c_175,plain,(
    ! [B_13] :
      ( k11_relat_1('#skF_2',B_13) = k1_xboole_0
      | k7_relat_1('#skF_2',k1_tarski(B_13)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_165])).

tff(c_210,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_175])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_210])).

tff(c_218,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_217,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_283,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k1_relat_1(B_72),A_73)
      | k9_relat_1(B_72,A_73) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_335,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = k1_xboole_0
      | k9_relat_1(B_80,A_81) != k1_xboole_0
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_283,c_30])).

tff(c_377,plain,(
    ! [A_86,B_87] :
      ( k7_relat_1(A_86,k1_tarski(B_87)) = k1_xboole_0
      | k11_relat_1(A_86,B_87) != k1_xboole_0
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_335])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_325,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(k7_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_333,plain,(
    ! [B_77,A_5] :
      ( k1_relat_1(k7_relat_1(B_77,k1_tarski(A_5))) = k1_tarski(A_5)
      | ~ v1_relat_1(B_77)
      | ~ r2_hidden(A_5,k1_relat_1(B_77)) ) ),
    inference(resolution,[status(thm)],[c_10,c_325])).

tff(c_383,plain,(
    ! [B_87,A_86] :
      ( k1_tarski(B_87) = k1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_86)
      | ~ r2_hidden(B_87,k1_relat_1(A_86))
      | k11_relat_1(A_86,B_87) != k1_xboole_0
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_333])).

tff(c_392,plain,(
    ! [B_87,A_86] :
      ( k1_tarski(B_87) = k1_xboole_0
      | ~ v1_relat_1(A_86)
      | ~ r2_hidden(B_87,k1_relat_1(A_86))
      | k11_relat_1(A_86,B_87) != k1_xboole_0
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_383])).

tff(c_425,plain,(
    ! [A_96,B_97] :
      ( ~ v1_relat_1(A_96)
      | ~ r2_hidden(B_97,k1_relat_1(A_96))
      | k11_relat_1(A_96,B_97) != k1_xboole_0
      | ~ v1_relat_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_392])).

tff(c_434,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_217,c_425])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.32  
% 2.16/1.32  %Foreground sorts:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Background operators:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Foreground operators:
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.32  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.16/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.16/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.32  
% 2.52/1.33  tff(f_84, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.52/1.33  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.52/1.33  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.52/1.33  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.52/1.33  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.52/1.33  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.52/1.33  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.52/1.33  tff(f_43, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.52/1.33  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.52/1.33  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.52/1.33  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.52/1.33  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.52/1.33  tff(c_42, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.52/1.33  tff(c_77, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.52/1.33  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.33  tff(c_107, plain, (![A_40, B_41]: (k7_relat_1(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(B_41, k1_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.33  tff(c_197, plain, (![A_56, A_57]: (k7_relat_1(A_56, k1_tarski(A_57))=k1_xboole_0 | ~v1_relat_1(A_56) | r2_hidden(A_57, k1_relat_1(A_56)))), inference(resolution, [status(thm)], [c_12, c_107])).
% 2.52/1.33  tff(c_36, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.52/1.33  tff(c_92, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_77, c_36])).
% 2.52/1.33  tff(c_200, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_197, c_92])).
% 2.52/1.33  tff(c_206, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_200])).
% 2.52/1.33  tff(c_32, plain, (![B_22, A_21]: (r1_xboole_0(k1_relat_1(B_22), A_21) | k7_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.33  tff(c_129, plain, (![B_44, A_45]: (k9_relat_1(B_44, A_45)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_44), A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.33  tff(c_154, plain, (![B_48, A_49]: (k9_relat_1(B_48, A_49)=k1_xboole_0 | k7_relat_1(B_48, A_49)!=k1_xboole_0 | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_32, c_129])).
% 2.52/1.33  tff(c_158, plain, (![A_50]: (k9_relat_1('#skF_2', A_50)=k1_xboole_0 | k7_relat_1('#skF_2', A_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.52/1.33  tff(c_16, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.33  tff(c_165, plain, (![B_13]: (k11_relat_1('#skF_2', B_13)=k1_xboole_0 | ~v1_relat_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski(B_13))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_16])).
% 2.52/1.33  tff(c_175, plain, (![B_13]: (k11_relat_1('#skF_2', B_13)=k1_xboole_0 | k7_relat_1('#skF_2', k1_tarski(B_13))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_165])).
% 2.52/1.33  tff(c_210, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_206, c_175])).
% 2.52/1.33  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_210])).
% 2.52/1.33  tff(c_218, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.52/1.33  tff(c_217, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.52/1.33  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.33  tff(c_69, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.33  tff(c_73, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 2.52/1.33  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.33  tff(c_283, plain, (![B_72, A_73]: (r1_xboole_0(k1_relat_1(B_72), A_73) | k9_relat_1(B_72, A_73)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.33  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.33  tff(c_335, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=k1_xboole_0 | k9_relat_1(B_80, A_81)!=k1_xboole_0 | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_283, c_30])).
% 2.52/1.33  tff(c_377, plain, (![A_86, B_87]: (k7_relat_1(A_86, k1_tarski(B_87))=k1_xboole_0 | k11_relat_1(A_86, B_87)!=k1_xboole_0 | ~v1_relat_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_16, c_335])).
% 2.52/1.33  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.33  tff(c_325, plain, (![B_77, A_78]: (k1_relat_1(k7_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.52/1.33  tff(c_333, plain, (![B_77, A_5]: (k1_relat_1(k7_relat_1(B_77, k1_tarski(A_5)))=k1_tarski(A_5) | ~v1_relat_1(B_77) | ~r2_hidden(A_5, k1_relat_1(B_77)))), inference(resolution, [status(thm)], [c_10, c_325])).
% 2.52/1.33  tff(c_383, plain, (![B_87, A_86]: (k1_tarski(B_87)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(A_86) | ~r2_hidden(B_87, k1_relat_1(A_86)) | k11_relat_1(A_86, B_87)!=k1_xboole_0 | ~v1_relat_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_377, c_333])).
% 2.52/1.33  tff(c_392, plain, (![B_87, A_86]: (k1_tarski(B_87)=k1_xboole_0 | ~v1_relat_1(A_86) | ~r2_hidden(B_87, k1_relat_1(A_86)) | k11_relat_1(A_86, B_87)!=k1_xboole_0 | ~v1_relat_1(A_86) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_383])).
% 2.52/1.33  tff(c_425, plain, (![A_96, B_97]: (~v1_relat_1(A_96) | ~r2_hidden(B_97, k1_relat_1(A_96)) | k11_relat_1(A_96, B_97)!=k1_xboole_0 | ~v1_relat_1(A_96) | ~v1_relat_1(A_96))), inference(negUnitSimplification, [status(thm)], [c_73, c_392])).
% 2.52/1.33  tff(c_434, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_217, c_425])).
% 2.52/1.33  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_218, c_434])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 94
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 3
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 19
% 2.52/1.33  #Demod        : 14
% 2.52/1.33  #Tautology    : 39
% 2.52/1.33  #SimpNegUnit  : 3
% 2.52/1.33  #BackRed      : 0
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.33  Preprocessing        : 0.31
% 2.52/1.33  Parsing              : 0.16
% 2.52/1.33  CNF conversion       : 0.02
% 2.52/1.33  Main loop            : 0.25
% 2.52/1.33  Inferencing          : 0.10
% 2.52/1.33  Reduction            : 0.07
% 2.52/1.33  Demodulation         : 0.04
% 2.52/1.33  BG Simplification    : 0.01
% 2.52/1.33  Subsumption          : 0.05
% 2.52/1.33  Abstraction          : 0.01
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.34  Total                : 0.59
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
