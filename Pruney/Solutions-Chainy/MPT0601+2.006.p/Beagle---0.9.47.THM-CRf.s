%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 111 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_44,axiom,(
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

tff(c_62,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110,plain,(
    k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_336,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden(k4_tarski(A_113,B_114),C_115)
      | ~ r2_hidden(B_114,k11_relat_1(C_115,A_113))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [C_36,A_21,D_39] :
      ( r2_hidden(C_36,k1_relat_1(A_21))
      | ~ r2_hidden(k4_tarski(C_36,D_39),A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_345,plain,(
    ! [A_116,C_117,B_118] :
      ( r2_hidden(A_116,k1_relat_1(C_117))
      | ~ r2_hidden(B_118,k11_relat_1(C_117,A_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_336,c_44])).

tff(c_362,plain,(
    ! [A_119,C_120] :
      ( r2_hidden(A_119,k1_relat_1(C_120))
      | ~ v1_relat_1(C_120)
      | k11_relat_1(C_120,A_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_345])).

tff(c_64,plain,
    ( k11_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_64])).

tff(c_373,plain,
    ( ~ v1_relat_1('#skF_10')
    | k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_362,c_119])).

tff(c_378,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_378])).

tff(c_382,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_40,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(A_18,k1_tarski(B_20)) = k11_relat_1(A_18,B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_381,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_36,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    ! [B_58,A_59] : r2_hidden(B_58,k2_tarski(A_59,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_14])).

tff(c_109,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_106])).

tff(c_467,plain,(
    ! [B_144,A_145] :
      ( r1_xboole_0(k1_relat_1(B_144),A_145)
      | k9_relat_1(B_144,A_145) != k1_xboole_0
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1604,plain,(
    ! [C_281,A_282,B_283] :
      ( ~ r2_hidden(C_281,A_282)
      | ~ r2_hidden(C_281,k1_relat_1(B_283))
      | k9_relat_1(B_283,A_282) != k1_xboole_0
      | ~ v1_relat_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_467,c_4])).

tff(c_1782,plain,(
    ! [A_285,B_286] :
      ( ~ r2_hidden(A_285,k1_relat_1(B_286))
      | k9_relat_1(B_286,k1_tarski(A_285)) != k1_xboole_0
      | ~ v1_relat_1(B_286) ) ),
    inference(resolution,[status(thm)],[c_109,c_1604])).

tff(c_1857,plain,
    ( k9_relat_1('#skF_10',k1_tarski('#skF_9')) != k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_381,c_1782])).

tff(c_1886,plain,(
    k9_relat_1('#skF_10',k1_tarski('#skF_9')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1857])).

tff(c_1890,plain,
    ( k11_relat_1('#skF_10','#skF_9') != k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1886])).

tff(c_1893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_382,c_1890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n007.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:08:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  
% 3.85/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.85/1.67  
% 3.85/1.67  %Foreground sorts:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Background operators:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Foreground operators:
% 3.85/1.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.85/1.67  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.85/1.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.85/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.67  tff('#skF_10', type, '#skF_10': $i).
% 3.85/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.67  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.85/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.85/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.67  tff('#skF_9', type, '#skF_9': $i).
% 3.85/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.85/1.67  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.85/1.67  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.85/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.85/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.67  
% 3.85/1.68  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.85/1.68  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.85/1.68  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.85/1.68  tff(f_84, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.85/1.68  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.85/1.68  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.68  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.68  tff(f_67, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.85/1.68  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.85/1.68  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.85/1.68  tff(c_62, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_70, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_110, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 3.85/1.68  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.85/1.68  tff(c_336, plain, (![A_113, B_114, C_115]: (r2_hidden(k4_tarski(A_113, B_114), C_115) | ~r2_hidden(B_114, k11_relat_1(C_115, A_113)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.85/1.68  tff(c_44, plain, (![C_36, A_21, D_39]: (r2_hidden(C_36, k1_relat_1(A_21)) | ~r2_hidden(k4_tarski(C_36, D_39), A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.85/1.68  tff(c_345, plain, (![A_116, C_117, B_118]: (r2_hidden(A_116, k1_relat_1(C_117)) | ~r2_hidden(B_118, k11_relat_1(C_117, A_116)) | ~v1_relat_1(C_117))), inference(resolution, [status(thm)], [c_336, c_44])).
% 3.85/1.68  tff(c_362, plain, (![A_119, C_120]: (r2_hidden(A_119, k1_relat_1(C_120)) | ~v1_relat_1(C_120) | k11_relat_1(C_120, A_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_345])).
% 3.85/1.68  tff(c_64, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_119, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_110, c_64])).
% 3.85/1.68  tff(c_373, plain, (~v1_relat_1('#skF_10') | k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_362, c_119])).
% 3.85/1.68  tff(c_378, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373])).
% 3.85/1.68  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_378])).
% 3.85/1.68  tff(c_382, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 3.85/1.68  tff(c_40, plain, (![A_18, B_20]: (k9_relat_1(A_18, k1_tarski(B_20))=k11_relat_1(A_18, B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.85/1.68  tff(c_381, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_70])).
% 3.85/1.68  tff(c_36, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.85/1.68  tff(c_88, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.85/1.68  tff(c_14, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.85/1.68  tff(c_106, plain, (![B_58, A_59]: (r2_hidden(B_58, k2_tarski(A_59, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_14])).
% 3.85/1.68  tff(c_109, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_106])).
% 3.85/1.68  tff(c_467, plain, (![B_144, A_145]: (r1_xboole_0(k1_relat_1(B_144), A_145) | k9_relat_1(B_144, A_145)!=k1_xboole_0 | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.68  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.68  tff(c_1604, plain, (![C_281, A_282, B_283]: (~r2_hidden(C_281, A_282) | ~r2_hidden(C_281, k1_relat_1(B_283)) | k9_relat_1(B_283, A_282)!=k1_xboole_0 | ~v1_relat_1(B_283))), inference(resolution, [status(thm)], [c_467, c_4])).
% 3.85/1.68  tff(c_1782, plain, (![A_285, B_286]: (~r2_hidden(A_285, k1_relat_1(B_286)) | k9_relat_1(B_286, k1_tarski(A_285))!=k1_xboole_0 | ~v1_relat_1(B_286))), inference(resolution, [status(thm)], [c_109, c_1604])).
% 3.85/1.68  tff(c_1857, plain, (k9_relat_1('#skF_10', k1_tarski('#skF_9'))!=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_381, c_1782])).
% 3.85/1.68  tff(c_1886, plain, (k9_relat_1('#skF_10', k1_tarski('#skF_9'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1857])).
% 3.85/1.68  tff(c_1890, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1886])).
% 3.85/1.68  tff(c_1893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_382, c_1890])).
% 3.85/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  Inference rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Ref     : 0
% 3.85/1.68  #Sup     : 404
% 3.85/1.68  #Fact    : 0
% 3.85/1.68  #Define  : 0
% 3.85/1.68  #Split   : 1
% 3.85/1.68  #Chain   : 0
% 3.85/1.68  #Close   : 0
% 3.85/1.68  
% 3.85/1.68  Ordering : KBO
% 3.85/1.68  
% 3.85/1.68  Simplification rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Subsume      : 19
% 3.85/1.68  #Demod        : 57
% 3.85/1.68  #Tautology    : 115
% 3.85/1.68  #SimpNegUnit  : 2
% 3.85/1.68  #BackRed      : 0
% 3.85/1.68  
% 3.85/1.68  #Partial instantiations: 0
% 3.85/1.68  #Strategies tried      : 1
% 3.85/1.68  
% 3.85/1.68  Timing (in seconds)
% 3.85/1.68  ----------------------
% 3.85/1.68  Preprocessing        : 0.35
% 3.85/1.68  Parsing              : 0.18
% 3.85/1.68  CNF conversion       : 0.03
% 3.85/1.68  Main loop            : 0.58
% 3.85/1.68  Inferencing          : 0.21
% 3.85/1.68  Reduction            : 0.17
% 3.85/1.68  Demodulation         : 0.13
% 3.85/1.68  BG Simplification    : 0.03
% 3.85/1.68  Subsumption          : 0.11
% 3.85/1.68  Abstraction          : 0.04
% 3.85/1.68  MUC search           : 0.00
% 3.85/1.68  Cooper               : 0.00
% 3.85/1.68  Total                : 0.96
% 3.85/1.68  Index Insertion      : 0.00
% 3.85/1.69  Index Deletion       : 0.00
% 3.85/1.69  Index Matching       : 0.00
% 3.85/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
