%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   73 (  94 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 148 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_64,plain,
    ( k7_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_104,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | k7_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_134,plain,(
    k7_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_536,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(k4_tarski('#skF_3'(A_153,B_154),'#skF_4'(A_153,B_154)),A_153)
      | r2_hidden('#skF_5'(A_153,B_154),B_154)
      | k1_relat_1(A_153) = B_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,(
    ! [A_15] : ~ r2_hidden(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_579,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_154),B_154)
      | k1_relat_1(k1_xboole_0) = B_154 ) ),
    inference(resolution,[status(thm)],[c_536,c_98])).

tff(c_592,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_155),B_155)
      | k1_xboole_0 = B_155 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_579])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_646,plain,(
    ! [A_156,B_157] :
      ( ~ r1_xboole_0(A_156,B_157)
      | k3_xboole_0(A_156,B_157) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_592,c_12])).

tff(c_702,plain,(
    k3_xboole_0(k1_relat_1('#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_646])).

tff(c_54,plain,(
    ! [B_47,A_46] :
      ( k3_xboole_0(k1_relat_1(B_47),A_46) = k1_relat_1(k7_relat_1(B_47,A_46))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_992,plain,
    ( k1_relat_1(k7_relat_1('#skF_8','#skF_7')) = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_54])).

tff(c_1030,plain,(
    k1_relat_1(k7_relat_1('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_992])).

tff(c_38,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k7_relat_1(A_40,B_41))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) != k1_xboole_0
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    ! [A_40,B_41] :
      ( k1_relat_1(k7_relat_1(A_40,B_41)) != k1_xboole_0
      | k7_relat_1(A_40,B_41) = k1_xboole_0
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_1061,plain,
    ( k7_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_120])).

tff(c_1084,plain,(
    k7_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1061])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_1084])).

tff(c_1088,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1087,plain,(
    k7_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1544,plain,(
    ! [A_234,C_235,B_236] :
      ( r2_hidden(A_234,k1_relat_1(k7_relat_1(C_235,B_236)))
      | ~ r2_hidden(A_234,k1_relat_1(C_235))
      | ~ r2_hidden(A_234,B_236)
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1570,plain,(
    ! [A_234] :
      ( r2_hidden(A_234,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_234,k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_234,'#skF_7')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_1544])).

tff(c_1583,plain,(
    ! [A_234] :
      ( r2_hidden(A_234,k1_xboole_0)
      | ~ r2_hidden(A_234,k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_234,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_1570])).

tff(c_1586,plain,(
    ! [A_237] :
      ( ~ r2_hidden(A_237,k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_237,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1583])).

tff(c_1662,plain,(
    ! [A_251] :
      ( ~ r2_hidden('#skF_1'(A_251,k1_relat_1('#skF_8')),'#skF_7')
      | r1_xboole_0(A_251,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1586])).

tff(c_1667,plain,(
    r1_xboole_0('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_8,c_1662])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1671,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1667,c_2])).

tff(c_1676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_1671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.96  
% 5.17/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.97  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.17/2.97  
% 5.17/2.97  %Foreground sorts:
% 5.17/2.97  
% 5.17/2.97  
% 5.17/2.97  %Background operators:
% 5.17/2.97  
% 5.17/2.97  
% 5.17/2.97  %Foreground operators:
% 5.17/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.97  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.17/2.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.17/2.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.17/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.97  tff('#skF_7', type, '#skF_7': $i).
% 5.17/2.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.17/2.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/2.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/2.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.17/2.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.17/2.97  tff('#skF_8', type, '#skF_8': $i).
% 5.17/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/2.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.17/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.17/2.97  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.17/2.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/2.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.17/2.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.17/2.97  
% 5.51/3.04  tff(f_116, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 5.51/3.04  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.51/3.04  tff(f_82, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.51/3.04  tff(f_69, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.51/3.04  tff(f_72, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.51/3.04  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.51/3.04  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.51/3.04  tff(f_86, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.51/3.04  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.51/3.04  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.51/3.04  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 5.51/3.04  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.51/3.04  tff(c_64, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/3.04  tff(c_104, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 5.51/3.04  tff(c_58, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | k7_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/3.04  tff(c_134, plain, (k7_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_58])).
% 5.51/3.04  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/3.04  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.51/3.04  tff(c_536, plain, (![A_153, B_154]: (r2_hidden(k4_tarski('#skF_3'(A_153, B_154), '#skF_4'(A_153, B_154)), A_153) | r2_hidden('#skF_5'(A_153, B_154), B_154) | k1_relat_1(A_153)=B_154)), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.51/3.04  tff(c_18, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.51/3.04  tff(c_95, plain, (![A_50, B_51]: (~r2_hidden(A_50, k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.51/3.04  tff(c_98, plain, (![A_15]: (~r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 5.51/3.04  tff(c_579, plain, (![B_154]: (r2_hidden('#skF_5'(k1_xboole_0, B_154), B_154) | k1_relat_1(k1_xboole_0)=B_154)), inference(resolution, [status(thm)], [c_536, c_98])).
% 5.51/3.04  tff(c_592, plain, (![B_155]: (r2_hidden('#skF_5'(k1_xboole_0, B_155), B_155) | k1_xboole_0=B_155)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_579])).
% 5.51/3.04  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.51/3.04  tff(c_646, plain, (![A_156, B_157]: (~r1_xboole_0(A_156, B_157) | k3_xboole_0(A_156, B_157)=k1_xboole_0)), inference(resolution, [status(thm)], [c_592, c_12])).
% 5.51/3.04  tff(c_702, plain, (k3_xboole_0(k1_relat_1('#skF_8'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_646])).
% 5.51/3.04  tff(c_54, plain, (![B_47, A_46]: (k3_xboole_0(k1_relat_1(B_47), A_46)=k1_relat_1(k7_relat_1(B_47, A_46)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/3.04  tff(c_992, plain, (k1_relat_1(k7_relat_1('#skF_8', '#skF_7'))=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_702, c_54])).
% 5.51/3.04  tff(c_1030, plain, (k1_relat_1(k7_relat_1('#skF_8', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_992])).
% 5.51/3.04  tff(c_38, plain, (![A_40, B_41]: (v1_relat_1(k7_relat_1(A_40, B_41)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.51/3.04  tff(c_113, plain, (![A_57]: (k1_relat_1(A_57)!=k1_xboole_0 | k1_xboole_0=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.51/3.04  tff(c_120, plain, (![A_40, B_41]: (k1_relat_1(k7_relat_1(A_40, B_41))!=k1_xboole_0 | k7_relat_1(A_40, B_41)=k1_xboole_0 | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_38, c_113])).
% 5.51/3.04  tff(c_1061, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_120])).
% 5.51/3.04  tff(c_1084, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1061])).
% 5.51/3.04  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_1084])).
% 5.51/3.04  tff(c_1088, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 5.51/3.04  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/3.04  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/3.04  tff(c_1087, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 5.51/3.04  tff(c_1544, plain, (![A_234, C_235, B_236]: (r2_hidden(A_234, k1_relat_1(k7_relat_1(C_235, B_236))) | ~r2_hidden(A_234, k1_relat_1(C_235)) | ~r2_hidden(A_234, B_236) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.51/3.04  tff(c_1570, plain, (![A_234]: (r2_hidden(A_234, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_234, k1_relat_1('#skF_8')) | ~r2_hidden(A_234, '#skF_7') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_1544])).
% 5.51/3.04  tff(c_1583, plain, (![A_234]: (r2_hidden(A_234, k1_xboole_0) | ~r2_hidden(A_234, k1_relat_1('#skF_8')) | ~r2_hidden(A_234, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_1570])).
% 5.51/3.04  tff(c_1586, plain, (![A_237]: (~r2_hidden(A_237, k1_relat_1('#skF_8')) | ~r2_hidden(A_237, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_98, c_1583])).
% 5.51/3.04  tff(c_1662, plain, (![A_251]: (~r2_hidden('#skF_1'(A_251, k1_relat_1('#skF_8')), '#skF_7') | r1_xboole_0(A_251, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_6, c_1586])).
% 5.51/3.04  tff(c_1667, plain, (r1_xboole_0('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_8, c_1662])).
% 5.51/3.04  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.51/3.04  tff(c_1671, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_1667, c_2])).
% 5.51/3.04  tff(c_1676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1088, c_1671])).
% 5.51/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/3.04  
% 5.51/3.04  Inference rules
% 5.51/3.04  ----------------------
% 5.51/3.04  #Ref     : 0
% 5.51/3.04  #Sup     : 348
% 5.51/3.04  #Fact    : 0
% 5.51/3.04  #Define  : 0
% 5.51/3.04  #Split   : 7
% 5.51/3.04  #Chain   : 0
% 5.51/3.04  #Close   : 0
% 5.51/3.04  
% 5.51/3.04  Ordering : KBO
% 5.51/3.04  
% 5.51/3.04  Simplification rules
% 5.51/3.04  ----------------------
% 5.51/3.04  #Subsume      : 86
% 5.51/3.04  #Demod        : 272
% 5.51/3.04  #Tautology    : 118
% 5.51/3.04  #SimpNegUnit  : 15
% 5.51/3.04  #BackRed      : 0
% 5.51/3.04  
% 5.51/3.04  #Partial instantiations: 0
% 5.51/3.04  #Strategies tried      : 1
% 5.51/3.04  
% 5.51/3.04  Timing (in seconds)
% 5.51/3.04  ----------------------
% 5.51/3.04  Preprocessing        : 0.75
% 5.51/3.04  Parsing              : 0.38
% 5.51/3.04  CNF conversion       : 0.06
% 5.51/3.04  Main loop            : 1.14
% 5.51/3.04  Inferencing          : 0.39
% 5.51/3.04  Reduction            : 0.37
% 5.51/3.04  Demodulation         : 0.27
% 5.51/3.04  BG Simplification    : 0.05
% 5.51/3.04  Subsumption          : 0.25
% 5.51/3.04  Abstraction          : 0.06
% 5.51/3.04  MUC search           : 0.00
% 5.51/3.04  Cooper               : 0.00
% 5.51/3.04  Total                : 1.99
% 5.51/3.04  Index Insertion      : 0.00
% 5.51/3.04  Index Deletion       : 0.00
% 5.51/3.04  Index Matching       : 0.00
% 5.51/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
