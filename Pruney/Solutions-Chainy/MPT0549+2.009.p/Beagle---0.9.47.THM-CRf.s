%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 110 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 212 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_50,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_127,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden(A_57,B_58)
      | ~ r2_hidden(A_57,k1_relat_1(k7_relat_1(C_59,B_58)))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [C_59,B_58] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_59,B_58))),B_58)
      | ~ v1_relat_1(C_59)
      | v1_xboole_0(k1_relat_1(k7_relat_1(C_59,B_58))) ) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_267,plain,(
    ! [A_67,C_68,B_69] :
      ( r2_hidden(A_67,k1_relat_1(C_68))
      | ~ r2_hidden(A_67,k1_relat_1(k7_relat_1(C_68,B_69)))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_456,plain,(
    ! [C_84,B_85] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_84,B_85))),k1_relat_1(C_84))
      | ~ v1_relat_1(C_84)
      | v1_xboole_0(k1_relat_1(k7_relat_1(C_84,B_85))) ) ),
    inference(resolution,[status(thm)],[c_4,c_267])).

tff(c_196,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_214,plain,(
    ! [C_56] :
      ( ~ r2_hidden(C_56,'#skF_3')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_90,c_196])).

tff(c_464,plain,(
    ! [B_85] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4',B_85))),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4',B_85))) ) ),
    inference(resolution,[status(thm)],[c_456,c_214])).

tff(c_582,plain,(
    ! [B_86] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4',B_86))),'#skF_3')
      | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4',B_86))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_464])).

tff(c_593,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_230,c_582])).

tff(c_599,plain,(
    v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_593])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_608,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_599,c_6])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    ! [A_17,B_18] :
      ( k1_relat_1(k7_relat_1(A_17,B_18)) != k1_xboole_0
      | k7_relat_1(A_17,B_18) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_634,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_123])).

tff(c_655,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_634])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_690,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_26])).

tff(c_715,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_690])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_715])).

tff(c_719,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    ! [A_13] : ~ r2_hidden(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_718,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_744,plain,(
    ! [A_94] :
      ( k2_relat_1(A_94) != k1_xboole_0
      | k1_xboole_0 = A_94
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_875,plain,(
    ! [A_119,B_120] :
      ( k2_relat_1(k7_relat_1(A_119,B_120)) != k1_xboole_0
      | k7_relat_1(A_119,B_120) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_24,c_744])).

tff(c_880,plain,(
    ! [B_123,A_124] :
      ( k9_relat_1(B_123,A_124) != k1_xboole_0
      | k7_relat_1(B_123,A_124) = k1_xboole_0
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_875])).

tff(c_882,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_880])).

tff(c_885,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_882])).

tff(c_934,plain,(
    ! [A_125,C_126,B_127] :
      ( r2_hidden(A_125,k1_relat_1(k7_relat_1(C_126,B_127)))
      | ~ r2_hidden(A_125,k1_relat_1(C_126))
      | ~ r2_hidden(A_125,B_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_946,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_125,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_125,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_934])).

tff(c_951,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,k1_xboole_0)
      | ~ r2_hidden(A_125,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_125,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30,c_946])).

tff(c_953,plain,(
    ! [A_128] :
      ( ~ r2_hidden(A_128,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_128,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_951])).

tff(c_971,plain,(
    ! [B_129] :
      ( ~ r2_hidden('#skF_2'(k1_relat_1('#skF_4'),B_129),'#skF_3')
      | r1_xboole_0(k1_relat_1('#skF_4'),B_129) ) ),
    inference(resolution,[status(thm)],[c_14,c_953])).

tff(c_975,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_971])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_719,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.42  
% 2.77/1.44  tff(f_100, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.77/1.44  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.44  tff(f_93, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.77/1.44  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.44  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.77/1.44  tff(f_70, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.77/1.44  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.77/1.44  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.77/1.44  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.77/1.44  tff(f_66, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.77/1.44  tff(c_50, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.77/1.44  tff(c_90, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 2.77/1.44  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.77/1.44  tff(c_127, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_44])).
% 2.77/1.44  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.77/1.44  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.44  tff(c_215, plain, (![A_57, B_58, C_59]: (r2_hidden(A_57, B_58) | ~r2_hidden(A_57, k1_relat_1(k7_relat_1(C_59, B_58))) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.44  tff(c_230, plain, (![C_59, B_58]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_59, B_58))), B_58) | ~v1_relat_1(C_59) | v1_xboole_0(k1_relat_1(k7_relat_1(C_59, B_58))))), inference(resolution, [status(thm)], [c_4, c_215])).
% 2.77/1.44  tff(c_267, plain, (![A_67, C_68, B_69]: (r2_hidden(A_67, k1_relat_1(C_68)) | ~r2_hidden(A_67, k1_relat_1(k7_relat_1(C_68, B_69))) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.44  tff(c_456, plain, (![C_84, B_85]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_84, B_85))), k1_relat_1(C_84)) | ~v1_relat_1(C_84) | v1_xboole_0(k1_relat_1(k7_relat_1(C_84, B_85))))), inference(resolution, [status(thm)], [c_4, c_267])).
% 2.77/1.44  tff(c_196, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.44  tff(c_214, plain, (![C_56]: (~r2_hidden(C_56, '#skF_3') | ~r2_hidden(C_56, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_90, c_196])).
% 2.77/1.44  tff(c_464, plain, (![B_85]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4', B_85))), '#skF_3') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', B_85))))), inference(resolution, [status(thm)], [c_456, c_214])).
% 2.77/1.44  tff(c_582, plain, (![B_86]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4', B_86))), '#skF_3') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', B_86))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_464])).
% 2.77/1.44  tff(c_593, plain, (~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_230, c_582])).
% 2.77/1.44  tff(c_599, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_593])).
% 2.77/1.44  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.44  tff(c_608, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_599, c_6])).
% 2.77/1.44  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.44  tff(c_116, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.44  tff(c_123, plain, (![A_17, B_18]: (k1_relat_1(k7_relat_1(A_17, B_18))!=k1_xboole_0 | k7_relat_1(A_17, B_18)=k1_xboole_0 | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_24, c_116])).
% 2.77/1.44  tff(c_634, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_608, c_123])).
% 2.77/1.44  tff(c_655, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_634])).
% 2.77/1.44  tff(c_26, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.44  tff(c_690, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_655, c_26])).
% 2.77/1.44  tff(c_715, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_690])).
% 2.77/1.44  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_715])).
% 2.77/1.44  tff(c_719, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.77/1.44  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.44  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.44  tff(c_18, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.44  tff(c_82, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.44  tff(c_85, plain, (![A_13]: (~r2_hidden(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_82])).
% 2.77/1.44  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.44  tff(c_718, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.77/1.44  tff(c_744, plain, (![A_94]: (k2_relat_1(A_94)!=k1_xboole_0 | k1_xboole_0=A_94 | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.44  tff(c_875, plain, (![A_119, B_120]: (k2_relat_1(k7_relat_1(A_119, B_120))!=k1_xboole_0 | k7_relat_1(A_119, B_120)=k1_xboole_0 | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_24, c_744])).
% 2.77/1.44  tff(c_880, plain, (![B_123, A_124]: (k9_relat_1(B_123, A_124)!=k1_xboole_0 | k7_relat_1(B_123, A_124)=k1_xboole_0 | ~v1_relat_1(B_123) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_26, c_875])).
% 2.77/1.44  tff(c_882, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_718, c_880])).
% 2.77/1.44  tff(c_885, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_882])).
% 2.77/1.44  tff(c_934, plain, (![A_125, C_126, B_127]: (r2_hidden(A_125, k1_relat_1(k7_relat_1(C_126, B_127))) | ~r2_hidden(A_125, k1_relat_1(C_126)) | ~r2_hidden(A_125, B_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.44  tff(c_946, plain, (![A_125]: (r2_hidden(A_125, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_125, k1_relat_1('#skF_4')) | ~r2_hidden(A_125, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_885, c_934])).
% 2.77/1.44  tff(c_951, plain, (![A_125]: (r2_hidden(A_125, k1_xboole_0) | ~r2_hidden(A_125, k1_relat_1('#skF_4')) | ~r2_hidden(A_125, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30, c_946])).
% 2.77/1.44  tff(c_953, plain, (![A_128]: (~r2_hidden(A_128, k1_relat_1('#skF_4')) | ~r2_hidden(A_128, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_85, c_951])).
% 2.77/1.44  tff(c_971, plain, (![B_129]: (~r2_hidden('#skF_2'(k1_relat_1('#skF_4'), B_129), '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), B_129))), inference(resolution, [status(thm)], [c_14, c_953])).
% 2.77/1.44  tff(c_975, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_12, c_971])).
% 2.77/1.44  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_719, c_719, c_975])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 198
% 2.77/1.44  #Fact    : 0
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 6
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 41
% 2.77/1.44  #Demod        : 168
% 2.77/1.44  #Tautology    : 87
% 2.77/1.44  #SimpNegUnit  : 20
% 2.77/1.44  #BackRed      : 2
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 2.77/1.44  Preprocessing        : 0.30
% 2.77/1.44  Parsing              : 0.17
% 2.77/1.44  CNF conversion       : 0.02
% 2.77/1.44  Main loop            : 0.38
% 2.77/1.44  Inferencing          : 0.15
% 2.77/1.44  Reduction            : 0.11
% 2.77/1.44  Demodulation         : 0.07
% 2.77/1.44  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.08
% 2.77/1.44  Abstraction          : 0.02
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.71
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
