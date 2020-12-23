%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   72 (  97 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 181 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

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

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_58,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_101,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_136,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_349,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden(A_104,B_105)
      | ~ r2_hidden(A_104,k1_relat_1(k7_relat_1(C_106,B_105)))
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_810,plain,(
    ! [C_231,B_232,B_233] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_231,B_232)),B_233),B_232)
      | ~ v1_relat_1(C_231)
      | r1_xboole_0(k1_relat_1(k7_relat_1(C_231,B_232)),B_233) ) ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_284,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_92,A_93)),k1_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_152,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_xboole_0(A_70,C_71)
      | ~ r1_xboole_0(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_70] :
      ( r1_xboole_0(A_70,'#skF_2')
      | ~ r1_tarski(A_70,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_101,c_152])).

tff(c_288,plain,(
    ! [A_93] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_93)),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_284,c_162])).

tff(c_295,plain,(
    ! [A_94] : r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_94)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_288])).

tff(c_4,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_338,plain,(
    ! [C_102,A_103] :
      ( ~ r2_hidden(C_102,'#skF_2')
      | ~ r2_hidden(C_102,k1_relat_1(k7_relat_1('#skF_3',A_103))) ) ),
    inference(resolution,[status(thm)],[c_295,c_4])).

tff(c_348,plain,(
    ! [A_103,B_4] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3',A_103)),B_4),'#skF_2')
      | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_103)),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_338])).

tff(c_822,plain,(
    ! [B_233] :
      ( ~ v1_relat_1('#skF_3')
      | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),B_233) ) ),
    inference(resolution,[status(thm)],[c_810,c_348])).

tff(c_896,plain,(
    ! [B_234] : r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),B_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_822])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_910,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_896,c_16])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k7_relat_1(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_92,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) != k1_xboole_0
      | k1_xboole_0 = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_99,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1(k7_relat_1(A_43,B_44)) != k1_xboole_0
      | k7_relat_1(A_43,B_44) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_974,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_99])).

tff(c_1034,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_974])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1034])).

tff(c_1038,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1086,plain,(
    ! [A_242,C_243,B_244] :
      ( ~ r2_hidden(A_242,C_243)
      | ~ r1_xboole_0(k2_tarski(A_242,B_244),C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1091,plain,(
    ! [A_242] : ~ r2_hidden(A_242,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_1086])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1037,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1451,plain,(
    ! [A_312,C_313,B_314] :
      ( r2_hidden(A_312,k1_relat_1(k7_relat_1(C_313,B_314)))
      | ~ r2_hidden(A_312,k1_relat_1(C_313))
      | ~ r2_hidden(A_312,B_314)
      | ~ v1_relat_1(C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1471,plain,(
    ! [A_312] :
      ( r2_hidden(A_312,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_312,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_312,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1037,c_1451])).

tff(c_1481,plain,(
    ! [A_312] :
      ( r2_hidden(A_312,k1_xboole_0)
      | ~ r2_hidden(A_312,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_312,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_1471])).

tff(c_1483,plain,(
    ! [A_315] :
      ( ~ r2_hidden(A_315,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_315,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1091,c_1481])).

tff(c_1494,plain,(
    ! [B_316] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_316),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_316) ) ),
    inference(resolution,[status(thm)],[c_8,c_1483])).

tff(c_1498,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1494])).

tff(c_1502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1038,c_1498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.47/1.61  
% 3.47/1.61  %Foreground sorts:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Background operators:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Foreground operators:
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.61  
% 3.79/1.63  tff(f_118, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.79/1.63  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.79/1.63  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.79/1.63  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.79/1.63  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.79/1.63  tff(f_67, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.79/1.63  tff(f_88, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.79/1.63  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.79/1.63  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.79/1.63  tff(f_84, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.79/1.63  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.79/1.63  tff(c_58, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.79/1.63  tff(c_101, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 3.79/1.63  tff(c_52, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.79/1.63  tff(c_136, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_52])).
% 3.79/1.63  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.79/1.63  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/1.63  tff(c_349, plain, (![A_104, B_105, C_106]: (r2_hidden(A_104, B_105) | ~r2_hidden(A_104, k1_relat_1(k7_relat_1(C_106, B_105))) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.63  tff(c_810, plain, (![C_231, B_232, B_233]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_231, B_232)), B_233), B_232) | ~v1_relat_1(C_231) | r1_xboole_0(k1_relat_1(k7_relat_1(C_231, B_232)), B_233))), inference(resolution, [status(thm)], [c_8, c_349])).
% 3.79/1.63  tff(c_284, plain, (![B_92, A_93]: (r1_tarski(k1_relat_1(k7_relat_1(B_92, A_93)), k1_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.79/1.63  tff(c_152, plain, (![A_70, C_71, B_72]: (r1_xboole_0(A_70, C_71) | ~r1_xboole_0(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/1.63  tff(c_162, plain, (![A_70]: (r1_xboole_0(A_70, '#skF_2') | ~r1_tarski(A_70, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_101, c_152])).
% 3.79/1.63  tff(c_288, plain, (![A_93]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_93)), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_284, c_162])).
% 3.79/1.63  tff(c_295, plain, (![A_94]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_94)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_288])).
% 3.79/1.63  tff(c_4, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/1.63  tff(c_338, plain, (![C_102, A_103]: (~r2_hidden(C_102, '#skF_2') | ~r2_hidden(C_102, k1_relat_1(k7_relat_1('#skF_3', A_103))))), inference(resolution, [status(thm)], [c_295, c_4])).
% 3.79/1.63  tff(c_348, plain, (![A_103, B_4]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_3', A_103)), B_4), '#skF_2') | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_103)), B_4))), inference(resolution, [status(thm)], [c_8, c_338])).
% 3.79/1.63  tff(c_822, plain, (![B_233]: (~v1_relat_1('#skF_3') | r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), B_233))), inference(resolution, [status(thm)], [c_810, c_348])).
% 3.79/1.63  tff(c_896, plain, (![B_234]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), B_234))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_822])).
% 3.79/1.63  tff(c_16, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.79/1.63  tff(c_910, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_896, c_16])).
% 3.79/1.63  tff(c_32, plain, (![A_43, B_44]: (v1_relat_1(k7_relat_1(A_43, B_44)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.79/1.63  tff(c_92, plain, (![A_58]: (k1_relat_1(A_58)!=k1_xboole_0 | k1_xboole_0=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.79/1.63  tff(c_99, plain, (![A_43, B_44]: (k1_relat_1(k7_relat_1(A_43, B_44))!=k1_xboole_0 | k7_relat_1(A_43, B_44)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_32, c_92])).
% 3.79/1.63  tff(c_974, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_910, c_99])).
% 3.79/1.63  tff(c_1034, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_974])).
% 3.79/1.63  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1034])).
% 3.79/1.63  tff(c_1038, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.79/1.63  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/1.63  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.79/1.63  tff(c_1086, plain, (![A_242, C_243, B_244]: (~r2_hidden(A_242, C_243) | ~r1_xboole_0(k2_tarski(A_242, B_244), C_243))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.79/1.63  tff(c_1091, plain, (![A_242]: (~r2_hidden(A_242, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1086])).
% 3.79/1.63  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.79/1.63  tff(c_1037, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.79/1.63  tff(c_1451, plain, (![A_312, C_313, B_314]: (r2_hidden(A_312, k1_relat_1(k7_relat_1(C_313, B_314))) | ~r2_hidden(A_312, k1_relat_1(C_313)) | ~r2_hidden(A_312, B_314) | ~v1_relat_1(C_313))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.63  tff(c_1471, plain, (![A_312]: (r2_hidden(A_312, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_312, k1_relat_1('#skF_3')) | ~r2_hidden(A_312, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1037, c_1451])).
% 3.79/1.63  tff(c_1481, plain, (![A_312]: (r2_hidden(A_312, k1_xboole_0) | ~r2_hidden(A_312, k1_relat_1('#skF_3')) | ~r2_hidden(A_312, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_1471])).
% 3.79/1.63  tff(c_1483, plain, (![A_315]: (~r2_hidden(A_315, k1_relat_1('#skF_3')) | ~r2_hidden(A_315, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1091, c_1481])).
% 3.79/1.63  tff(c_1494, plain, (![B_316]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_316), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_316))), inference(resolution, [status(thm)], [c_8, c_1483])).
% 3.79/1.63  tff(c_1498, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_1494])).
% 3.79/1.63  tff(c_1502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1038, c_1038, c_1498])).
% 3.79/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.63  
% 3.79/1.63  Inference rules
% 3.79/1.63  ----------------------
% 3.79/1.63  #Ref     : 0
% 3.79/1.63  #Sup     : 321
% 3.79/1.63  #Fact    : 0
% 3.79/1.63  #Define  : 0
% 3.79/1.63  #Split   : 6
% 3.79/1.63  #Chain   : 0
% 3.79/1.63  #Close   : 0
% 3.79/1.63  
% 3.79/1.63  Ordering : KBO
% 3.79/1.63  
% 3.79/1.63  Simplification rules
% 3.79/1.63  ----------------------
% 3.79/1.63  #Subsume      : 90
% 3.79/1.63  #Demod        : 137
% 3.79/1.63  #Tautology    : 80
% 3.79/1.63  #SimpNegUnit  : 8
% 3.79/1.63  #BackRed      : 3
% 3.79/1.63  
% 3.79/1.63  #Partial instantiations: 0
% 3.79/1.63  #Strategies tried      : 1
% 3.79/1.63  
% 3.79/1.63  Timing (in seconds)
% 3.79/1.63  ----------------------
% 3.79/1.63  Preprocessing        : 0.32
% 3.79/1.63  Parsing              : 0.17
% 3.79/1.63  CNF conversion       : 0.02
% 3.79/1.63  Main loop            : 0.49
% 3.79/1.63  Inferencing          : 0.18
% 3.79/1.63  Reduction            : 0.14
% 3.79/1.63  Demodulation         : 0.09
% 3.79/1.63  BG Simplification    : 0.02
% 3.79/1.63  Subsumption          : 0.12
% 3.79/1.63  Abstraction          : 0.02
% 3.79/1.63  MUC search           : 0.00
% 3.79/1.63  Cooper               : 0.00
% 3.79/1.63  Total                : 0.85
% 3.79/1.63  Index Insertion      : 0.00
% 3.79/1.63  Index Deletion       : 0.00
% 3.79/1.63  Index Matching       : 0.00
% 3.79/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
