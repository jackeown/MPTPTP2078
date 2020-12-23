%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 160 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 313 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_71,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_62,plain,(
    ! [A_50] : r2_hidden(A_50,k1_ordinal1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,
    ( r2_hidden('#skF_4',k1_ordinal1('#skF_5'))
    | r1_ordinal1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_133,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_80])).

tff(c_60,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_ordinal1(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_101,plain,(
    ! [A_64] :
      ( v1_ordinal1(A_64)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_109,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_101])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_557,plain,(
    ! [A_133,B_134] :
      ( r2_hidden(A_133,B_134)
      | ~ r2_xboole_0(A_133,B_134)
      | ~ v3_ordinal1(B_134)
      | ~ v1_ordinal1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3829,plain,(
    ! [A_361,B_362] :
      ( r2_hidden(A_361,B_362)
      | ~ v3_ordinal1(B_362)
      | ~ v1_ordinal1(A_361)
      | B_362 = A_361
      | ~ r1_tarski(A_361,B_362) ) ),
    inference(resolution,[status(thm)],[c_20,c_557])).

tff(c_50,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_tarski(A_43)) = k1_ordinal1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_227,plain,(
    ! [D_91,A_92,B_93] :
      ( ~ r2_hidden(D_91,A_92)
      | r2_hidden(D_91,k2_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_247,plain,(
    ! [D_94,A_95] :
      ( ~ r2_hidden(D_94,A_95)
      | r2_hidden(D_94,k1_ordinal1(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_227])).

tff(c_264,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_247,c_110])).

tff(c_4211,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3829,c_264])).

tff(c_4338,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70,c_4211])).

tff(c_4347,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4338])).

tff(c_4353,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4347])).

tff(c_4360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_133,c_4353])).

tff(c_4361,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4338])).

tff(c_4367,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_110])).

tff(c_4373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4367])).

tff(c_4374,plain,(
    ~ r1_ordinal1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_108,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_4375,plain,(
    r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5048,plain,(
    ! [D_450,B_451,A_452] :
      ( r2_hidden(D_450,B_451)
      | r2_hidden(D_450,A_452)
      | ~ r2_hidden(D_450,k2_xboole_0(A_452,B_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6771,plain,(
    ! [D_604,A_605] :
      ( r2_hidden(D_604,k1_tarski(A_605))
      | r2_hidden(D_604,A_605)
      | ~ r2_hidden(D_604,k1_ordinal1(A_605)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5048])).

tff(c_44,plain,(
    ! [A_41] : k3_tarski(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4417,plain,(
    ! [A_373,B_374] :
      ( r1_tarski(A_373,k3_tarski(B_374))
      | ~ r2_hidden(A_373,B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4428,plain,(
    ! [A_373,A_41] :
      ( r1_tarski(A_373,A_41)
      | ~ r2_hidden(A_373,k1_tarski(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4417])).

tff(c_7239,plain,(
    ! [D_611,A_612] :
      ( r1_tarski(D_611,A_612)
      | r2_hidden(D_611,A_612)
      | ~ r2_hidden(D_611,k1_ordinal1(A_612)) ) ),
    inference(resolution,[status(thm)],[c_6771,c_4428])).

tff(c_7299,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4375,c_7239])).

tff(c_7301,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7299])).

tff(c_52,plain,(
    ! [B_47,A_44] :
      ( r1_tarski(B_47,A_44)
      | ~ r2_hidden(B_47,A_44)
      | ~ v1_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7304,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7301,c_52])).

tff(c_7310,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_7304])).

tff(c_58,plain,(
    ! [A_48,B_49] :
      ( r1_ordinal1(A_48,B_49)
      | ~ r1_tarski(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7352,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7310,c_58])).

tff(c_7355,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_7352])).

tff(c_7357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4374,c_7355])).

tff(c_7358,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7299])).

tff(c_7362,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7358,c_58])).

tff(c_7365,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_7362])).

tff(c_7367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4374,c_7365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:40:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.51  
% 6.98/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.51  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 6.98/2.51  
% 6.98/2.51  %Foreground sorts:
% 6.98/2.51  
% 6.98/2.51  
% 6.98/2.51  %Background operators:
% 6.98/2.51  
% 6.98/2.51  
% 6.98/2.51  %Foreground operators:
% 6.98/2.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.98/2.51  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.51  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 6.98/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.98/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.98/2.51  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.98/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.51  tff('#skF_5', type, '#skF_5': $i).
% 6.98/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.98/2.51  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.98/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.51  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 6.98/2.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.98/2.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.98/2.51  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.51  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.98/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.51  
% 6.98/2.52  tff(f_88, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.98/2.52  tff(f_121, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.98/2.52  tff(f_86, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.98/2.52  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 6.98/2.52  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.98/2.52  tff(f_97, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 6.98/2.52  tff(f_71, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.98/2.52  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.98/2.52  tff(f_63, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 6.98/2.52  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.98/2.52  tff(f_78, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 6.98/2.52  tff(c_62, plain, (![A_50]: (r2_hidden(A_50, k1_ordinal1(A_50)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.98/2.52  tff(c_72, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.98/2.52  tff(c_70, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.98/2.52  tff(c_74, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.98/2.52  tff(c_110, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_74])).
% 6.98/2.52  tff(c_80, plain, (r2_hidden('#skF_4', k1_ordinal1('#skF_5')) | r1_ordinal1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.98/2.52  tff(c_133, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_110, c_80])).
% 6.98/2.52  tff(c_60, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~r1_ordinal1(A_48, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_101, plain, (![A_64]: (v1_ordinal1(A_64) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.98/2.52  tff(c_109, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_101])).
% 6.98/2.52  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.98/2.52  tff(c_557, plain, (![A_133, B_134]: (r2_hidden(A_133, B_134) | ~r2_xboole_0(A_133, B_134) | ~v3_ordinal1(B_134) | ~v1_ordinal1(A_133))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.98/2.52  tff(c_3829, plain, (![A_361, B_362]: (r2_hidden(A_361, B_362) | ~v3_ordinal1(B_362) | ~v1_ordinal1(A_361) | B_362=A_361 | ~r1_tarski(A_361, B_362))), inference(resolution, [status(thm)], [c_20, c_557])).
% 6.98/2.52  tff(c_50, plain, (![A_43]: (k2_xboole_0(A_43, k1_tarski(A_43))=k1_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.98/2.52  tff(c_227, plain, (![D_91, A_92, B_93]: (~r2_hidden(D_91, A_92) | r2_hidden(D_91, k2_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.98/2.52  tff(c_247, plain, (![D_94, A_95]: (~r2_hidden(D_94, A_95) | r2_hidden(D_94, k1_ordinal1(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_227])).
% 6.98/2.52  tff(c_264, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_247, c_110])).
% 6.98/2.52  tff(c_4211, plain, (~v3_ordinal1('#skF_5') | ~v1_ordinal1('#skF_4') | '#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3829, c_264])).
% 6.98/2.52  tff(c_4338, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70, c_4211])).
% 6.98/2.52  tff(c_4347, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_4338])).
% 6.98/2.52  tff(c_4353, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_4347])).
% 6.98/2.52  tff(c_4360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_133, c_4353])).
% 6.98/2.52  tff(c_4361, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_4338])).
% 6.98/2.52  tff(c_4367, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_110])).
% 6.98/2.52  tff(c_4373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_4367])).
% 6.98/2.52  tff(c_4374, plain, (~r1_ordinal1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 6.98/2.52  tff(c_108, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_101])).
% 6.98/2.52  tff(c_4375, plain, (r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 6.98/2.52  tff(c_5048, plain, (![D_450, B_451, A_452]: (r2_hidden(D_450, B_451) | r2_hidden(D_450, A_452) | ~r2_hidden(D_450, k2_xboole_0(A_452, B_451)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.98/2.52  tff(c_6771, plain, (![D_604, A_605]: (r2_hidden(D_604, k1_tarski(A_605)) | r2_hidden(D_604, A_605) | ~r2_hidden(D_604, k1_ordinal1(A_605)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5048])).
% 6.98/2.52  tff(c_44, plain, (![A_41]: (k3_tarski(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.98/2.52  tff(c_4417, plain, (![A_373, B_374]: (r1_tarski(A_373, k3_tarski(B_374)) | ~r2_hidden(A_373, B_374))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.98/2.52  tff(c_4428, plain, (![A_373, A_41]: (r1_tarski(A_373, A_41) | ~r2_hidden(A_373, k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4417])).
% 6.98/2.52  tff(c_7239, plain, (![D_611, A_612]: (r1_tarski(D_611, A_612) | r2_hidden(D_611, A_612) | ~r2_hidden(D_611, k1_ordinal1(A_612)))), inference(resolution, [status(thm)], [c_6771, c_4428])).
% 6.98/2.52  tff(c_7299, plain, (r1_tarski('#skF_4', '#skF_5') | r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4375, c_7239])).
% 6.98/2.52  tff(c_7301, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_7299])).
% 6.98/2.52  tff(c_52, plain, (![B_47, A_44]: (r1_tarski(B_47, A_44) | ~r2_hidden(B_47, A_44) | ~v1_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.98/2.52  tff(c_7304, plain, (r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_7301, c_52])).
% 6.98/2.52  tff(c_7310, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_7304])).
% 6.98/2.52  tff(c_58, plain, (![A_48, B_49]: (r1_ordinal1(A_48, B_49) | ~r1_tarski(A_48, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_7352, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_7310, c_58])).
% 6.98/2.52  tff(c_7355, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_7352])).
% 6.98/2.52  tff(c_7357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4374, c_7355])).
% 6.98/2.52  tff(c_7358, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_7299])).
% 6.98/2.52  tff(c_7362, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_7358, c_58])).
% 6.98/2.52  tff(c_7365, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_7362])).
% 6.98/2.52  tff(c_7367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4374, c_7365])).
% 6.98/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.52  
% 6.98/2.52  Inference rules
% 6.98/2.52  ----------------------
% 6.98/2.52  #Ref     : 0
% 6.98/2.52  #Sup     : 1515
% 6.98/2.52  #Fact    : 12
% 6.98/2.52  #Define  : 0
% 6.98/2.52  #Split   : 7
% 6.98/2.52  #Chain   : 0
% 6.98/2.52  #Close   : 0
% 6.98/2.52  
% 6.98/2.52  Ordering : KBO
% 6.98/2.52  
% 6.98/2.52  Simplification rules
% 6.98/2.52  ----------------------
% 6.98/2.52  #Subsume      : 241
% 6.98/2.52  #Demod        : 96
% 6.98/2.52  #Tautology    : 87
% 6.98/2.52  #SimpNegUnit  : 26
% 6.98/2.52  #BackRed      : 8
% 6.98/2.52  
% 6.98/2.52  #Partial instantiations: 0
% 6.98/2.52  #Strategies tried      : 1
% 6.98/2.52  
% 6.98/2.52  Timing (in seconds)
% 6.98/2.52  ----------------------
% 6.98/2.52  Preprocessing        : 0.38
% 6.98/2.52  Parsing              : 0.20
% 6.98/2.52  CNF conversion       : 0.03
% 6.98/2.52  Main loop            : 1.25
% 6.98/2.52  Inferencing          : 0.39
% 6.98/2.52  Reduction            : 0.35
% 6.98/2.52  Demodulation         : 0.21
% 6.98/2.53  BG Simplification    : 0.05
% 6.98/2.53  Subsumption          : 0.35
% 6.98/2.53  Abstraction          : 0.06
% 6.98/2.53  MUC search           : 0.00
% 6.98/2.53  Cooper               : 0.00
% 6.98/2.53  Total                : 1.66
% 6.98/2.53  Index Insertion      : 0.00
% 6.98/2.53  Index Deletion       : 0.00
% 6.98/2.53  Index Matching       : 0.00
% 6.98/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
