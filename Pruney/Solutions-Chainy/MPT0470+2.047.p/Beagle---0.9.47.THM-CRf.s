%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 180 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_11 > #skF_2 > #skF_8 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

tff(c_56,plain,
    ( k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_96,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    ! [A_124] :
      ( v1_relat_1(A_124)
      | ~ v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_52,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | r2_hidden(k4_tarski('#skF_10'(A_119),'#skF_11'(A_119)),A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_625,plain,(
    ! [D_192,B_193,A_194,E_195] :
      ( r2_hidden(k4_tarski(D_192,'#skF_4'(B_193,A_194,k5_relat_1(A_194,B_193),D_192,E_195)),A_194)
      | ~ r2_hidden(k4_tarski(D_192,E_195),k5_relat_1(A_194,B_193))
      | ~ v1_relat_1(k5_relat_1(A_194,B_193))
      | ~ v1_relat_1(B_193)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [A_140,B_141,C_142] :
      ( ~ r1_xboole_0(A_140,B_141)
      | ~ r2_hidden(C_142,B_141)
      | ~ r2_hidden(C_142,A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [C_148,B_149,A_150] :
      ( ~ r2_hidden(C_148,B_149)
      | ~ r2_hidden(C_148,A_150)
      | k4_xboole_0(A_150,B_149) != A_150 ) ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_155,plain,(
    ! [C_151,A_152] :
      ( ~ r2_hidden(C_151,A_152)
      | k4_xboole_0(A_152,k1_tarski(C_151)) != A_152 ) ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_160,plain,(
    ! [C_151] : ~ r2_hidden(C_151,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_634,plain,(
    ! [D_192,E_195,B_193] :
      ( ~ r2_hidden(k4_tarski(D_192,E_195),k5_relat_1(k1_xboole_0,B_193))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_193))
      | ~ v1_relat_1(B_193)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_625,c_160])).

tff(c_1927,plain,(
    ! [D_263,E_264,B_265] :
      ( ~ r2_hidden(k4_tarski(D_263,E_264),k5_relat_1(k1_xboole_0,B_265))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_265))
      | ~ v1_relat_1(B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_634])).

tff(c_1973,plain,(
    ! [B_270] :
      ( ~ v1_relat_1(B_270)
      | k5_relat_1(k1_xboole_0,B_270) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_270)) ) ),
    inference(resolution,[status(thm)],[c_54,c_1927])).

tff(c_1977,plain,(
    ! [B_118] :
      ( k5_relat_1(k1_xboole_0,B_118) = k1_xboole_0
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_1973])).

tff(c_1981,plain,(
    ! [B_271] :
      ( k5_relat_1(k1_xboole_0,B_271) = k1_xboole_0
      | ~ v1_relat_1(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1977])).

tff(c_1990,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_1981])).

tff(c_1996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1990])).

tff(c_1997,plain,(
    k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2648,plain,(
    ! [B_345,A_346,D_347,E_348] :
      ( r2_hidden(k4_tarski('#skF_4'(B_345,A_346,k5_relat_1(A_346,B_345),D_347,E_348),E_348),B_345)
      | ~ r2_hidden(k4_tarski(D_347,E_348),k5_relat_1(A_346,B_345))
      | ~ v1_relat_1(k5_relat_1(A_346,B_345))
      | ~ v1_relat_1(B_345)
      | ~ v1_relat_1(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2027,plain,(
    ! [A_282,B_283,C_284] :
      ( ~ r1_xboole_0(A_282,B_283)
      | ~ r2_hidden(C_284,B_283)
      | ~ r2_hidden(C_284,A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2047,plain,(
    ! [C_289,B_290,A_291] :
      ( ~ r2_hidden(C_289,B_290)
      | ~ r2_hidden(C_289,A_291)
      | k4_xboole_0(A_291,B_290) != A_291 ) ),
    inference(resolution,[status(thm)],[c_14,c_2027])).

tff(c_2058,plain,(
    ! [C_294,A_295] :
      ( ~ r2_hidden(C_294,A_295)
      | k4_xboole_0(A_295,k1_tarski(C_294)) != A_295 ) ),
    inference(resolution,[status(thm)],[c_18,c_2047])).

tff(c_2063,plain,(
    ! [C_294] : ~ r2_hidden(C_294,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2058])).

tff(c_2659,plain,(
    ! [D_347,E_348,A_346] :
      ( ~ r2_hidden(k4_tarski(D_347,E_348),k5_relat_1(A_346,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_346,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_346) ) ),
    inference(resolution,[status(thm)],[c_2648,c_2063])).

tff(c_3838,plain,(
    ! [D_403,E_404,A_405] :
      ( ~ r2_hidden(k4_tarski(D_403,E_404),k5_relat_1(A_405,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_405,k1_xboole_0))
      | ~ v1_relat_1(A_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2659])).

tff(c_3874,plain,(
    ! [A_406] :
      ( ~ v1_relat_1(A_406)
      | k5_relat_1(A_406,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_406,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3838])).

tff(c_3878,plain,(
    ! [A_117] :
      ( k5_relat_1(A_117,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_52,c_3874])).

tff(c_3892,plain,(
    ! [A_411] :
      ( k5_relat_1(A_411,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_3878])).

tff(c_3901,plain,(
    k5_relat_1('#skF_12',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_3892])).

tff(c_3907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1997,c_3901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.83  
% 4.74/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.83  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_11 > #skF_2 > #skF_8 > #skF_1 > #skF_12
% 4.74/1.83  
% 4.74/1.83  %Foreground sorts:
% 4.74/1.83  
% 4.74/1.83  
% 4.74/1.83  %Background operators:
% 4.74/1.83  
% 4.74/1.83  
% 4.74/1.83  %Foreground operators:
% 4.74/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.83  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.74/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.74/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.74/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 4.74/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.74/1.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.74/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.83  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.74/1.83  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.74/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.83  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.74/1.83  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.74/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.83  tff('#skF_11', type, '#skF_11': $i > $i).
% 4.74/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.74/1.83  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.74/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.74/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.83  tff('#skF_12', type, '#skF_12': $i).
% 4.74/1.83  
% 4.80/1.84  tff(f_104, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.80/1.84  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.84  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.80/1.84  tff(f_89, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.80/1.84  tff(f_97, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 4.80/1.84  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 4.80/1.84  tff(f_46, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.80/1.84  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.80/1.84  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.80/1.84  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.80/1.84  tff(c_56, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.80/1.84  tff(c_96, plain, (k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 4.80/1.84  tff(c_58, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.80/1.84  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.80/1.84  tff(c_67, plain, (![A_124]: (v1_relat_1(A_124) | ~v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.80/1.84  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_67])).
% 4.80/1.84  tff(c_52, plain, (![A_117, B_118]: (v1_relat_1(k5_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.84  tff(c_54, plain, (![A_119]: (k1_xboole_0=A_119 | r2_hidden(k4_tarski('#skF_10'(A_119), '#skF_11'(A_119)), A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.80/1.84  tff(c_625, plain, (![D_192, B_193, A_194, E_195]: (r2_hidden(k4_tarski(D_192, '#skF_4'(B_193, A_194, k5_relat_1(A_194, B_193), D_192, E_195)), A_194) | ~r2_hidden(k4_tarski(D_192, E_195), k5_relat_1(A_194, B_193)) | ~v1_relat_1(k5_relat_1(A_194, B_193)) | ~v1_relat_1(B_193) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.84  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.80/1.84  tff(c_18, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/1.84  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.80/1.84  tff(c_116, plain, (![A_140, B_141, C_142]: (~r1_xboole_0(A_140, B_141) | ~r2_hidden(C_142, B_141) | ~r2_hidden(C_142, A_140))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.80/1.84  tff(c_142, plain, (![C_148, B_149, A_150]: (~r2_hidden(C_148, B_149) | ~r2_hidden(C_148, A_150) | k4_xboole_0(A_150, B_149)!=A_150)), inference(resolution, [status(thm)], [c_14, c_116])).
% 4.80/1.84  tff(c_155, plain, (![C_151, A_152]: (~r2_hidden(C_151, A_152) | k4_xboole_0(A_152, k1_tarski(C_151))!=A_152)), inference(resolution, [status(thm)], [c_18, c_142])).
% 4.80/1.84  tff(c_160, plain, (![C_151]: (~r2_hidden(C_151, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_155])).
% 4.80/1.84  tff(c_634, plain, (![D_192, E_195, B_193]: (~r2_hidden(k4_tarski(D_192, E_195), k5_relat_1(k1_xboole_0, B_193)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_193)) | ~v1_relat_1(B_193) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_625, c_160])).
% 4.80/1.84  tff(c_1927, plain, (![D_263, E_264, B_265]: (~r2_hidden(k4_tarski(D_263, E_264), k5_relat_1(k1_xboole_0, B_265)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_265)) | ~v1_relat_1(B_265))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_634])).
% 4.80/1.84  tff(c_1973, plain, (![B_270]: (~v1_relat_1(B_270) | k5_relat_1(k1_xboole_0, B_270)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_270)))), inference(resolution, [status(thm)], [c_54, c_1927])).
% 4.80/1.84  tff(c_1977, plain, (![B_118]: (k5_relat_1(k1_xboole_0, B_118)=k1_xboole_0 | ~v1_relat_1(B_118) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_1973])).
% 4.80/1.84  tff(c_1981, plain, (![B_271]: (k5_relat_1(k1_xboole_0, B_271)=k1_xboole_0 | ~v1_relat_1(B_271))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1977])).
% 4.80/1.84  tff(c_1990, plain, (k5_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_1981])).
% 4.80/1.84  tff(c_1996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1990])).
% 4.80/1.84  tff(c_1997, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 4.80/1.84  tff(c_2648, plain, (![B_345, A_346, D_347, E_348]: (r2_hidden(k4_tarski('#skF_4'(B_345, A_346, k5_relat_1(A_346, B_345), D_347, E_348), E_348), B_345) | ~r2_hidden(k4_tarski(D_347, E_348), k5_relat_1(A_346, B_345)) | ~v1_relat_1(k5_relat_1(A_346, B_345)) | ~v1_relat_1(B_345) | ~v1_relat_1(A_346))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.84  tff(c_2027, plain, (![A_282, B_283, C_284]: (~r1_xboole_0(A_282, B_283) | ~r2_hidden(C_284, B_283) | ~r2_hidden(C_284, A_282))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.80/1.84  tff(c_2047, plain, (![C_289, B_290, A_291]: (~r2_hidden(C_289, B_290) | ~r2_hidden(C_289, A_291) | k4_xboole_0(A_291, B_290)!=A_291)), inference(resolution, [status(thm)], [c_14, c_2027])).
% 4.80/1.84  tff(c_2058, plain, (![C_294, A_295]: (~r2_hidden(C_294, A_295) | k4_xboole_0(A_295, k1_tarski(C_294))!=A_295)), inference(resolution, [status(thm)], [c_18, c_2047])).
% 4.80/1.84  tff(c_2063, plain, (![C_294]: (~r2_hidden(C_294, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2058])).
% 4.80/1.84  tff(c_2659, plain, (![D_347, E_348, A_346]: (~r2_hidden(k4_tarski(D_347, E_348), k5_relat_1(A_346, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_346, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_346))), inference(resolution, [status(thm)], [c_2648, c_2063])).
% 4.80/1.84  tff(c_3838, plain, (![D_403, E_404, A_405]: (~r2_hidden(k4_tarski(D_403, E_404), k5_relat_1(A_405, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_405, k1_xboole_0)) | ~v1_relat_1(A_405))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2659])).
% 4.80/1.84  tff(c_3874, plain, (![A_406]: (~v1_relat_1(A_406) | k5_relat_1(A_406, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_406, k1_xboole_0)))), inference(resolution, [status(thm)], [c_54, c_3838])).
% 4.80/1.84  tff(c_3878, plain, (![A_117]: (k5_relat_1(A_117, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_52, c_3874])).
% 4.80/1.84  tff(c_3892, plain, (![A_411]: (k5_relat_1(A_411, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_411))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_3878])).
% 4.80/1.84  tff(c_3901, plain, (k5_relat_1('#skF_12', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_3892])).
% 4.80/1.84  tff(c_3907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1997, c_3901])).
% 4.80/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.84  
% 4.80/1.84  Inference rules
% 4.80/1.84  ----------------------
% 4.80/1.84  #Ref     : 0
% 4.80/1.84  #Sup     : 912
% 4.80/1.84  #Fact    : 0
% 4.80/1.84  #Define  : 0
% 4.80/1.84  #Split   : 1
% 4.80/1.84  #Chain   : 0
% 4.80/1.84  #Close   : 0
% 4.80/1.84  
% 4.80/1.84  Ordering : KBO
% 4.80/1.84  
% 4.80/1.84  Simplification rules
% 4.80/1.84  ----------------------
% 4.80/1.84  #Subsume      : 254
% 4.80/1.84  #Demod        : 199
% 4.80/1.84  #Tautology    : 338
% 4.80/1.84  #SimpNegUnit  : 5
% 4.80/1.84  #BackRed      : 0
% 4.80/1.84  
% 4.80/1.84  #Partial instantiations: 0
% 4.80/1.84  #Strategies tried      : 1
% 4.80/1.84  
% 4.80/1.84  Timing (in seconds)
% 4.80/1.84  ----------------------
% 4.80/1.84  Preprocessing        : 0.33
% 4.80/1.84  Parsing              : 0.16
% 4.80/1.84  CNF conversion       : 0.03
% 4.80/1.84  Main loop            : 0.76
% 4.80/1.84  Inferencing          : 0.29
% 4.80/1.84  Reduction            : 0.20
% 4.80/1.85  Demodulation         : 0.14
% 4.80/1.85  BG Simplification    : 0.04
% 4.80/1.85  Subsumption          : 0.16
% 4.80/1.85  Abstraction          : 0.05
% 4.80/1.85  MUC search           : 0.00
% 4.80/1.85  Cooper               : 0.00
% 4.80/1.85  Total                : 1.12
% 4.80/1.85  Index Insertion      : 0.00
% 4.80/1.85  Index Deletion       : 0.00
% 4.80/1.85  Index Matching       : 0.00
% 4.80/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
