%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :   69 (  84 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 126 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

tff(c_78,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_146,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_138,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k1_tarski(A_59),B_60)
      | r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,(
    ! [B_60,A_59] :
      ( r1_xboole_0(B_60,k1_tarski(A_59))
      | r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_386,plain,(
    ! [B_118,A_119] :
      ( k10_relat_1(B_118,A_119) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_118),A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1988,plain,(
    ! [B_4129,A_4130] :
      ( k10_relat_1(B_4129,k1_tarski(A_4130)) = k1_xboole_0
      | ~ v1_relat_1(B_4129)
      | r2_hidden(A_4130,k2_relat_1(B_4129)) ) ),
    inference(resolution,[status(thm)],[c_145,c_386])).

tff(c_72,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_177,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_72])).

tff(c_2019,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1988,c_177])).

tff(c_2031,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2019])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_2031])).

tff(c_2035,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_16,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2363,plain,(
    ! [A_4244,B_4245,C_4246,D_4247] : k3_enumset1(A_4244,A_4244,B_4245,C_4246,D_4247) = k2_enumset1(A_4244,B_4245,C_4246,D_4247) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37,G_43,E_39] : r2_hidden(G_43,k3_enumset1(A_35,B_36,C_37,G_43,E_39)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2387,plain,(
    ! [C_4248,A_4249,B_4250,D_4251] : r2_hidden(C_4248,k2_enumset1(A_4249,B_4250,C_4248,D_4251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2363,c_34])).

tff(c_2394,plain,(
    ! [B_4252,A_4253,C_4254] : r2_hidden(B_4252,k1_enumset1(A_4253,B_4252,C_4254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2387])).

tff(c_2401,plain,(
    ! [A_4255,B_4256] : r2_hidden(A_4255,k2_tarski(A_4255,B_4256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2394])).

tff(c_2406,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2401])).

tff(c_2269,plain,(
    ! [B_4233,A_4234] :
      ( r1_xboole_0(k2_relat_1(B_4233),A_4234)
      | k10_relat_1(B_4233,A_4234) != k1_xboole_0
      | ~ v1_relat_1(B_4233) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2322,plain,(
    ! [A_4239,B_4240] :
      ( r1_xboole_0(A_4239,k2_relat_1(B_4240))
      | k10_relat_1(B_4240,A_4239) != k1_xboole_0
      | ~ v1_relat_1(B_4240) ) ),
    inference(resolution,[status(thm)],[c_2269,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3875,plain,(
    ! [A_8172,B_8173] :
      ( k4_xboole_0(A_8172,k2_relat_1(B_8173)) = A_8172
      | k10_relat_1(B_8173,A_8172) != k1_xboole_0
      | ~ v1_relat_1(B_8173) ) ),
    inference(resolution,[status(thm)],[c_2322,c_12])).

tff(c_2034,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2116,plain,(
    ! [A_4217,B_4218,C_4219] :
      ( ~ r1_xboole_0(A_4217,B_4218)
      | ~ r2_hidden(C_4219,B_4218)
      | ~ r2_hidden(C_4219,A_4217) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2521,plain,(
    ! [C_4298,B_4299,A_4300] :
      ( ~ r2_hidden(C_4298,B_4299)
      | ~ r2_hidden(C_4298,A_4300)
      | k4_xboole_0(A_4300,B_4299) != A_4300 ) ),
    inference(resolution,[status(thm)],[c_14,c_2116])).

tff(c_2575,plain,(
    ! [A_4300] :
      ( ~ r2_hidden('#skF_4',A_4300)
      | k4_xboole_0(A_4300,k2_relat_1('#skF_5')) != A_4300 ) ),
    inference(resolution,[status(thm)],[c_2034,c_2521])).

tff(c_3894,plain,(
    ! [A_8172] :
      ( ~ r2_hidden('#skF_4',A_8172)
      | k10_relat_1('#skF_5',A_8172) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3875,c_2575])).

tff(c_3951,plain,(
    ! [A_8221] :
      ( ~ r2_hidden('#skF_4',A_8221)
      | k10_relat_1('#skF_5',A_8221) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3894])).

tff(c_3979,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2406,c_3951])).

tff(c_4024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_3979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.30  
% 5.72/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.72/2.30  
% 5.72/2.30  %Foreground sorts:
% 5.72/2.30  
% 5.72/2.30  
% 5.72/2.30  %Background operators:
% 5.72/2.30  
% 5.72/2.30  
% 5.72/2.30  %Foreground operators:
% 5.72/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.72/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 5.72/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.72/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.72/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.72/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.72/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.72/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.72/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.72/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.72/2.30  tff('#skF_5', type, '#skF_5': $i).
% 5.72/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.72/2.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.72/2.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.72/2.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 5.72/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.72/2.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.72/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.72/2.30  tff('#skF_4', type, '#skF_4': $i).
% 5.72/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.72/2.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.72/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.72/2.30  
% 6.01/2.31  tff(f_105, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 6.01/2.31  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.01/2.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.01/2.31  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 6.01/2.31  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.01/2.31  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.01/2.31  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.01/2.31  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.01/2.31  tff(f_91, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 6.01/2.31  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.01/2.31  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.01/2.31  tff(c_78, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.01/2.31  tff(c_146, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 6.01/2.31  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.01/2.31  tff(c_138, plain, (![A_59, B_60]: (r1_xboole_0(k1_tarski(A_59), B_60) | r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.01/2.31  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.01/2.31  tff(c_145, plain, (![B_60, A_59]: (r1_xboole_0(B_60, k1_tarski(A_59)) | r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_138, c_2])).
% 6.01/2.31  tff(c_386, plain, (![B_118, A_119]: (k10_relat_1(B_118, A_119)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_118), A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.01/2.31  tff(c_1988, plain, (![B_4129, A_4130]: (k10_relat_1(B_4129, k1_tarski(A_4130))=k1_xboole_0 | ~v1_relat_1(B_4129) | r2_hidden(A_4130, k2_relat_1(B_4129)))), inference(resolution, [status(thm)], [c_145, c_386])).
% 6.01/2.31  tff(c_72, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.01/2.31  tff(c_177, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_146, c_72])).
% 6.01/2.31  tff(c_2019, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1988, c_177])).
% 6.01/2.31  tff(c_2031, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2019])).
% 6.01/2.31  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_2031])).
% 6.01/2.31  tff(c_2035, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 6.01/2.31  tff(c_16, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.01/2.31  tff(c_18, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.01/2.31  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.01/2.31  tff(c_2363, plain, (![A_4244, B_4245, C_4246, D_4247]: (k3_enumset1(A_4244, A_4244, B_4245, C_4246, D_4247)=k2_enumset1(A_4244, B_4245, C_4246, D_4247))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.01/2.31  tff(c_34, plain, (![A_35, B_36, C_37, G_43, E_39]: (r2_hidden(G_43, k3_enumset1(A_35, B_36, C_37, G_43, E_39)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.01/2.31  tff(c_2387, plain, (![C_4248, A_4249, B_4250, D_4251]: (r2_hidden(C_4248, k2_enumset1(A_4249, B_4250, C_4248, D_4251)))), inference(superposition, [status(thm), theory('equality')], [c_2363, c_34])).
% 6.01/2.31  tff(c_2394, plain, (![B_4252, A_4253, C_4254]: (r2_hidden(B_4252, k1_enumset1(A_4253, B_4252, C_4254)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2387])).
% 6.01/2.31  tff(c_2401, plain, (![A_4255, B_4256]: (r2_hidden(A_4255, k2_tarski(A_4255, B_4256)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2394])).
% 6.01/2.31  tff(c_2406, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2401])).
% 6.01/2.31  tff(c_2269, plain, (![B_4233, A_4234]: (r1_xboole_0(k2_relat_1(B_4233), A_4234) | k10_relat_1(B_4233, A_4234)!=k1_xboole_0 | ~v1_relat_1(B_4233))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.01/2.31  tff(c_2322, plain, (![A_4239, B_4240]: (r1_xboole_0(A_4239, k2_relat_1(B_4240)) | k10_relat_1(B_4240, A_4239)!=k1_xboole_0 | ~v1_relat_1(B_4240))), inference(resolution, [status(thm)], [c_2269, c_2])).
% 6.01/2.31  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.01/2.31  tff(c_3875, plain, (![A_8172, B_8173]: (k4_xboole_0(A_8172, k2_relat_1(B_8173))=A_8172 | k10_relat_1(B_8173, A_8172)!=k1_xboole_0 | ~v1_relat_1(B_8173))), inference(resolution, [status(thm)], [c_2322, c_12])).
% 6.01/2.31  tff(c_2034, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 6.01/2.31  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.01/2.31  tff(c_2116, plain, (![A_4217, B_4218, C_4219]: (~r1_xboole_0(A_4217, B_4218) | ~r2_hidden(C_4219, B_4218) | ~r2_hidden(C_4219, A_4217))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.01/2.31  tff(c_2521, plain, (![C_4298, B_4299, A_4300]: (~r2_hidden(C_4298, B_4299) | ~r2_hidden(C_4298, A_4300) | k4_xboole_0(A_4300, B_4299)!=A_4300)), inference(resolution, [status(thm)], [c_14, c_2116])).
% 6.01/2.31  tff(c_2575, plain, (![A_4300]: (~r2_hidden('#skF_4', A_4300) | k4_xboole_0(A_4300, k2_relat_1('#skF_5'))!=A_4300)), inference(resolution, [status(thm)], [c_2034, c_2521])).
% 6.01/2.31  tff(c_3894, plain, (![A_8172]: (~r2_hidden('#skF_4', A_8172) | k10_relat_1('#skF_5', A_8172)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3875, c_2575])).
% 6.01/2.31  tff(c_3951, plain, (![A_8221]: (~r2_hidden('#skF_4', A_8221) | k10_relat_1('#skF_5', A_8221)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3894])).
% 6.01/2.31  tff(c_3979, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2406, c_3951])).
% 6.01/2.31  tff(c_4024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2035, c_3979])).
% 6.01/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.01/2.31  
% 6.01/2.31  Inference rules
% 6.01/2.31  ----------------------
% 6.01/2.31  #Ref     : 0
% 6.01/2.31  #Sup     : 713
% 6.01/2.31  #Fact    : 40
% 6.01/2.31  #Define  : 0
% 6.01/2.31  #Split   : 1
% 6.01/2.31  #Chain   : 0
% 6.01/2.31  #Close   : 0
% 6.01/2.31  
% 6.01/2.31  Ordering : KBO
% 6.01/2.31  
% 6.01/2.31  Simplification rules
% 6.01/2.31  ----------------------
% 6.01/2.32  #Subsume      : 193
% 6.01/2.32  #Demod        : 61
% 6.01/2.32  #Tautology    : 155
% 6.01/2.32  #SimpNegUnit  : 2
% 6.01/2.32  #BackRed      : 0
% 6.01/2.32  
% 6.01/2.32  #Partial instantiations: 2608
% 6.01/2.32  #Strategies tried      : 1
% 6.01/2.32  
% 6.01/2.32  Timing (in seconds)
% 6.01/2.32  ----------------------
% 6.01/2.32  Preprocessing        : 0.49
% 6.01/2.32  Parsing              : 0.27
% 6.01/2.32  CNF conversion       : 0.03
% 6.01/2.32  Main loop            : 1.01
% 6.01/2.32  Inferencing          : 0.50
% 6.01/2.32  Reduction            : 0.22
% 6.01/2.32  Demodulation         : 0.16
% 6.01/2.32  BG Simplification    : 0.07
% 6.01/2.32  Subsumption          : 0.16
% 6.01/2.32  Abstraction          : 0.08
% 6.01/2.32  MUC search           : 0.00
% 6.01/2.32  Cooper               : 0.00
% 6.01/2.32  Total                : 1.53
% 6.01/2.32  Index Insertion      : 0.00
% 6.01/2.32  Index Deletion       : 0.00
% 6.01/2.32  Index Matching       : 0.00
% 6.01/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
