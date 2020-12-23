%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 17.19s
% Output     : CNFRefutation 17.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 183 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 359 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_81,axiom,(
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

tff(f_89,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_87,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_60,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_28,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_795,plain,(
    ! [A_181,B_182,C_183,D_184] : k3_enumset1(A_181,A_181,B_182,C_183,D_184) = k2_enumset1(A_181,B_182,C_183,D_184) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_24,G_32,D_27,C_26,E_28] : r2_hidden(G_32,k3_enumset1(A_24,G_32,C_26,D_27,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_854,plain,(
    ! [A_185,B_186,C_187,D_188] : r2_hidden(A_185,k2_enumset1(A_185,B_186,C_187,D_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_48])).

tff(c_892,plain,(
    ! [A_189,B_190,C_191] : r2_hidden(A_189,k1_enumset1(A_189,B_190,C_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_854])).

tff(c_930,plain,(
    ! [A_192,B_193] : r2_hidden(A_192,k2_tarski(A_192,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_892])).

tff(c_989,plain,(
    ! [A_197] : r2_hidden(A_197,k1_tarski(A_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_930])).

tff(c_80,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_tarski(A_34)) = k1_ordinal1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_165,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | r2_hidden(D_58,k2_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [D_58,A_34] :
      ( ~ r2_hidden(D_58,k1_tarski(A_34))
      | r2_hidden(D_58,k1_ordinal1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_165])).

tff(c_1032,plain,(
    ! [A_197] : r2_hidden(A_197,k1_ordinal1(A_197)) ),
    inference(resolution,[status(thm)],[c_989,c_170])).

tff(c_92,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_90,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_100,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_120,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_84,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ r1_ordinal1(A_35,B_36)
      | ~ v3_ordinal1(B_36)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_102,plain,(
    ! [A_45] :
      ( v1_ordinal1(A_45)
      | ~ v3_ordinal1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_102])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_622,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(A_151,B_152)
      | ~ r2_xboole_0(A_151,B_152)
      | ~ v3_ordinal1(B_152)
      | ~ v1_ordinal1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11329,plain,(
    ! [A_28819,B_28820] :
      ( r2_hidden(A_28819,B_28820)
      | ~ v3_ordinal1(B_28820)
      | ~ v1_ordinal1(A_28819)
      | B_28820 = A_28819
      | ~ r1_tarski(A_28819,B_28820) ) ),
    inference(resolution,[status(thm)],[c_22,c_622])).

tff(c_200,plain,(
    ! [D_85,A_86,B_87] :
      ( ~ r2_hidden(D_85,A_86)
      | r2_hidden(D_85,k2_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    ! [D_88,A_89] :
      ( ~ r2_hidden(D_88,A_89)
      | r2_hidden(D_88,k1_ordinal1(A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_200])).

tff(c_94,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_94])).

tff(c_213,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_207,c_151])).

tff(c_11685,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_11329,c_213])).

tff(c_11789,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_90,c_11685])).

tff(c_11795,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11789])).

tff(c_11798,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_11795])).

tff(c_11802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_120,c_11798])).

tff(c_11803,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11789])).

tff(c_11807,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11803,c_151])).

tff(c_11814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_11807])).

tff(c_11816,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_11815,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_11817,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_11828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11815,c_11817])).

tff(c_11830,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_12475,plain,(
    ! [D_29321,B_29322,A_29323] :
      ( r2_hidden(D_29321,B_29322)
      | r2_hidden(D_29321,A_29323)
      | ~ r2_hidden(D_29321,k2_xboole_0(A_29323,B_29322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22438,plain,(
    ! [D_56781,A_56782] :
      ( r2_hidden(D_56781,k1_tarski(A_56782))
      | r2_hidden(D_56781,A_56782)
      | ~ r2_hidden(D_56781,k1_ordinal1(A_56782)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12475])).

tff(c_38,plain,(
    ! [A_23] : k3_tarski(k1_tarski(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_11873,plain,(
    ! [A_29201,B_29202] :
      ( r1_tarski(A_29201,k3_tarski(B_29202))
      | ~ r2_hidden(A_29201,B_29202) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11876,plain,(
    ! [A_29201,A_23] :
      ( r1_tarski(A_29201,A_23)
      | ~ r2_hidden(A_29201,k1_tarski(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_11873])).

tff(c_42481,plain,(
    ! [D_122541,A_122542] :
      ( r1_tarski(D_122541,A_122542)
      | r2_hidden(D_122541,A_122542)
      | ~ r2_hidden(D_122541,k1_ordinal1(A_122542)) ) ),
    inference(resolution,[status(thm)],[c_22438,c_11876])).

tff(c_42564,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_11830,c_42481])).

tff(c_42565,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_42564])).

tff(c_12373,plain,(
    ! [B_29319,A_29320] :
      ( r2_hidden(B_29319,A_29320)
      | r1_ordinal1(A_29320,B_29319)
      | ~ v3_ordinal1(B_29319)
      | ~ v3_ordinal1(A_29320) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12473,plain,(
    ! [A_29320,B_29319] :
      ( ~ r2_hidden(A_29320,B_29319)
      | r1_ordinal1(A_29320,B_29319)
      | ~ v3_ordinal1(B_29319)
      | ~ v3_ordinal1(A_29320) ) ),
    inference(resolution,[status(thm)],[c_12373,c_2])).

tff(c_42568,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42565,c_12473])).

tff(c_42573,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_42568])).

tff(c_42575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11816,c_42573])).

tff(c_42576,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_42564])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( r1_ordinal1(A_35,B_36)
      | ~ r1_tarski(A_35,B_36)
      | ~ v3_ordinal1(B_36)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42580,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42576,c_82])).

tff(c_42583,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_42580])).

tff(c_42585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11816,c_42583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.19/7.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/7.81  
% 17.19/7.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/7.81  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 17.19/7.81  
% 17.19/7.81  %Foreground sorts:
% 17.19/7.81  
% 17.19/7.81  
% 17.19/7.81  %Background operators:
% 17.19/7.81  
% 17.19/7.81  
% 17.19/7.81  %Foreground operators:
% 17.19/7.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.19/7.81  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 17.19/7.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.19/7.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.19/7.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.19/7.81  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 17.19/7.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.19/7.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.19/7.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.19/7.81  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 17.19/7.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.19/7.81  tff('#skF_5', type, '#skF_5': $i).
% 17.19/7.81  tff('#skF_6', type, '#skF_6': $i).
% 17.19/7.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.19/7.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.19/7.81  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 17.19/7.81  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 17.19/7.81  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 17.19/7.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 17.19/7.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.19/7.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.19/7.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.19/7.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.19/7.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 17.19/7.81  
% 17.19/7.83  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 17.19/7.83  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 17.19/7.83  tff(f_52, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 17.19/7.83  tff(f_54, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 17.19/7.83  tff(f_81, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 17.19/7.83  tff(f_89, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 17.19/7.83  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 17.19/7.83  tff(f_125, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 17.19/7.83  tff(f_97, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 17.19/7.83  tff(f_87, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 17.19/7.83  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 17.19/7.83  tff(f_106, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 17.19/7.83  tff(f_60, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 17.19/7.83  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 17.19/7.83  tff(f_115, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 17.19/7.83  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 17.19/7.83  tff(c_28, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.19/7.83  tff(c_30, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.19/7.83  tff(c_32, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.19/7.83  tff(c_795, plain, (![A_181, B_182, C_183, D_184]: (k3_enumset1(A_181, A_181, B_182, C_183, D_184)=k2_enumset1(A_181, B_182, C_183, D_184))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.19/7.83  tff(c_48, plain, (![A_24, G_32, D_27, C_26, E_28]: (r2_hidden(G_32, k3_enumset1(A_24, G_32, C_26, D_27, E_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.19/7.83  tff(c_854, plain, (![A_185, B_186, C_187, D_188]: (r2_hidden(A_185, k2_enumset1(A_185, B_186, C_187, D_188)))), inference(superposition, [status(thm), theory('equality')], [c_795, c_48])).
% 17.19/7.83  tff(c_892, plain, (![A_189, B_190, C_191]: (r2_hidden(A_189, k1_enumset1(A_189, B_190, C_191)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_854])).
% 17.19/7.83  tff(c_930, plain, (![A_192, B_193]: (r2_hidden(A_192, k2_tarski(A_192, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_892])).
% 17.19/7.83  tff(c_989, plain, (![A_197]: (r2_hidden(A_197, k1_tarski(A_197)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_930])).
% 17.19/7.83  tff(c_80, plain, (![A_34]: (k2_xboole_0(A_34, k1_tarski(A_34))=k1_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.19/7.83  tff(c_165, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | r2_hidden(D_58, k2_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.19/7.83  tff(c_170, plain, (![D_58, A_34]: (~r2_hidden(D_58, k1_tarski(A_34)) | r2_hidden(D_58, k1_ordinal1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_165])).
% 17.19/7.83  tff(c_1032, plain, (![A_197]: (r2_hidden(A_197, k1_ordinal1(A_197)))), inference(resolution, [status(thm)], [c_989, c_170])).
% 17.19/7.83  tff(c_92, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.19/7.83  tff(c_90, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.19/7.83  tff(c_100, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.19/7.83  tff(c_120, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_100])).
% 17.19/7.83  tff(c_84, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~r1_ordinal1(A_35, B_36) | ~v3_ordinal1(B_36) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.19/7.83  tff(c_102, plain, (![A_45]: (v1_ordinal1(A_45) | ~v3_ordinal1(A_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.19/7.83  tff(c_110, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_102])).
% 17.19/7.83  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.19/7.83  tff(c_622, plain, (![A_151, B_152]: (r2_hidden(A_151, B_152) | ~r2_xboole_0(A_151, B_152) | ~v3_ordinal1(B_152) | ~v1_ordinal1(A_151))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.19/7.83  tff(c_11329, plain, (![A_28819, B_28820]: (r2_hidden(A_28819, B_28820) | ~v3_ordinal1(B_28820) | ~v1_ordinal1(A_28819) | B_28820=A_28819 | ~r1_tarski(A_28819, B_28820))), inference(resolution, [status(thm)], [c_22, c_622])).
% 17.19/7.83  tff(c_200, plain, (![D_85, A_86, B_87]: (~r2_hidden(D_85, A_86) | r2_hidden(D_85, k2_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.19/7.83  tff(c_207, plain, (![D_88, A_89]: (~r2_hidden(D_88, A_89) | r2_hidden(D_88, k1_ordinal1(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_200])).
% 17.19/7.83  tff(c_94, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.19/7.83  tff(c_151, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_94])).
% 17.19/7.83  tff(c_213, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_207, c_151])).
% 17.19/7.83  tff(c_11685, plain, (~v3_ordinal1('#skF_6') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_11329, c_213])).
% 17.19/7.83  tff(c_11789, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_90, c_11685])).
% 17.19/7.83  tff(c_11795, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_11789])).
% 17.19/7.83  tff(c_11798, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_11795])).
% 17.19/7.83  tff(c_11802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_120, c_11798])).
% 17.19/7.83  tff(c_11803, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_11789])).
% 17.19/7.83  tff(c_11807, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11803, c_151])).
% 17.19/7.83  tff(c_11814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1032, c_11807])).
% 17.19/7.83  tff(c_11816, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_100])).
% 17.19/7.83  tff(c_11815, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_100])).
% 17.19/7.83  tff(c_11817, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_94])).
% 17.19/7.83  tff(c_11828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11815, c_11817])).
% 17.19/7.83  tff(c_11830, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_94])).
% 17.19/7.83  tff(c_12475, plain, (![D_29321, B_29322, A_29323]: (r2_hidden(D_29321, B_29322) | r2_hidden(D_29321, A_29323) | ~r2_hidden(D_29321, k2_xboole_0(A_29323, B_29322)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.19/7.83  tff(c_22438, plain, (![D_56781, A_56782]: (r2_hidden(D_56781, k1_tarski(A_56782)) | r2_hidden(D_56781, A_56782) | ~r2_hidden(D_56781, k1_ordinal1(A_56782)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12475])).
% 17.19/7.83  tff(c_38, plain, (![A_23]: (k3_tarski(k1_tarski(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.19/7.83  tff(c_11873, plain, (![A_29201, B_29202]: (r1_tarski(A_29201, k3_tarski(B_29202)) | ~r2_hidden(A_29201, B_29202))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.19/7.83  tff(c_11876, plain, (![A_29201, A_23]: (r1_tarski(A_29201, A_23) | ~r2_hidden(A_29201, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_11873])).
% 17.19/7.83  tff(c_42481, plain, (![D_122541, A_122542]: (r1_tarski(D_122541, A_122542) | r2_hidden(D_122541, A_122542) | ~r2_hidden(D_122541, k1_ordinal1(A_122542)))), inference(resolution, [status(thm)], [c_22438, c_11876])).
% 17.19/7.83  tff(c_42564, plain, (r1_tarski('#skF_5', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_11830, c_42481])).
% 17.19/7.83  tff(c_42565, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_42564])).
% 17.19/7.83  tff(c_12373, plain, (![B_29319, A_29320]: (r2_hidden(B_29319, A_29320) | r1_ordinal1(A_29320, B_29319) | ~v3_ordinal1(B_29319) | ~v3_ordinal1(A_29320))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.19/7.83  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 17.19/7.83  tff(c_12473, plain, (![A_29320, B_29319]: (~r2_hidden(A_29320, B_29319) | r1_ordinal1(A_29320, B_29319) | ~v3_ordinal1(B_29319) | ~v3_ordinal1(A_29320))), inference(resolution, [status(thm)], [c_12373, c_2])).
% 17.19/7.83  tff(c_42568, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_42565, c_12473])).
% 17.19/7.83  tff(c_42573, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_42568])).
% 17.19/7.83  tff(c_42575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11816, c_42573])).
% 17.19/7.83  tff(c_42576, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_42564])).
% 17.19/7.83  tff(c_82, plain, (![A_35, B_36]: (r1_ordinal1(A_35, B_36) | ~r1_tarski(A_35, B_36) | ~v3_ordinal1(B_36) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.19/7.83  tff(c_42580, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_42576, c_82])).
% 17.19/7.83  tff(c_42583, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_42580])).
% 17.19/7.83  tff(c_42585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11816, c_42583])).
% 17.19/7.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/7.83  
% 17.19/7.83  Inference rules
% 17.19/7.83  ----------------------
% 17.19/7.83  #Ref     : 0
% 17.19/7.83  #Sup     : 6678
% 17.19/7.83  #Fact    : 214
% 17.19/7.83  #Define  : 0
% 17.19/7.83  #Split   : 7
% 17.19/7.83  #Chain   : 0
% 17.19/7.83  #Close   : 0
% 17.19/7.83  
% 17.19/7.83  Ordering : KBO
% 17.19/7.83  
% 17.19/7.83  Simplification rules
% 17.19/7.83  ----------------------
% 17.19/7.83  #Subsume      : 2186
% 17.19/7.83  #Demod        : 121
% 17.19/7.83  #Tautology    : 401
% 17.19/7.83  #SimpNegUnit  : 70
% 17.19/7.83  #BackRed      : 9
% 17.19/7.83  
% 17.19/7.83  #Partial instantiations: 45850
% 17.19/7.83  #Strategies tried      : 1
% 17.19/7.83  
% 17.19/7.83  Timing (in seconds)
% 17.19/7.83  ----------------------
% 17.19/7.83  Preprocessing        : 0.36
% 17.19/7.83  Parsing              : 0.17
% 17.19/7.83  CNF conversion       : 0.03
% 17.19/7.83  Main loop            : 6.70
% 17.19/7.83  Inferencing          : 2.97
% 17.19/7.83  Reduction            : 1.47
% 17.19/7.83  Demodulation         : 0.90
% 17.19/7.83  BG Simplification    : 0.22
% 17.19/7.83  Subsumption          : 1.69
% 17.19/7.83  Abstraction          : 0.36
% 17.19/7.83  MUC search           : 0.00
% 17.19/7.83  Cooper               : 0.00
% 17.19/7.83  Total                : 7.09
% 17.19/7.83  Index Insertion      : 0.00
% 17.19/7.83  Index Deletion       : 0.00
% 17.19/7.83  Index Matching       : 0.00
% 17.19/7.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
