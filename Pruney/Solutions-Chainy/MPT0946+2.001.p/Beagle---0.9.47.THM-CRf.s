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
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 330 expanded)
%              Number of leaves         :   36 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 861 expanded)
%              Number of equality atoms :   17 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_112,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_121,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_125,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(c_58,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ r1_ordinal1(A_10,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_31] : v1_relat_1(k1_wellord2(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134,plain,(
    ! [B_57,A_58] :
      ( r4_wellord1(B_57,A_58)
      | ~ r4_wellord1(A_58,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_136,plain,
    ( r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_134])).

tff(c_139,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_136])).

tff(c_56,plain,(
    ! [B_37,A_36] :
      ( k2_wellord1(k1_wellord2(B_37),A_36) = k1_wellord2(A_36)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_44,plain,(
    ! [A_23] :
      ( k3_relat_1(k1_wellord2(A_23)) = A_23
      | ~ v1_relat_1(k1_wellord2(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_70,plain,(
    ! [A_23] : k3_relat_1(k1_wellord2(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44])).

tff(c_52,plain,(
    ! [B_34,A_32] :
      ( k1_wellord1(k1_wellord2(B_34),A_32) = A_32
      | ~ r2_hidden(A_32,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_287,plain,(
    ! [A_83,B_84] :
      ( ~ r4_wellord1(A_83,k2_wellord1(A_83,k1_wellord1(A_83,B_84)))
      | ~ r2_hidden(B_84,k3_relat_1(A_83))
      | ~ v2_wellord1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_290,plain,(
    ! [B_34,A_32] :
      ( ~ r4_wellord1(k1_wellord2(B_34),k2_wellord1(k1_wellord2(B_34),A_32))
      | ~ r2_hidden(A_32,k3_relat_1(k1_wellord2(B_34)))
      | ~ v2_wellord1(k1_wellord2(B_34))
      | ~ v1_relat_1(k1_wellord2(B_34))
      | ~ r2_hidden(A_32,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_287])).

tff(c_382,plain,(
    ! [B_96,A_97] :
      ( ~ r4_wellord1(k1_wellord2(B_96),k2_wellord1(k1_wellord2(B_96),A_97))
      | ~ v2_wellord1(k1_wellord2(B_96))
      | ~ r2_hidden(A_97,B_96)
      | ~ v3_ordinal1(B_96)
      | ~ v3_ordinal1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_70,c_290])).

tff(c_425,plain,(
    ! [B_102,A_103] :
      ( ~ r4_wellord1(k1_wellord2(B_102),k1_wellord2(A_103))
      | ~ v2_wellord1(k1_wellord2(B_102))
      | ~ r2_hidden(A_103,B_102)
      | ~ v3_ordinal1(B_102)
      | ~ v3_ordinal1(A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_382])).

tff(c_428,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_425])).

tff(c_434,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_428])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_441,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_438])).

tff(c_444,plain,(
    ~ r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_441])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_ordinal1(B_5,A_4)
      | r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_431,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_425])).

tff(c_437,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_431])).

tff(c_447,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_454,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_447])).

tff(c_457,plain,(
    ~ r1_ordinal1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_454])).

tff(c_460,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_457])).

tff(c_466,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_460])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_466])).

tff(c_470,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_82,plain,(
    ! [A_42] :
      ( v1_ordinal1(A_42)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | ~ r2_xboole_0(A_61,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v1_ordinal1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_150,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v1_ordinal1(A_1)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_54,plain,(
    ! [A_35] :
      ( v2_wellord1(k1_wellord2(A_35))
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_469,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_484,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_487,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_484])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_487])).

tff(c_492,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_496,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_492])).

tff(c_499,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_89,c_64,c_496])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_499])).

tff(c_503,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_90,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_82])).

tff(c_502,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_521,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_524,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_521])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_524])).

tff(c_529,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_533,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_529])).

tff(c_536,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_90,c_62,c_533])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:58:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  %$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.38  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.55/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.55/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.55/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.38  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.55/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.38  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.55/1.38  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.55/1.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.55/1.38  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.55/1.38  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.38  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.55/1.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.55/1.38  
% 2.86/1.39  tff(f_139, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.86/1.39  tff(f_61, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.86/1.39  tff(f_112, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.86/1.39  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.86/1.39  tff(f_129, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.86/1.39  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.86/1.39  tff(f_121, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.86/1.39  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.86/1.39  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.86/1.39  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.86/1.39  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.86/1.39  tff(f_70, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.86/1.39  tff(f_125, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.86/1.39  tff(c_58, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.39  tff(c_64, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.39  tff(c_62, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.39  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~r1_ordinal1(A_10, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.39  tff(c_50, plain, (![A_31]: (v1_relat_1(k1_wellord2(A_31)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.86/1.39  tff(c_60, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.39  tff(c_134, plain, (![B_57, A_58]: (r4_wellord1(B_57, A_58) | ~r4_wellord1(A_58, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.39  tff(c_136, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_134])).
% 2.86/1.39  tff(c_139, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_136])).
% 2.86/1.39  tff(c_56, plain, (![B_37, A_36]: (k2_wellord1(k1_wellord2(B_37), A_36)=k1_wellord2(A_36) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.86/1.39  tff(c_44, plain, (![A_23]: (k3_relat_1(k1_wellord2(A_23))=A_23 | ~v1_relat_1(k1_wellord2(A_23)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.39  tff(c_70, plain, (![A_23]: (k3_relat_1(k1_wellord2(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44])).
% 2.86/1.39  tff(c_52, plain, (![B_34, A_32]: (k1_wellord1(k1_wellord2(B_34), A_32)=A_32 | ~r2_hidden(A_32, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.86/1.39  tff(c_287, plain, (![A_83, B_84]: (~r4_wellord1(A_83, k2_wellord1(A_83, k1_wellord1(A_83, B_84))) | ~r2_hidden(B_84, k3_relat_1(A_83)) | ~v2_wellord1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.86/1.39  tff(c_290, plain, (![B_34, A_32]: (~r4_wellord1(k1_wellord2(B_34), k2_wellord1(k1_wellord2(B_34), A_32)) | ~r2_hidden(A_32, k3_relat_1(k1_wellord2(B_34))) | ~v2_wellord1(k1_wellord2(B_34)) | ~v1_relat_1(k1_wellord2(B_34)) | ~r2_hidden(A_32, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_52, c_287])).
% 2.86/1.39  tff(c_382, plain, (![B_96, A_97]: (~r4_wellord1(k1_wellord2(B_96), k2_wellord1(k1_wellord2(B_96), A_97)) | ~v2_wellord1(k1_wellord2(B_96)) | ~r2_hidden(A_97, B_96) | ~v3_ordinal1(B_96) | ~v3_ordinal1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_70, c_290])).
% 2.86/1.39  tff(c_425, plain, (![B_102, A_103]: (~r4_wellord1(k1_wellord2(B_102), k1_wellord2(A_103)) | ~v2_wellord1(k1_wellord2(B_102)) | ~r2_hidden(A_103, B_102) | ~v3_ordinal1(B_102) | ~v3_ordinal1(A_103) | ~r1_tarski(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_56, c_382])).
% 2.86/1.39  tff(c_428, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_139, c_425])).
% 2.86/1.39  tff(c_434, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_428])).
% 2.86/1.39  tff(c_438, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_434])).
% 2.86/1.39  tff(c_441, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_438])).
% 2.86/1.39  tff(c_444, plain, (~r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_441])).
% 2.86/1.39  tff(c_12, plain, (![B_5, A_4]: (r1_ordinal1(B_5, A_4) | r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.39  tff(c_431, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_425])).
% 2.86/1.39  tff(c_437, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_431])).
% 2.86/1.39  tff(c_447, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_437])).
% 2.86/1.39  tff(c_454, plain, (~r1_ordinal1('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_447])).
% 2.86/1.39  tff(c_457, plain, (~r1_ordinal1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_454])).
% 2.86/1.39  tff(c_460, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_457])).
% 2.86/1.39  tff(c_466, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_460])).
% 2.86/1.39  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_466])).
% 2.86/1.39  tff(c_470, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_437])).
% 2.86/1.39  tff(c_82, plain, (![A_42]: (v1_ordinal1(A_42) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.39  tff(c_89, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_82])).
% 2.86/1.39  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.39  tff(c_146, plain, (![A_61, B_62]: (r2_hidden(A_61, B_62) | ~r2_xboole_0(A_61, B_62) | ~v3_ordinal1(B_62) | ~v1_ordinal1(A_61))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.86/1.39  tff(c_150, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~v3_ordinal1(B_2) | ~v1_ordinal1(A_1) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_146])).
% 2.86/1.39  tff(c_54, plain, (![A_35]: (v2_wellord1(k1_wellord2(A_35)) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.86/1.39  tff(c_469, plain, (~r2_hidden('#skF_5', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_437])).
% 2.86/1.39  tff(c_484, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_469])).
% 2.86/1.39  tff(c_487, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_484])).
% 2.86/1.39  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_487])).
% 2.86/1.39  tff(c_492, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_469])).
% 2.86/1.39  tff(c_496, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_150, c_492])).
% 2.86/1.39  tff(c_499, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_89, c_64, c_496])).
% 2.86/1.39  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_499])).
% 2.86/1.39  tff(c_503, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_434])).
% 2.86/1.39  tff(c_90, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_82])).
% 2.86/1.39  tff(c_502, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_434])).
% 2.86/1.39  tff(c_521, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_502])).
% 2.86/1.39  tff(c_524, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_521])).
% 2.86/1.39  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_524])).
% 2.86/1.39  tff(c_529, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_502])).
% 2.86/1.39  tff(c_533, plain, (~v3_ordinal1('#skF_5') | ~v1_ordinal1('#skF_4') | '#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_150, c_529])).
% 2.86/1.39  tff(c_536, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_90, c_62, c_533])).
% 2.86/1.39  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_536])).
% 2.86/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  Inference rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Ref     : 0
% 2.86/1.39  #Sup     : 83
% 2.86/1.39  #Fact    : 2
% 2.86/1.39  #Define  : 0
% 2.86/1.39  #Split   : 4
% 2.86/1.39  #Chain   : 0
% 2.86/1.39  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 6
% 2.86/1.39  #Demod        : 118
% 2.86/1.39  #Tautology    : 39
% 2.86/1.39  #SimpNegUnit  : 5
% 2.86/1.39  #BackRed      : 0
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.40  Preprocessing        : 0.33
% 2.86/1.40  Parsing              : 0.18
% 2.86/1.40  CNF conversion       : 0.02
% 2.86/1.40  Main loop            : 0.30
% 2.86/1.40  Inferencing          : 0.12
% 2.86/1.40  Reduction            : 0.09
% 2.86/1.40  Demodulation         : 0.07
% 2.86/1.40  BG Simplification    : 0.02
% 2.86/1.40  Subsumption          : 0.06
% 2.86/1.40  Abstraction          : 0.01
% 2.86/1.40  MUC search           : 0.00
% 2.86/1.40  Cooper               : 0.00
% 2.86/1.40  Total                : 0.67
% 2.86/1.40  Index Insertion      : 0.00
% 2.86/1.40  Index Deletion       : 0.00
% 2.86/1.40  Index Matching       : 0.00
% 2.86/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
