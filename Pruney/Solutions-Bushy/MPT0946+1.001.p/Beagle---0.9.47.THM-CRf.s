%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0946+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 202 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 451 expanded)
%              Number of equality atoms :   14 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_50,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_39,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(c_40,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [A_24] :
      ( v2_wellord1(k1_wellord2(A_24))
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [B_12,A_10] :
      ( k1_wellord1(k1_wellord2(B_12),A_10) = A_10
      | ~ r2_hidden(A_10,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_9] : v1_relat_1(k1_wellord2(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_1] :
      ( k3_relat_1(k1_wellord2(A_1)) = A_1
      | ~ v1_relat_1(k1_wellord2(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_1] : k3_relat_1(k1_wellord2(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14])).

tff(c_60,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k1_wellord1(B_31,A_32),k3_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_1,A_32] :
      ( r1_tarski(k1_wellord1(k1_wellord2(A_1),A_32),A_1)
      | ~ v1_relat_1(k1_wellord2(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_65,plain,(
    ! [A_1,A_32] : r1_tarski(k1_wellord1(k1_wellord2(A_1),A_32),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( k2_wellord1(k1_wellord2(B_26),A_25) = k1_wellord2(A_25)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_204,plain,(
    ! [A_57,B_58] :
      ( ~ r4_wellord1(A_57,k2_wellord1(A_57,k1_wellord1(A_57,B_58)))
      | ~ r2_hidden(B_58,k3_relat_1(A_57))
      | ~ v2_wellord1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_211,plain,(
    ! [B_26,B_58] :
      ( ~ r4_wellord1(k1_wellord2(B_26),k1_wellord2(k1_wellord1(k1_wellord2(B_26),B_58)))
      | ~ r2_hidden(B_58,k3_relat_1(k1_wellord2(B_26)))
      | ~ v2_wellord1(k1_wellord2(B_26))
      | ~ v1_relat_1(k1_wellord2(B_26))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_26),B_58),B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_204])).

tff(c_216,plain,(
    ! [B_59,B_60] :
      ( ~ r4_wellord1(k1_wellord2(B_59),k1_wellord2(k1_wellord1(k1_wellord2(B_59),B_60)))
      | ~ r2_hidden(B_60,B_59)
      | ~ v2_wellord1(k1_wellord2(B_59)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_20,c_48,c_211])).

tff(c_246,plain,(
    ! [B_64,A_65] :
      ( ~ r4_wellord1(k1_wellord2(B_64),k1_wellord2(A_65))
      | ~ r2_hidden(A_65,B_64)
      | ~ v2_wellord1(k1_wellord2(B_64))
      | ~ r2_hidden(A_65,B_64)
      | ~ v3_ordinal1(B_64)
      | ~ v3_ordinal1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_216])).

tff(c_252,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_258,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_252])).

tff(c_260,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [B_17,A_15] :
      ( r2_hidden(B_17,A_15)
      | B_17 = A_15
      | r2_hidden(A_15,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [B_37,A_38] :
      ( r4_wellord1(B_37,A_38)
      | ~ r4_wellord1(A_38,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_81,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_78])).

tff(c_249,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_246])).

tff(c_255,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_249])).

tff(c_259,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_266,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_259])).

tff(c_276,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_266])).

tff(c_277,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_276])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_277])).

tff(c_292,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_360,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_292])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_360])).

tff(c_365,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_370,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_365])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_370])).

%------------------------------------------------------------------------------
