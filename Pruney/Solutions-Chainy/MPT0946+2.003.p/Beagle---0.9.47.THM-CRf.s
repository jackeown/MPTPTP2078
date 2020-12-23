%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 465 expanded)
%              Number of leaves         :   32 ( 179 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 (1262 expanded)
%              Number of equality atoms :   24 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_108,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_95,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_93,axiom,(
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

tff(f_104,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_59,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_52,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    ! [A_29] :
      ( v2_wellord1(k1_wellord2(A_29))
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_109,plain,(
    ! [B_46,A_47] :
      ( r4_wellord1(B_46,A_47)
      | ~ r4_wellord1(A_47,B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,
    ( r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_114,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_111])).

tff(c_44,plain,(
    ! [B_31,A_30] :
      ( k2_wellord1(k1_wellord2(B_31),A_30) = k1_wellord2(A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_40,plain,(
    ! [B_28,A_26] :
      ( k1_wellord1(k1_wellord2(B_28),A_26) = A_26
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_246,plain,(
    ! [A_61,B_62] :
      ( ~ r4_wellord1(A_61,k2_wellord1(A_61,k1_wellord1(A_61,B_62)))
      | ~ r2_hidden(B_62,k3_relat_1(A_61))
      | ~ v2_wellord1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_249,plain,(
    ! [B_28,A_26] :
      ( ~ r4_wellord1(k1_wellord2(B_28),k2_wellord1(k1_wellord2(B_28),A_26))
      | ~ r2_hidden(A_26,k3_relat_1(k1_wellord2(B_28)))
      | ~ v2_wellord1(k1_wellord2(B_28))
      | ~ v1_relat_1(k1_wellord2(B_28))
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_246])).

tff(c_412,plain,(
    ! [B_79,A_80] :
      ( ~ r4_wellord1(k1_wellord2(B_79),k2_wellord1(k1_wellord2(B_79),A_80))
      | ~ v2_wellord1(k1_wellord2(B_79))
      | ~ r2_hidden(A_80,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_249])).

tff(c_417,plain,(
    ! [B_84,A_85] :
      ( ~ r4_wellord1(k1_wellord2(B_84),k1_wellord2(A_85))
      | ~ v2_wellord1(k1_wellord2(B_84))
      | ~ r2_hidden(A_85,B_84)
      | ~ v3_ordinal1(B_84)
      | ~ v3_ordinal1(A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_412])).

tff(c_420,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_417])).

tff(c_426,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_420])).

tff(c_430,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_69,plain,(
    ! [A_35] :
      ( v1_ordinal1(A_35)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_69])).

tff(c_145,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | B_50 = A_51
      | r2_hidden(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_5,A_2] :
      ( r1_tarski(B_5,A_2)
      | ~ r2_hidden(B_5,A_2)
      | ~ v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ v1_ordinal1(A_51)
      | B_50 = A_51
      | r2_hidden(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_77,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_200,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ v1_ordinal1(A_55)
      | B_54 = A_55
      | r2_hidden(A_55,B_54)
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_207,plain,(
    ! [A_55,B_54] :
      ( r1_tarski(A_55,B_54)
      | ~ v1_ordinal1(B_54)
      | r1_tarski(B_54,A_55)
      | ~ v1_ordinal1(A_55)
      | B_54 = A_55
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_200,c_6])).

tff(c_423,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_417])).

tff(c_429,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_423])).

tff(c_437,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_440,plain,
    ( ~ v1_ordinal1('#skF_4')
    | r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_207,c_437])).

tff(c_446,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_76,c_77,c_440])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_430,c_446])).

tff(c_449,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_451,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_454,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_454])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_463,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_459])).

tff(c_472,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_76,c_463])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_430,c_472])).

tff(c_475,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_481,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_484,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_481])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_484])).

tff(c_489,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_14,plain,(
    ! [B_10,A_8] :
      ( r2_hidden(B_10,A_8)
      | B_10 = A_8
      | r2_hidden(A_8,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_493,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_158,c_489])).

tff(c_498,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_77,c_493])).

tff(c_499,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_498])).

tff(c_501,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_429])).

tff(c_502,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_508,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_502])).

tff(c_518,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_508])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_489,c_46,c_518])).

tff(c_521,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_525,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_521])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:19:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v2_ordinal1 > v1_relat_1 > v1_ordinal1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.61/1.35  
% 2.61/1.35  %Foreground sorts:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Background operators:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Foreground operators:
% 2.61/1.35  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.35  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.61/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.61/1.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.61/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.35  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.61/1.35  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.61/1.35  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.61/1.35  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.35  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.35  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.61/1.35  
% 2.78/1.37  tff(f_122, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.78/1.37  tff(f_108, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.78/1.37  tff(f_95, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.78/1.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.78/1.37  tff(f_112, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.78/1.37  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.78/1.37  tff(f_104, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.78/1.37  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.78/1.37  tff(f_31, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.78/1.37  tff(f_59, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.78/1.37  tff(f_38, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.78/1.37  tff(c_52, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.78/1.37  tff(c_42, plain, (![A_29]: (v2_wellord1(k1_wellord2(A_29)) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.78/1.37  tff(c_50, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.78/1.37  tff(c_46, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.78/1.37  tff(c_38, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.78/1.37  tff(c_48, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.78/1.37  tff(c_109, plain, (![B_46, A_47]: (r4_wellord1(B_46, A_47) | ~r4_wellord1(A_47, B_46) | ~v1_relat_1(B_46) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.78/1.37  tff(c_111, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_109])).
% 2.78/1.37  tff(c_114, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_111])).
% 2.78/1.37  tff(c_44, plain, (![B_31, A_30]: (k2_wellord1(k1_wellord2(B_31), A_30)=k1_wellord2(A_30) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.78/1.37  tff(c_32, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.37  tff(c_58, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.78/1.37  tff(c_40, plain, (![B_28, A_26]: (k1_wellord1(k1_wellord2(B_28), A_26)=A_26 | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.37  tff(c_246, plain, (![A_61, B_62]: (~r4_wellord1(A_61, k2_wellord1(A_61, k1_wellord1(A_61, B_62))) | ~r2_hidden(B_62, k3_relat_1(A_61)) | ~v2_wellord1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.37  tff(c_249, plain, (![B_28, A_26]: (~r4_wellord1(k1_wellord2(B_28), k2_wellord1(k1_wellord2(B_28), A_26)) | ~r2_hidden(A_26, k3_relat_1(k1_wellord2(B_28))) | ~v2_wellord1(k1_wellord2(B_28)) | ~v1_relat_1(k1_wellord2(B_28)) | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_40, c_246])).
% 2.78/1.37  tff(c_412, plain, (![B_79, A_80]: (~r4_wellord1(k1_wellord2(B_79), k2_wellord1(k1_wellord2(B_79), A_80)) | ~v2_wellord1(k1_wellord2(B_79)) | ~r2_hidden(A_80, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_249])).
% 2.78/1.37  tff(c_417, plain, (![B_84, A_85]: (~r4_wellord1(k1_wellord2(B_84), k1_wellord2(A_85)) | ~v2_wellord1(k1_wellord2(B_84)) | ~r2_hidden(A_85, B_84) | ~v3_ordinal1(B_84) | ~v3_ordinal1(A_85) | ~r1_tarski(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_44, c_412])).
% 2.78/1.37  tff(c_420, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_114, c_417])).
% 2.78/1.37  tff(c_426, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_420])).
% 2.78/1.37  tff(c_430, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_426])).
% 2.78/1.37  tff(c_69, plain, (![A_35]: (v1_ordinal1(A_35) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.37  tff(c_76, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_69])).
% 2.78/1.37  tff(c_145, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | B_50=A_51 | r2_hidden(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.37  tff(c_6, plain, (![B_5, A_2]: (r1_tarski(B_5, A_2) | ~r2_hidden(B_5, A_2) | ~v1_ordinal1(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.37  tff(c_158, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~v1_ordinal1(A_51) | B_50=A_51 | r2_hidden(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(resolution, [status(thm)], [c_145, c_6])).
% 2.78/1.37  tff(c_77, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_69])).
% 2.78/1.37  tff(c_200, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~v1_ordinal1(A_55) | B_54=A_55 | r2_hidden(A_55, B_54) | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_145, c_6])).
% 2.78/1.37  tff(c_207, plain, (![A_55, B_54]: (r1_tarski(A_55, B_54) | ~v1_ordinal1(B_54) | r1_tarski(B_54, A_55) | ~v1_ordinal1(A_55) | B_54=A_55 | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_200, c_6])).
% 2.78/1.37  tff(c_423, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_417])).
% 2.78/1.37  tff(c_429, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_423])).
% 2.78/1.37  tff(c_437, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_429])).
% 2.78/1.37  tff(c_440, plain, (~v1_ordinal1('#skF_4') | r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_207, c_437])).
% 2.78/1.37  tff(c_446, plain, (r1_tarski('#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_76, c_77, c_440])).
% 2.78/1.37  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_430, c_446])).
% 2.78/1.37  tff(c_449, plain, (~r2_hidden('#skF_5', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_429])).
% 2.78/1.37  tff(c_451, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_449])).
% 2.78/1.37  tff(c_454, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_451])).
% 2.78/1.37  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_454])).
% 2.78/1.37  tff(c_459, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_449])).
% 2.78/1.37  tff(c_463, plain, (r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_158, c_459])).
% 2.78/1.37  tff(c_472, plain, (r1_tarski('#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_76, c_463])).
% 2.78/1.37  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_430, c_472])).
% 2.78/1.37  tff(c_475, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_426])).
% 2.78/1.37  tff(c_481, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_475])).
% 2.78/1.37  tff(c_484, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_481])).
% 2.78/1.37  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_484])).
% 2.78/1.37  tff(c_489, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_475])).
% 2.78/1.37  tff(c_14, plain, (![B_10, A_8]: (r2_hidden(B_10, A_8) | B_10=A_8 | r2_hidden(A_8, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.37  tff(c_493, plain, (r1_tarski('#skF_5', '#skF_4') | ~v1_ordinal1('#skF_4') | '#skF_5'='#skF_4' | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_158, c_489])).
% 2.78/1.37  tff(c_498, plain, (r1_tarski('#skF_5', '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_77, c_493])).
% 2.78/1.37  tff(c_499, plain, (r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_498])).
% 2.78/1.37  tff(c_501, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_429])).
% 2.78/1.37  tff(c_502, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_501])).
% 2.78/1.37  tff(c_508, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_502])).
% 2.78/1.37  tff(c_518, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_508])).
% 2.78/1.37  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_489, c_46, c_518])).
% 2.78/1.37  tff(c_521, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_501])).
% 2.78/1.37  tff(c_525, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_521])).
% 2.78/1.37  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_525])).
% 2.78/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.37  
% 2.78/1.37  Inference rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Ref     : 0
% 2.78/1.37  #Sup     : 81
% 2.78/1.37  #Fact    : 4
% 2.78/1.37  #Define  : 0
% 2.78/1.37  #Split   : 5
% 2.78/1.37  #Chain   : 0
% 2.78/1.37  #Close   : 0
% 2.78/1.37  
% 2.78/1.37  Ordering : KBO
% 2.78/1.37  
% 2.78/1.37  Simplification rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Subsume      : 4
% 2.78/1.37  #Demod        : 114
% 2.78/1.37  #Tautology    : 40
% 2.78/1.37  #SimpNegUnit  : 5
% 2.78/1.37  #BackRed      : 0
% 2.78/1.37  
% 2.78/1.37  #Partial instantiations: 0
% 2.78/1.37  #Strategies tried      : 1
% 2.78/1.37  
% 2.78/1.37  Timing (in seconds)
% 2.78/1.37  ----------------------
% 2.78/1.38  Preprocessing        : 0.32
% 2.78/1.38  Parsing              : 0.16
% 2.78/1.38  CNF conversion       : 0.02
% 2.78/1.38  Main loop            : 0.29
% 2.78/1.38  Inferencing          : 0.11
% 2.78/1.38  Reduction            : 0.09
% 2.78/1.38  Demodulation         : 0.07
% 2.78/1.38  BG Simplification    : 0.02
% 2.78/1.38  Subsumption          : 0.06
% 2.78/1.38  Abstraction          : 0.01
% 2.78/1.38  MUC search           : 0.00
% 2.78/1.38  Cooper               : 0.00
% 2.78/1.38  Total                : 0.65
% 2.78/1.38  Index Insertion      : 0.00
% 2.78/1.38  Index Deletion       : 0.00
% 2.78/1.38  Index Matching       : 0.00
% 2.78/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
