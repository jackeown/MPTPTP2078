%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 343 expanded)
%              Number of leaves         :   32 ( 135 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 914 expanded)
%              Number of equality atoms :   17 ( 119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_ordinal1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_105,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_114,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_60,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_118,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_60,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( k2_wellord1(k1_wellord2(B_35),A_34) = k1_wellord2(A_34)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    ! [A_29] : v1_relat_1(k1_wellord2(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_21] :
      ( k3_relat_1(k1_wellord2(A_21)) = A_21
      | ~ v1_relat_1(k1_wellord2(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    ! [A_21] : k3_relat_1(k1_wellord2(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_50,plain,(
    ! [B_32,A_30] :
      ( k1_wellord1(k1_wellord2(B_32),A_30) = A_30
      | ~ r2_hidden(A_30,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_356,plain,(
    ! [A_93,B_94] :
      ( ~ r4_wellord1(A_93,k2_wellord1(A_93,k1_wellord1(A_93,B_94)))
      | ~ r2_hidden(B_94,k3_relat_1(A_93))
      | ~ v2_wellord1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_359,plain,(
    ! [B_32,A_30] :
      ( ~ r4_wellord1(k1_wellord2(B_32),k2_wellord1(k1_wellord2(B_32),A_30))
      | ~ r2_hidden(A_30,k3_relat_1(k1_wellord2(B_32)))
      | ~ v2_wellord1(k1_wellord2(B_32))
      | ~ v1_relat_1(k1_wellord2(B_32))
      | ~ r2_hidden(A_30,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_356])).

tff(c_479,plain,(
    ! [B_108,A_109] :
      ( ~ r4_wellord1(k1_wellord2(B_108),k2_wellord1(k1_wellord2(B_108),A_109))
      | ~ v2_wellord1(k1_wellord2(B_108))
      | ~ r2_hidden(A_109,B_108)
      | ~ v3_ordinal1(B_108)
      | ~ v3_ordinal1(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68,c_359])).

tff(c_707,plain,(
    ! [B_122,A_123] :
      ( ~ r4_wellord1(k1_wellord2(B_122),k1_wellord2(A_123))
      | ~ v2_wellord1(k1_wellord2(B_122))
      | ~ r2_hidden(A_123,B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_479])).

tff(c_713,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_707])).

tff(c_719,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_713])).

tff(c_727,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_730,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_727])).

tff(c_733,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_730])).

tff(c_20,plain,(
    ! [B_11,A_9] :
      ( r2_hidden(B_11,A_9)
      | r1_ordinal1(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden(A_5,B_6)
      | r2_hidden(A_5,k1_ordinal1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_64,B_65] :
      ( r1_ordinal1(A_64,B_65)
      | ~ r2_hidden(A_64,k1_ordinal1(B_65))
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_170,plain,(
    ! [A_66,B_67] :
      ( r1_ordinal1(A_66,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_66)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_16,c_156])).

tff(c_180,plain,(
    ! [B_11,A_9] :
      ( r1_ordinal1(B_11,A_9)
      | r1_ordinal1(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_121,plain,(
    ! [B_55,A_56] :
      ( r4_wellord1(B_55,A_56)
      | ~ r4_wellord1(A_56,B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_123,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_121])).

tff(c_126,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_123])).

tff(c_710,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_707])).

tff(c_716,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_710])).

tff(c_720,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_723,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_720])).

tff(c_726,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_723])).

tff(c_736,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_726])).

tff(c_742,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_736])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_742])).

tff(c_750,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_ordinal1(A_3,B_4)
      | ~ r1_tarski(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_756,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_750,c_8])).

tff(c_765,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_756])).

tff(c_184,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,k1_ordinal1(B_70))
      | ~ r1_ordinal1(A_69,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | r2_hidden(A_5,B_6)
      | ~ r2_hidden(A_5,k1_ordinal1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,(
    ! [B_70,A_69] :
      ( B_70 = A_69
      | r2_hidden(A_69,B_70)
      | ~ r1_ordinal1(A_69,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_69) ) ),
    inference(resolution,[status(thm)],[c_184,c_12])).

tff(c_52,plain,(
    ! [A_33] :
      ( v2_wellord1(k1_wellord2(A_33))
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_749,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_790,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_749])).

tff(c_793,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_790])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_793])).

tff(c_798,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_802,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_798])).

tff(c_808,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_765,c_802])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_808])).

tff(c_812,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_818,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_812,c_8])).

tff(c_827,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_818])).

tff(c_811,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_849,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_852,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_849])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_852])).

tff(c_857,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_861,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_857])).

tff(c_867,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_827,c_861])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.64  
% 3.50/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.65  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_ordinal1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.50/1.65  
% 3.50/1.65  %Foreground sorts:
% 3.50/1.65  
% 3.50/1.65  
% 3.50/1.65  %Background operators:
% 3.50/1.65  
% 3.50/1.65  
% 3.50/1.65  %Foreground operators:
% 3.50/1.65  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.50/1.65  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.50/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.50/1.65  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.50/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.65  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.50/1.65  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.50/1.65  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.50/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.65  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.50/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.65  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.50/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.65  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.50/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.65  
% 3.50/1.67  tff(f_132, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 3.50/1.67  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.50/1.67  tff(f_122, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 3.50/1.67  tff(f_105, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.50/1.67  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.50/1.67  tff(f_114, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 3.50/1.67  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 3.50/1.67  tff(f_60, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.50/1.67  tff(f_45, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.50/1.67  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.50/1.67  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 3.50/1.67  tff(f_118, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 3.50/1.67  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.50/1.67  tff(c_62, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.50/1.67  tff(c_60, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.50/1.67  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.50/1.67  tff(c_58, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.50/1.67  tff(c_54, plain, (![B_35, A_34]: (k2_wellord1(k1_wellord2(B_35), A_34)=k1_wellord2(A_34) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.67  tff(c_48, plain, (![A_29]: (v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.50/1.67  tff(c_42, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21 | ~v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.50/1.67  tff(c_68, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 3.50/1.67  tff(c_50, plain, (![B_32, A_30]: (k1_wellord1(k1_wellord2(B_32), A_30)=A_30 | ~r2_hidden(A_30, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.67  tff(c_356, plain, (![A_93, B_94]: (~r4_wellord1(A_93, k2_wellord1(A_93, k1_wellord1(A_93, B_94))) | ~r2_hidden(B_94, k3_relat_1(A_93)) | ~v2_wellord1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.67  tff(c_359, plain, (![B_32, A_30]: (~r4_wellord1(k1_wellord2(B_32), k2_wellord1(k1_wellord2(B_32), A_30)) | ~r2_hidden(A_30, k3_relat_1(k1_wellord2(B_32))) | ~v2_wellord1(k1_wellord2(B_32)) | ~v1_relat_1(k1_wellord2(B_32)) | ~r2_hidden(A_30, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_50, c_356])).
% 3.50/1.67  tff(c_479, plain, (![B_108, A_109]: (~r4_wellord1(k1_wellord2(B_108), k2_wellord1(k1_wellord2(B_108), A_109)) | ~v2_wellord1(k1_wellord2(B_108)) | ~r2_hidden(A_109, B_108) | ~v3_ordinal1(B_108) | ~v3_ordinal1(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68, c_359])).
% 3.50/1.67  tff(c_707, plain, (![B_122, A_123]: (~r4_wellord1(k1_wellord2(B_122), k1_wellord2(A_123)) | ~v2_wellord1(k1_wellord2(B_122)) | ~r2_hidden(A_123, B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(A_123) | ~r1_tarski(A_123, B_122))), inference(superposition, [status(thm), theory('equality')], [c_54, c_479])).
% 3.50/1.67  tff(c_713, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_707])).
% 3.50/1.67  tff(c_719, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_713])).
% 3.50/1.67  tff(c_727, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_719])).
% 3.50/1.67  tff(c_730, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_727])).
% 3.50/1.67  tff(c_733, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_730])).
% 3.50/1.67  tff(c_20, plain, (![B_11, A_9]: (r2_hidden(B_11, A_9) | r1_ordinal1(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.50/1.67  tff(c_16, plain, (![A_5, B_6]: (~r2_hidden(A_5, B_6) | r2_hidden(A_5, k1_ordinal1(B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.67  tff(c_156, plain, (![A_64, B_65]: (r1_ordinal1(A_64, B_65) | ~r2_hidden(A_64, k1_ordinal1(B_65)) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.67  tff(c_170, plain, (![A_66, B_67]: (r1_ordinal1(A_66, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_66) | ~r2_hidden(A_66, B_67))), inference(resolution, [status(thm)], [c_16, c_156])).
% 3.50/1.67  tff(c_180, plain, (![B_11, A_9]: (r1_ordinal1(B_11, A_9) | r1_ordinal1(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(resolution, [status(thm)], [c_20, c_170])).
% 3.50/1.67  tff(c_121, plain, (![B_55, A_56]: (r4_wellord1(B_55, A_56) | ~r4_wellord1(A_56, B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.50/1.67  tff(c_123, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_121])).
% 3.50/1.67  tff(c_126, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_123])).
% 3.50/1.67  tff(c_710, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_126, c_707])).
% 3.50/1.67  tff(c_716, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_710])).
% 3.50/1.67  tff(c_720, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_716])).
% 3.50/1.67  tff(c_723, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_720])).
% 3.50/1.67  tff(c_726, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_723])).
% 3.50/1.67  tff(c_736, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_180, c_726])).
% 3.50/1.67  tff(c_742, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_736])).
% 3.50/1.67  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_733, c_742])).
% 3.50/1.67  tff(c_750, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_719])).
% 3.50/1.67  tff(c_8, plain, (![A_3, B_4]: (r1_ordinal1(A_3, B_4) | ~r1_tarski(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.50/1.67  tff(c_756, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_750, c_8])).
% 3.50/1.67  tff(c_765, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_756])).
% 3.50/1.67  tff(c_184, plain, (![A_69, B_70]: (r2_hidden(A_69, k1_ordinal1(B_70)) | ~r1_ordinal1(A_69, B_70) | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.67  tff(c_12, plain, (![B_6, A_5]: (B_6=A_5 | r2_hidden(A_5, B_6) | ~r2_hidden(A_5, k1_ordinal1(B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.67  tff(c_199, plain, (![B_70, A_69]: (B_70=A_69 | r2_hidden(A_69, B_70) | ~r1_ordinal1(A_69, B_70) | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_69))), inference(resolution, [status(thm)], [c_184, c_12])).
% 3.50/1.67  tff(c_52, plain, (![A_33]: (v2_wellord1(k1_wellord2(A_33)) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.50/1.67  tff(c_749, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_719])).
% 3.50/1.67  tff(c_790, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_749])).
% 3.50/1.67  tff(c_793, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_790])).
% 3.50/1.67  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_793])).
% 3.50/1.67  tff(c_798, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_749])).
% 3.50/1.67  tff(c_802, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_199, c_798])).
% 3.50/1.67  tff(c_808, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_765, c_802])).
% 3.50/1.67  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_808])).
% 3.50/1.67  tff(c_812, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_716])).
% 3.50/1.67  tff(c_818, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_812, c_8])).
% 3.50/1.67  tff(c_827, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_818])).
% 3.50/1.67  tff(c_811, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_716])).
% 3.50/1.67  tff(c_849, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_811])).
% 3.50/1.67  tff(c_852, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_849])).
% 3.50/1.67  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_852])).
% 3.50/1.67  tff(c_857, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_811])).
% 3.50/1.67  tff(c_861, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_199, c_857])).
% 3.50/1.67  tff(c_867, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_827, c_861])).
% 3.50/1.67  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_867])).
% 3.50/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.67  
% 3.50/1.67  Inference rules
% 3.50/1.67  ----------------------
% 3.50/1.67  #Ref     : 0
% 3.50/1.67  #Sup     : 151
% 3.50/1.67  #Fact    : 2
% 3.50/1.67  #Define  : 0
% 3.50/1.67  #Split   : 4
% 3.50/1.67  #Chain   : 0
% 3.50/1.67  #Close   : 0
% 3.50/1.67  
% 3.50/1.67  Ordering : KBO
% 3.50/1.67  
% 3.50/1.67  Simplification rules
% 3.50/1.67  ----------------------
% 3.50/1.67  #Subsume      : 31
% 3.50/1.67  #Demod        : 102
% 3.50/1.67  #Tautology    : 50
% 3.50/1.67  #SimpNegUnit  : 9
% 3.50/1.67  #BackRed      : 0
% 3.50/1.67  
% 3.50/1.67  #Partial instantiations: 0
% 3.50/1.67  #Strategies tried      : 1
% 3.50/1.67  
% 3.50/1.67  Timing (in seconds)
% 3.50/1.67  ----------------------
% 3.50/1.68  Preprocessing        : 0.36
% 3.50/1.68  Parsing              : 0.19
% 3.50/1.68  CNF conversion       : 0.03
% 3.50/1.68  Main loop            : 0.47
% 3.50/1.68  Inferencing          : 0.16
% 3.50/1.68  Reduction            : 0.13
% 3.50/1.68  Demodulation         : 0.09
% 3.50/1.68  BG Simplification    : 0.03
% 3.50/1.68  Subsumption          : 0.12
% 3.50/1.68  Abstraction          : 0.02
% 3.50/1.68  MUC search           : 0.00
% 3.50/1.68  Cooper               : 0.00
% 3.50/1.68  Total                : 0.87
% 3.50/1.68  Index Insertion      : 0.00
% 3.50/1.68  Index Deletion       : 0.00
% 3.50/1.68  Index Matching       : 0.00
% 3.50/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
