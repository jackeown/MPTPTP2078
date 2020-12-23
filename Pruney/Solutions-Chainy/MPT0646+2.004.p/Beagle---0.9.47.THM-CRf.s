%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 337 expanded)
%              Number of leaves         :   22 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  163 ( 938 expanded)
%              Number of equality atoms :   28 ( 214 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( r1_tarski(k2_relat_1(B),k1_relat_1(A))
                    & r1_tarski(k2_relat_1(C),k1_relat_1(A))
                    & k1_relat_1(B) = k1_relat_1(C)
                    & k5_relat_1(B,A) = k5_relat_1(C,A) )
                 => B = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_36,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k5_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_8,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_10,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    v1_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_151,plain,(
    ! [A_38] :
      ( r1_tarski(k2_relat_1('#skF_1'(A_38)),k1_relat_1(A_38))
      | v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_157,plain,
    ( r1_tarski(k2_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4'))),k1_relat_1('#skF_3'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_151])).

tff(c_163,plain,
    ( r1_tarski(k2_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4'))),k1_relat_1('#skF_3'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_157])).

tff(c_190,plain,(
    v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( r1_tarski(k2_relat_1(B_7),k1_relat_1(A_5))
      | k1_relat_1(k5_relat_1(B_7,A_5)) != k1_relat_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_371,plain,(
    ! [B_53,A_54] :
      ( v2_funct_1(B_53)
      | ~ r1_tarski(k2_relat_1(B_53),k1_relat_1(A_54))
      | ~ v2_funct_1(k5_relat_1(B_53,A_54))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_875,plain,(
    ! [B_74,A_75] :
      ( v2_funct_1(B_74)
      | ~ v2_funct_1(k5_relat_1(B_74,A_75))
      | k1_relat_1(k5_relat_1(B_74,A_75)) != k1_relat_1(B_74)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_12,c_371])).

tff(c_908,plain,
    ( v2_funct_1('#skF_3')
    | k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_875])).

tff(c_935,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_46,c_44,c_70,c_908])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_935])).

tff(c_939,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_34,plain,(
    ! [A_11] :
      ( v1_relat_1('#skF_1'(A_11))
      | v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_11] :
      ( '#skF_2'(A_11) != '#skF_1'(A_11)
      | v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_942,plain,
    ( '#skF_2'(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_939])).

tff(c_945,plain,(
    '#skF_2'(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_942])).

tff(c_30,plain,(
    ! [A_11] :
      ( v1_relat_1('#skF_2'(A_11))
      | v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_127,plain,(
    ! [A_36] :
      ( r1_tarski(k2_relat_1('#skF_2'(A_36)),k1_relat_1(A_36))
      | v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_133,plain,
    ( r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))),k1_relat_1('#skF_3'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_127])).

tff(c_139,plain,
    ( r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))),k1_relat_1('#skF_3'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_133])).

tff(c_964,plain,(
    r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_939,c_139])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k5_relat_1(B_3,k6_relat_1(A_2)) = B_3
      | ~ r1_tarski(k2_relat_1(B_3),A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_967,plain,
    ( k5_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4')),k6_relat_1(k1_relat_1('#skF_3'))) = '#skF_2'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_964,c_6])).

tff(c_969,plain,
    ( k5_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4')),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_967])).

tff(c_996,plain,(
    ~ v1_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_999,plain,
    ( v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_996])).

tff(c_1002,plain,(
    v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_999])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_939,c_1002])).

tff(c_1005,plain,(
    k5_relat_1('#skF_2'(k5_relat_1('#skF_3','#skF_4')),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_20,plain,(
    ! [A_11] :
      ( k5_relat_1('#skF_2'(A_11),A_11) = k5_relat_1('#skF_1'(A_11),A_11)
      | v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1010,plain,
    ( k5_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4')),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'(k5_relat_1('#skF_3','#skF_4'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_20])).

tff(c_1017,plain,
    ( k5_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4')),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'(k5_relat_1('#skF_3','#skF_4'))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_1010])).

tff(c_1018,plain,(
    k5_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4')),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_939,c_1017])).

tff(c_160,plain,(
    ! [A_1] :
      ( r1_tarski(k2_relat_1('#skF_1'(k6_relat_1(A_1))),A_1)
      | v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_181,plain,(
    ! [A_40] :
      ( r1_tarski(k2_relat_1('#skF_1'(k6_relat_1(A_40))),A_40)
      | v2_funct_1(k6_relat_1(A_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_160])).

tff(c_1220,plain,(
    ! [A_89] :
      ( k5_relat_1('#skF_1'(k6_relat_1(A_89)),k6_relat_1(A_89)) = '#skF_1'(k6_relat_1(A_89))
      | ~ v1_relat_1('#skF_1'(k6_relat_1(A_89)))
      | v2_funct_1(k6_relat_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_1232,plain,
    ( k5_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4')),k6_relat_1(k1_relat_1('#skF_3'))) = '#skF_1'(k6_relat_1(k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_1'(k6_relat_1(k1_relat_1('#skF_3'))))
    | v2_funct_1(k6_relat_1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1220])).

tff(c_1238,plain,
    ( '#skF_2'(k5_relat_1('#skF_3','#skF_4')) = '#skF_1'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4')))
    | v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_1018,c_38,c_38,c_1232])).

tff(c_1239,plain,(
    ~ v1_relat_1('#skF_1'(k5_relat_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_939,c_945,c_1238])).

tff(c_1244,plain,
    ( v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_1239])).

tff(c_1247,plain,(
    v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_77,c_1244])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_939,c_1247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.56  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.47/1.56  
% 3.47/1.56  %Foreground sorts:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Background operators:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Foreground operators:
% 3.47/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.47/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.47/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.56  
% 3.47/1.57  tff(f_107, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 3.47/1.57  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.47/1.57  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.47/1.57  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_1)).
% 3.47/1.57  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 3.47/1.57  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 3.47/1.57  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.47/1.57  tff(c_36, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_38, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.57  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.57  tff(c_70, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 3.47/1.57  tff(c_8, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.57  tff(c_75, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 3.47/1.57  tff(c_10, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.57  tff(c_77, plain, (v1_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 3.47/1.57  tff(c_151, plain, (![A_38]: (r1_tarski(k2_relat_1('#skF_1'(A_38)), k1_relat_1(A_38)) | v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_157, plain, (r1_tarski(k2_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4'))), k1_relat_1('#skF_3')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_151])).
% 3.47/1.57  tff(c_163, plain, (r1_tarski(k2_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4'))), k1_relat_1('#skF_3')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_157])).
% 3.47/1.57  tff(c_190, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_163])).
% 3.47/1.57  tff(c_12, plain, (![B_7, A_5]: (r1_tarski(k2_relat_1(B_7), k1_relat_1(A_5)) | k1_relat_1(k5_relat_1(B_7, A_5))!=k1_relat_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.47/1.57  tff(c_371, plain, (![B_53, A_54]: (v2_funct_1(B_53) | ~r1_tarski(k2_relat_1(B_53), k1_relat_1(A_54)) | ~v2_funct_1(k5_relat_1(B_53, A_54)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.57  tff(c_875, plain, (![B_74, A_75]: (v2_funct_1(B_74) | ~v2_funct_1(k5_relat_1(B_74, A_75)) | k1_relat_1(k5_relat_1(B_74, A_75))!=k1_relat_1(B_74) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_12, c_371])).
% 3.47/1.57  tff(c_908, plain, (v2_funct_1('#skF_3') | k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_190, c_875])).
% 3.47/1.57  tff(c_935, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_46, c_44, c_70, c_908])).
% 3.47/1.57  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_935])).
% 3.47/1.57  tff(c_939, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_163])).
% 3.47/1.57  tff(c_34, plain, (![A_11]: (v1_relat_1('#skF_1'(A_11)) | v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_18, plain, (![A_11]: ('#skF_2'(A_11)!='#skF_1'(A_11) | v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_942, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_939])).
% 3.47/1.57  tff(c_945, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_942])).
% 3.47/1.57  tff(c_30, plain, (![A_11]: (v1_relat_1('#skF_2'(A_11)) | v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_127, plain, (![A_36]: (r1_tarski(k2_relat_1('#skF_2'(A_36)), k1_relat_1(A_36)) | v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_133, plain, (r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))), k1_relat_1('#skF_3')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_127])).
% 3.47/1.57  tff(c_139, plain, (r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))), k1_relat_1('#skF_3')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_133])).
% 3.47/1.57  tff(c_964, plain, (r1_tarski(k2_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_939, c_139])).
% 3.47/1.57  tff(c_6, plain, (![B_3, A_2]: (k5_relat_1(B_3, k6_relat_1(A_2))=B_3 | ~r1_tarski(k2_relat_1(B_3), A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.57  tff(c_967, plain, (k5_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')), k6_relat_1(k1_relat_1('#skF_3')))='#skF_2'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_964, c_6])).
% 3.47/1.57  tff(c_969, plain, (k5_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_967])).
% 3.47/1.57  tff(c_996, plain, (~v1_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_969])).
% 3.47/1.57  tff(c_999, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_996])).
% 3.47/1.57  tff(c_1002, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_999])).
% 3.47/1.57  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_939, c_1002])).
% 3.47/1.57  tff(c_1005, plain, (k5_relat_1('#skF_2'(k5_relat_1('#skF_3', '#skF_4')), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_969])).
% 3.47/1.57  tff(c_20, plain, (![A_11]: (k5_relat_1('#skF_2'(A_11), A_11)=k5_relat_1('#skF_1'(A_11), A_11) | v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_1010, plain, (k5_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4')), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'(k5_relat_1('#skF_3', '#skF_4')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_20])).
% 3.47/1.57  tff(c_1017, plain, (k5_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4')), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'(k5_relat_1('#skF_3', '#skF_4')) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_1010])).
% 3.47/1.57  tff(c_1018, plain, (k5_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4')), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_939, c_1017])).
% 3.47/1.57  tff(c_160, plain, (![A_1]: (r1_tarski(k2_relat_1('#skF_1'(k6_relat_1(A_1))), A_1) | v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 3.47/1.57  tff(c_181, plain, (![A_40]: (r1_tarski(k2_relat_1('#skF_1'(k6_relat_1(A_40))), A_40) | v2_funct_1(k6_relat_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_160])).
% 3.47/1.57  tff(c_1220, plain, (![A_89]: (k5_relat_1('#skF_1'(k6_relat_1(A_89)), k6_relat_1(A_89))='#skF_1'(k6_relat_1(A_89)) | ~v1_relat_1('#skF_1'(k6_relat_1(A_89))) | v2_funct_1(k6_relat_1(A_89)))), inference(resolution, [status(thm)], [c_181, c_6])).
% 3.47/1.57  tff(c_1232, plain, (k5_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4')), k6_relat_1(k1_relat_1('#skF_3')))='#skF_1'(k6_relat_1(k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_1'(k6_relat_1(k1_relat_1('#skF_3')))) | v2_funct_1(k6_relat_1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1220])).
% 3.47/1.57  tff(c_1238, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))='#skF_1'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4'))) | v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_1018, c_38, c_38, c_1232])).
% 3.47/1.57  tff(c_1239, plain, (~v1_relat_1('#skF_1'(k5_relat_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_939, c_945, c_1238])).
% 3.47/1.57  tff(c_1244, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1239])).
% 3.47/1.57  tff(c_1247, plain, (v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_77, c_1244])).
% 3.47/1.57  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_939, c_1247])).
% 3.47/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.57  
% 3.47/1.57  Inference rules
% 3.47/1.57  ----------------------
% 3.47/1.57  #Ref     : 1
% 3.47/1.57  #Sup     : 255
% 3.47/1.57  #Fact    : 0
% 3.47/1.57  #Define  : 0
% 3.47/1.57  #Split   : 6
% 3.47/1.57  #Chain   : 0
% 3.47/1.57  #Close   : 0
% 3.47/1.57  
% 3.47/1.57  Ordering : KBO
% 3.47/1.57  
% 3.47/1.57  Simplification rules
% 3.47/1.57  ----------------------
% 3.47/1.57  #Subsume      : 28
% 3.47/1.57  #Demod        : 431
% 3.47/1.57  #Tautology    : 115
% 3.47/1.57  #SimpNegUnit  : 29
% 3.47/1.57  #BackRed      : 0
% 3.47/1.57  
% 3.47/1.57  #Partial instantiations: 0
% 3.47/1.57  #Strategies tried      : 1
% 3.47/1.57  
% 3.47/1.57  Timing (in seconds)
% 3.47/1.57  ----------------------
% 3.47/1.57  Preprocessing        : 0.30
% 3.47/1.57  Parsing              : 0.16
% 3.47/1.57  CNF conversion       : 0.02
% 3.47/1.57  Main loop            : 0.48
% 3.47/1.57  Inferencing          : 0.17
% 3.47/1.57  Reduction            : 0.17
% 3.47/1.57  Demodulation         : 0.12
% 3.47/1.57  BG Simplification    : 0.03
% 3.47/1.57  Subsumption          : 0.09
% 3.47/1.57  Abstraction          : 0.03
% 3.47/1.57  MUC search           : 0.00
% 3.47/1.57  Cooper               : 0.00
% 3.47/1.57  Total                : 0.81
% 3.47/1.57  Index Insertion      : 0.00
% 3.47/1.57  Index Deletion       : 0.00
% 3.47/1.57  Index Matching       : 0.00
% 3.47/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
