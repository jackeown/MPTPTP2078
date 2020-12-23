%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.53s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 213 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  195 (1092 expanded)
%              Number of equality atoms :   44 ( 344 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k1_relat_1(A) = k2_relat_1(B)
                & k2_relat_1(A) = k1_relat_1(B)
                & ! [C,D] :
                    ( ( r2_hidden(C,k1_relat_1(A))
                      & r2_hidden(D,k1_relat_1(B)) )
                   => ( k1_funct_1(A,C) = D
                    <=> k1_funct_1(B,D) = C ) ) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35),k1_relat_1(A_35))
      | v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_390,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_2'(k2_funct_1(A_55)),k2_relat_1(A_55))
      | v2_funct_1(k2_funct_1(A_55))
      | ~ v1_funct_1(k2_funct_1(A_55))
      | ~ v1_relat_1(k2_funct_1(A_55))
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_79])).

tff(c_399,plain,
    ( r2_hidden('#skF_2'(k2_funct_1('#skF_4')),k1_relat_1('#skF_5'))
    | v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_390])).

tff(c_403,plain,
    ( r2_hidden('#skF_2'(k2_funct_1('#skF_4')),k1_relat_1('#skF_5'))
    | v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_399])).

tff(c_404,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_456,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_404])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_456])).

tff(c_462,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_461,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | v2_funct_1(k2_funct_1('#skF_4'))
    | r2_hidden('#skF_2'(k2_funct_1('#skF_4')),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_463,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_467,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_463])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_467])).

tff(c_473,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_14,B_18] :
      ( r2_hidden('#skF_3'(A_14,B_18),k1_relat_1(A_14))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( k1_funct_1(B_13,k1_funct_1(k2_funct_1(B_13),A_12)) = A_12
      | ~ r2_hidden(A_12,k2_relat_1(B_13))
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(k1_funct_1(B_37,A_38),k2_relat_1(B_37))
      | ~ r2_hidden(A_38,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_676,plain,(
    ! [A_73,A_74] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_73),A_74),k1_relat_1(A_73))
      | ~ r2_hidden(A_74,k1_relat_1(k2_funct_1(A_73)))
      | ~ v1_funct_1(k2_funct_1(A_73))
      | ~ v1_relat_1(k2_funct_1(A_73))
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_96,plain,(
    ! [A_38] :
      ( r2_hidden(k1_funct_1('#skF_4',A_38),k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_38,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_87])).

tff(c_102,plain,(
    ! [A_40] :
      ( r2_hidden(k1_funct_1('#skF_4',A_40),k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_40,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_96])).

tff(c_48,plain,(
    ! [C_27] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_27)) = C_27
      | ~ r2_hidden(k1_funct_1('#skF_4',C_27),k1_relat_1('#skF_5'))
      | ~ r2_hidden(C_27,k1_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_106,plain,(
    ! [A_40] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_40)) = A_40
      | ~ r2_hidden(A_40,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_102,c_48])).

tff(c_692,plain,(
    ! [A_74] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_4',k1_funct_1(k2_funct_1('#skF_4'),A_74))) = k1_funct_1(k2_funct_1('#skF_4'),A_74)
      | ~ r2_hidden(A_74,k1_relat_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_676,c_106])).

tff(c_716,plain,(
    ! [A_75] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_4',k1_funct_1(k2_funct_1('#skF_4'),A_75))) = k1_funct_1(k2_funct_1('#skF_4'),A_75)
      | ~ r2_hidden(A_75,k1_relat_1(k2_funct_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_462,c_473,c_692])).

tff(c_746,plain,(
    ! [A_12] :
      ( k1_funct_1(k2_funct_1('#skF_4'),A_12) = k1_funct_1('#skF_5',A_12)
      | ~ r2_hidden(A_12,k1_relat_1(k2_funct_1('#skF_4')))
      | ~ r2_hidden(A_12,k2_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_716])).

tff(c_767,plain,(
    ! [A_76] :
      ( k1_funct_1(k2_funct_1('#skF_4'),A_76) = k1_funct_1('#skF_5',A_76)
      | ~ r2_hidden(A_76,k1_relat_1(k2_funct_1('#skF_4')))
      | ~ r2_hidden(A_76,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_32,c_746])).

tff(c_786,plain,(
    ! [A_76] :
      ( k1_funct_1(k2_funct_1('#skF_4'),A_76) = k1_funct_1('#skF_5',A_76)
      | ~ r2_hidden(A_76,k2_relat_1('#skF_4'))
      | ~ r2_hidden(A_76,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_767])).

tff(c_801,plain,(
    ! [A_77] :
      ( k1_funct_1(k2_funct_1('#skF_4'),A_77) = k1_funct_1('#skF_5',A_77)
      | ~ r2_hidden(A_77,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_32,c_786])).

tff(c_809,plain,(
    ! [B_18] :
      ( k1_funct_1(k2_funct_1('#skF_4'),'#skF_3'('#skF_5',B_18)) = k1_funct_1('#skF_5','#skF_3'('#skF_5',B_18))
      | B_18 = '#skF_5'
      | k1_relat_1(B_18) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_801])).

tff(c_2939,plain,(
    ! [B_124] :
      ( k1_funct_1(k2_funct_1('#skF_4'),'#skF_3'('#skF_5',B_124)) = k1_funct_1('#skF_5','#skF_3'('#skF_5',B_124))
      | B_124 = '#skF_5'
      | k1_relat_1(B_124) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_809])).

tff(c_26,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_3'(A_14,B_18)) != k1_funct_1(A_14,'#skF_3'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2972,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_5')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2939,c_26])).

tff(c_2994,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_473,c_40,c_38,c_2972])).

tff(c_2995,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2994])).

tff(c_3007,plain,
    ( k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2995])).

tff(c_3010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_32,c_3007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.06  
% 5.44/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.06  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 5.44/2.06  
% 5.44/2.06  %Foreground sorts:
% 5.44/2.06  
% 5.44/2.06  
% 5.44/2.06  %Background operators:
% 5.44/2.06  
% 5.44/2.06  
% 5.44/2.06  %Foreground operators:
% 5.44/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.44/2.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.44/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.44/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.44/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.44/2.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.44/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.44/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.44/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.44/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.44/2.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.44/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.44/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.44/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.44/2.06  
% 5.53/2.08  tff(f_123, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 5.53/2.08  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.53/2.08  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.53/2.08  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 5.53/2.08  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.53/2.08  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 5.53/2.08  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 5.53/2.08  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_36, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_32, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.53/2.08  tff(c_30, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.53/2.08  tff(c_79, plain, (![A_35]: (r2_hidden('#skF_2'(A_35), k1_relat_1(A_35)) | v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.53/2.08  tff(c_390, plain, (![A_55]: (r2_hidden('#skF_2'(k2_funct_1(A_55)), k2_relat_1(A_55)) | v2_funct_1(k2_funct_1(A_55)) | ~v1_funct_1(k2_funct_1(A_55)) | ~v1_relat_1(k2_funct_1(A_55)) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_20, c_79])).
% 5.53/2.08  tff(c_399, plain, (r2_hidden('#skF_2'(k2_funct_1('#skF_4')), k1_relat_1('#skF_5')) | v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_390])).
% 5.53/2.08  tff(c_403, plain, (r2_hidden('#skF_2'(k2_funct_1('#skF_4')), k1_relat_1('#skF_5')) | v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_399])).
% 5.53/2.08  tff(c_404, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_403])).
% 5.53/2.08  tff(c_456, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_404])).
% 5.53/2.08  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_456])).
% 5.53/2.08  tff(c_462, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_403])).
% 5.53/2.08  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.53/2.08  tff(c_461, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | v2_funct_1(k2_funct_1('#skF_4')) | r2_hidden('#skF_2'(k2_funct_1('#skF_4')), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_403])).
% 5.53/2.08  tff(c_463, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_461])).
% 5.53/2.08  tff(c_467, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_463])).
% 5.53/2.08  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_467])).
% 5.53/2.08  tff(c_473, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_461])).
% 5.53/2.08  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_28, plain, (![A_14, B_18]: (r2_hidden('#skF_3'(A_14, B_18), k1_relat_1(A_14)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.53/2.08  tff(c_24, plain, (![B_13, A_12]: (k1_funct_1(B_13, k1_funct_1(k2_funct_1(B_13), A_12))=A_12 | ~r2_hidden(A_12, k2_relat_1(B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.53/2.08  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.53/2.08  tff(c_87, plain, (![B_37, A_38]: (r2_hidden(k1_funct_1(B_37, A_38), k2_relat_1(B_37)) | ~r2_hidden(A_38, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.53/2.08  tff(c_676, plain, (![A_73, A_74]: (r2_hidden(k1_funct_1(k2_funct_1(A_73), A_74), k1_relat_1(A_73)) | ~r2_hidden(A_74, k1_relat_1(k2_funct_1(A_73))) | ~v1_funct_1(k2_funct_1(A_73)) | ~v1_relat_1(k2_funct_1(A_73)) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_18, c_87])).
% 5.53/2.08  tff(c_96, plain, (![A_38]: (r2_hidden(k1_funct_1('#skF_4', A_38), k1_relat_1('#skF_5')) | ~r2_hidden(A_38, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_87])).
% 5.53/2.08  tff(c_102, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_4', A_40), k1_relat_1('#skF_5')) | ~r2_hidden(A_40, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_96])).
% 5.53/2.08  tff(c_48, plain, (![C_27]: (k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_27))=C_27 | ~r2_hidden(k1_funct_1('#skF_4', C_27), k1_relat_1('#skF_5')) | ~r2_hidden(C_27, k1_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.53/2.08  tff(c_106, plain, (![A_40]: (k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_40))=A_40 | ~r2_hidden(A_40, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_102, c_48])).
% 5.53/2.08  tff(c_692, plain, (![A_74]: (k1_funct_1('#skF_5', k1_funct_1('#skF_4', k1_funct_1(k2_funct_1('#skF_4'), A_74)))=k1_funct_1(k2_funct_1('#skF_4'), A_74) | ~r2_hidden(A_74, k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_676, c_106])).
% 5.53/2.08  tff(c_716, plain, (![A_75]: (k1_funct_1('#skF_5', k1_funct_1('#skF_4', k1_funct_1(k2_funct_1('#skF_4'), A_75)))=k1_funct_1(k2_funct_1('#skF_4'), A_75) | ~r2_hidden(A_75, k1_relat_1(k2_funct_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_462, c_473, c_692])).
% 5.53/2.08  tff(c_746, plain, (![A_12]: (k1_funct_1(k2_funct_1('#skF_4'), A_12)=k1_funct_1('#skF_5', A_12) | ~r2_hidden(A_12, k1_relat_1(k2_funct_1('#skF_4'))) | ~r2_hidden(A_12, k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_716])).
% 5.53/2.08  tff(c_767, plain, (![A_76]: (k1_funct_1(k2_funct_1('#skF_4'), A_76)=k1_funct_1('#skF_5', A_76) | ~r2_hidden(A_76, k1_relat_1(k2_funct_1('#skF_4'))) | ~r2_hidden(A_76, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_746])).
% 5.53/2.08  tff(c_786, plain, (![A_76]: (k1_funct_1(k2_funct_1('#skF_4'), A_76)=k1_funct_1('#skF_5', A_76) | ~r2_hidden(A_76, k2_relat_1('#skF_4')) | ~r2_hidden(A_76, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_767])).
% 5.53/2.08  tff(c_801, plain, (![A_77]: (k1_funct_1(k2_funct_1('#skF_4'), A_77)=k1_funct_1('#skF_5', A_77) | ~r2_hidden(A_77, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_786])).
% 5.53/2.08  tff(c_809, plain, (![B_18]: (k1_funct_1(k2_funct_1('#skF_4'), '#skF_3'('#skF_5', B_18))=k1_funct_1('#skF_5', '#skF_3'('#skF_5', B_18)) | B_18='#skF_5' | k1_relat_1(B_18)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_801])).
% 5.53/2.08  tff(c_2939, plain, (![B_124]: (k1_funct_1(k2_funct_1('#skF_4'), '#skF_3'('#skF_5', B_124))=k1_funct_1('#skF_5', '#skF_3'('#skF_5', B_124)) | B_124='#skF_5' | k1_relat_1(B_124)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_809])).
% 5.53/2.08  tff(c_26, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_3'(A_14, B_18))!=k1_funct_1(A_14, '#skF_3'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.53/2.08  tff(c_2972, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_5') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2939, c_26])).
% 5.53/2.08  tff(c_2994, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_473, c_40, c_38, c_2972])).
% 5.53/2.08  tff(c_2995, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_2994])).
% 5.53/2.08  tff(c_3007, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2995])).
% 5.53/2.08  tff(c_3010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_3007])).
% 5.53/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.08  
% 5.53/2.08  Inference rules
% 5.53/2.08  ----------------------
% 5.53/2.08  #Ref     : 5
% 5.53/2.08  #Sup     : 669
% 5.53/2.08  #Fact    : 0
% 5.53/2.08  #Define  : 0
% 5.53/2.08  #Split   : 8
% 5.53/2.08  #Chain   : 0
% 5.53/2.08  #Close   : 0
% 5.53/2.08  
% 5.53/2.08  Ordering : KBO
% 5.53/2.08  
% 5.53/2.08  Simplification rules
% 5.53/2.08  ----------------------
% 5.53/2.08  #Subsume      : 111
% 5.53/2.08  #Demod        : 1064
% 5.53/2.08  #Tautology    : 227
% 5.53/2.08  #SimpNegUnit  : 1
% 5.53/2.08  #BackRed      : 0
% 5.53/2.08  
% 5.53/2.08  #Partial instantiations: 0
% 5.53/2.08  #Strategies tried      : 1
% 5.53/2.08  
% 5.53/2.08  Timing (in seconds)
% 5.53/2.08  ----------------------
% 5.53/2.08  Preprocessing        : 0.39
% 5.53/2.08  Parsing              : 0.21
% 5.53/2.08  CNF conversion       : 0.03
% 5.53/2.08  Main loop            : 0.89
% 5.53/2.08  Inferencing          : 0.30
% 5.53/2.08  Reduction            : 0.30
% 5.53/2.08  Demodulation         : 0.21
% 5.53/2.08  BG Simplification    : 0.05
% 5.53/2.08  Subsumption          : 0.20
% 5.53/2.08  Abstraction          : 0.05
% 5.53/2.08  MUC search           : 0.00
% 5.53/2.08  Cooper               : 0.00
% 5.53/2.08  Total                : 1.32
% 5.53/2.08  Index Insertion      : 0.00
% 5.53/2.08  Index Deletion       : 0.00
% 5.53/2.08  Index Matching       : 0.00
% 5.53/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
