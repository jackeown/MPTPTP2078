%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  147 (2945 expanded)
%              Number of leaves         :   20 (1132 expanded)
%              Depth                    :   30
%              Number of atoms          :  544 (18248 expanded)
%              Number of equality atoms :  226 (7076 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_32,plain,(
    k2_funct_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_489,plain,(
    ! [A_58,B_59] :
      ( k1_funct_1(A_58,'#skF_2'(A_58,B_59)) = '#skF_1'(A_58,B_59)
      | k1_funct_1(B_59,'#skF_3'(A_58,B_59)) = '#skF_4'(A_58,B_59)
      | k2_funct_1(A_58) = B_59
      | k2_relat_1(A_58) != k1_relat_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_295,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),k1_relat_1(A_53))
      | k1_funct_1(B_54,'#skF_3'(A_53,B_54)) = '#skF_4'(A_53,B_54)
      | k2_funct_1(A_53) = B_54
      | k2_relat_1(A_53) != k1_relat_1(B_54)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(k1_funct_1(B_29,A_30),k2_relat_1(B_29))
      | ~ r2_hidden(A_30,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_5',A_30),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_72,plain,(
    ! [A_33] :
      ( r2_hidden(k1_funct_1('#skF_5',A_33),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_33,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_65])).

tff(c_50,plain,(
    ! [C_27] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_27)) = C_27
      | ~ r2_hidden(k1_funct_1('#skF_5',C_27),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_27,k1_relat_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_76,plain,(
    ! [A_33] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_33)) = A_33
      | ~ r2_hidden(A_33,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72,c_50])).

tff(c_303,plain,(
    ! [B_54] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5',B_54))) = '#skF_2'('#skF_5',B_54)
      | k1_funct_1(B_54,'#skF_3'('#skF_5',B_54)) = '#skF_4'('#skF_5',B_54)
      | k2_funct_1('#skF_5') = B_54
      | k2_relat_1('#skF_5') != k1_relat_1(B_54)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_295,c_76])).

tff(c_337,plain,(
    ! [B_54] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5',B_54))) = '#skF_2'('#skF_5',B_54)
      | k1_funct_1(B_54,'#skF_3'('#skF_5',B_54)) = '#skF_4'('#skF_5',B_54)
      | k2_funct_1('#skF_5') = B_54
      | k1_relat_1(B_54) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_303])).

tff(c_496,plain,(
    ! [B_59] :
      ( k1_funct_1('#skF_6','#skF_1'('#skF_5',B_59)) = '#skF_2'('#skF_5',B_59)
      | k1_funct_1(B_59,'#skF_3'('#skF_5',B_59)) = '#skF_4'('#skF_5',B_59)
      | k2_funct_1('#skF_5') = B_59
      | k1_relat_1(B_59) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | k1_funct_1(B_59,'#skF_3'('#skF_5',B_59)) = '#skF_4'('#skF_5',B_59)
      | k2_funct_1('#skF_5') = B_59
      | k2_relat_1('#skF_5') != k1_relat_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_337])).

tff(c_613,plain,(
    ! [B_60] :
      ( k1_funct_1('#skF_6','#skF_1'('#skF_5',B_60)) = '#skF_2'('#skF_5',B_60)
      | k1_funct_1(B_60,'#skF_3'('#skF_5',B_60)) = '#skF_4'('#skF_5',B_60)
      | k2_funct_1('#skF_5') = B_60
      | k1_relat_1(B_60) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_496])).

tff(c_36,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_6',A_30),k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_59])).

tff(c_67,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_6',A_30),k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62])).

tff(c_675,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_67])).

tff(c_727,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_675])).

tff(c_728,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_727])).

tff(c_738,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_258,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),k1_relat_1(A_46))
      | r2_hidden('#skF_3'(A_46,B_47),k2_relat_1(A_46))
      | k2_funct_1(A_46) = B_47
      | k2_relat_1(A_46) != k1_relat_1(B_47)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_264,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_2'('#skF_5',B_47),k1_relat_1('#skF_5'))
      | r2_hidden('#skF_3'('#skF_5',B_47),k1_relat_1('#skF_6'))
      | k2_funct_1('#skF_5') = B_47
      | k2_relat_1('#skF_5') != k1_relat_1(B_47)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_258])).

tff(c_268,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_2'('#skF_5',B_47),k1_relat_1('#skF_5'))
      | r2_hidden('#skF_3'('#skF_5',B_47),k1_relat_1('#skF_6'))
      | k2_funct_1('#skF_5') = B_47
      | k1_relat_1(B_47) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_264])).

tff(c_744,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_268,c_738])).

tff(c_751,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_744])).

tff(c_752,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_751])).

tff(c_279,plain,(
    ! [A_50,B_51] :
      ( k1_funct_1(A_50,'#skF_2'(A_50,B_51)) = '#skF_1'(A_50,B_51)
      | r2_hidden('#skF_3'(A_50,B_51),k2_relat_1(A_50))
      | k2_funct_1(A_50) = B_51
      | k2_relat_1(A_50) != k1_relat_1(B_51)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_285,plain,(
    ! [B_51] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_51)) = '#skF_1'('#skF_5',B_51)
      | r2_hidden('#skF_3'('#skF_5',B_51),k1_relat_1('#skF_6'))
      | k2_funct_1('#skF_5') = B_51
      | k2_relat_1('#skF_5') != k1_relat_1(B_51)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_279])).

tff(c_289,plain,(
    ! [B_51] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_51)) = '#skF_1'('#skF_5',B_51)
      | r2_hidden('#skF_3'('#skF_5',B_51),k1_relat_1('#skF_6'))
      | k2_funct_1('#skF_5') = B_51
      | k1_relat_1(B_51) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_285])).

tff(c_741,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_289,c_738])).

tff(c_747,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_741])).

tff(c_748,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_747])).

tff(c_69,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_5',A_30),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_65])).

tff(c_787,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_69])).

tff(c_809,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_787])).

tff(c_756,plain,(
    k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6'))) = '#skF_2'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_752,c_76])).

tff(c_880,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_756])).

tff(c_910,plain,(
    ! [B_63,A_64] :
      ( k1_funct_1(B_63,'#skF_1'(A_64,B_63)) != '#skF_2'(A_64,B_63)
      | ~ r2_hidden('#skF_1'(A_64,B_63),k2_relat_1(A_64))
      | r2_hidden('#skF_3'(A_64,B_63),k2_relat_1(A_64))
      | k2_funct_1(A_64) = B_63
      | k2_relat_1(A_64) != k1_relat_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_912,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k2_relat_1('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5','#skF_6'),k2_relat_1('#skF_5'))
    | k2_funct_1('#skF_5') = '#skF_6'
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_910])).

tff(c_916,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_42,c_40,c_34,c_34,c_809,c_34,c_912])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_738,c_916])).

tff(c_919,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6')
    | r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_995,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_585,plain,(
    ! [B_59] :
      ( k1_funct_1('#skF_6','#skF_1'('#skF_5',B_59)) = '#skF_2'('#skF_5',B_59)
      | k1_funct_1(B_59,'#skF_3'('#skF_5',B_59)) = '#skF_4'('#skF_5',B_59)
      | k2_funct_1('#skF_5') = B_59
      | k1_relat_1(B_59) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_496])).

tff(c_920,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_107,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',D_36)) = D_36
      | ~ r2_hidden(D_36,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_6',D_36),k1_relat_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_114,plain,(
    ! [A_30] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_30)) = A_30
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_67,c_107])).

tff(c_924,plain,(
    k1_funct_1('#skF_5',k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6'))) = '#skF_3'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_920,c_114])).

tff(c_950,plain,
    ( k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_924])).

tff(c_983,plain,
    ( k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_950])).

tff(c_984,plain,
    ( k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_983])).

tff(c_996,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_984])).

tff(c_14,plain,(
    ! [A_3,B_13] :
      ( r2_hidden('#skF_2'(A_3,B_13),k1_relat_1(A_3))
      | k1_funct_1(B_13,'#skF_3'(A_3,B_13)) = '#skF_4'(A_3,B_13)
      | k2_funct_1(A_3) = B_13
      | k2_relat_1(A_3) != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_519,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_5',B_59),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'('#skF_5',B_59),k1_relat_1('#skF_5'))
      | k1_funct_1(B_59,'#skF_3'('#skF_5',B_59)) = '#skF_4'('#skF_5',B_59)
      | k2_funct_1('#skF_5') = B_59
      | k2_relat_1('#skF_5') != k1_relat_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_69])).

tff(c_1073,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_5',B_67),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'('#skF_5',B_67),k1_relat_1('#skF_5'))
      | k1_funct_1(B_67,'#skF_3'('#skF_5',B_67)) = '#skF_4'('#skF_5',B_67)
      | k2_funct_1('#skF_5') = B_67
      | k1_relat_1(B_67) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_519])).

tff(c_1079,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_1'('#skF_5',B_13),k1_relat_1('#skF_6'))
      | k1_relat_1(B_13) != k1_relat_1('#skF_6')
      | k1_funct_1(B_13,'#skF_3'('#skF_5',B_13)) = '#skF_4'('#skF_5',B_13)
      | k2_funct_1('#skF_5') = B_13
      | k2_relat_1('#skF_5') != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_1073])).

tff(c_1089,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_1'('#skF_5',B_68),k1_relat_1('#skF_6'))
      | k1_funct_1(B_68,'#skF_3'('#skF_5',B_68)) = '#skF_4'('#skF_5',B_68)
      | k2_funct_1('#skF_5') = B_68
      | k1_relat_1(B_68) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_1079])).

tff(c_1011,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_67])).

tff(c_1052,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_1092,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1089,c_1052])).

tff(c_1157,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1092])).

tff(c_1158,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1157])).

tff(c_1186,plain,(
    k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_924])).

tff(c_8,plain,(
    ! [A_3,B_13] :
      ( r2_hidden('#skF_2'(A_3,B_13),k1_relat_1(A_3))
      | k1_funct_1(A_3,'#skF_4'(A_3,B_13)) != '#skF_3'(A_3,B_13)
      | ~ r2_hidden('#skF_4'(A_3,B_13),k1_relat_1(A_3))
      | k2_funct_1(A_3) = B_13
      | k2_relat_1(A_3) != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1862,plain,(
    ! [A_84,B_85] :
      ( k1_funct_1(A_84,'#skF_2'(A_84,B_85)) = '#skF_1'(A_84,B_85)
      | k1_funct_1(A_84,'#skF_4'(A_84,B_85)) != '#skF_3'(A_84,B_85)
      | ~ r2_hidden('#skF_4'(A_84,B_85),k1_relat_1(A_84))
      | k2_funct_1(A_84) = B_85
      | k2_relat_1(A_84) != k1_relat_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1865,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_995,c_1862])).

tff(c_1868,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_42,c_40,c_34,c_1186,c_1865])).

tff(c_1869,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1868])).

tff(c_1892,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_69])).

tff(c_1918,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1052,c_1892])).

tff(c_1932,plain,
    ( k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | k2_funct_1('#skF_5') = '#skF_6'
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1918])).

tff(c_1945,plain,(
    k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_42,c_40,c_34,c_995,c_1186,c_1932])).

tff(c_1947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1945])).

tff(c_1949,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_2521,plain,(
    ! [B_101,A_102] :
      ( k1_funct_1(B_101,'#skF_1'(A_102,B_101)) != '#skF_2'(A_102,B_101)
      | ~ r2_hidden('#skF_1'(A_102,B_101),k2_relat_1(A_102))
      | k1_funct_1(B_101,'#skF_3'(A_102,B_101)) = '#skF_4'(A_102,B_101)
      | k2_funct_1(A_102) = B_101
      | k2_relat_1(A_102) != k1_relat_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101)
      | ~ v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2525,plain,(
    ! [B_101] :
      ( k1_funct_1(B_101,'#skF_1'('#skF_5',B_101)) != '#skF_2'('#skF_5',B_101)
      | ~ r2_hidden('#skF_1'('#skF_5',B_101),k1_relat_1('#skF_6'))
      | k1_funct_1(B_101,'#skF_3'('#skF_5',B_101)) = '#skF_4'('#skF_5',B_101)
      | k2_funct_1('#skF_5') = B_101
      | k2_relat_1('#skF_5') != k1_relat_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2521])).

tff(c_2530,plain,(
    ! [B_103] :
      ( k1_funct_1(B_103,'#skF_1'('#skF_5',B_103)) != '#skF_2'('#skF_5',B_103)
      | ~ r2_hidden('#skF_1'('#skF_5',B_103),k1_relat_1('#skF_6'))
      | k1_funct_1(B_103,'#skF_3'('#skF_5',B_103)) = '#skF_4'('#skF_5',B_103)
      | k2_funct_1('#skF_5') = B_103
      | k1_relat_1(B_103) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_2525])).

tff(c_2534,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) != '#skF_2'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1949,c_2530])).

tff(c_2538,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_996,c_2534])).

tff(c_2539,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2538])).

tff(c_2540,plain,(
    k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2539,c_924])).

tff(c_3488,plain,(
    ! [B_119,A_120] :
      ( k1_funct_1(B_119,'#skF_1'(A_120,B_119)) != '#skF_2'(A_120,B_119)
      | ~ r2_hidden('#skF_1'(A_120,B_119),k2_relat_1(A_120))
      | k1_funct_1(A_120,'#skF_4'(A_120,B_119)) != '#skF_3'(A_120,B_119)
      | ~ r2_hidden('#skF_4'(A_120,B_119),k1_relat_1(A_120))
      | k2_funct_1(A_120) = B_119
      | k2_relat_1(A_120) != k1_relat_1(B_119)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3490,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k2_relat_1('#skF_5'))
    | k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | k2_funct_1('#skF_5') = '#skF_6'
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_3488])).

tff(c_3494,plain,(
    k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_42,c_40,c_34,c_995,c_2540,c_1949,c_34,c_3490])).

tff(c_3496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3494])).

tff(c_3498,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) != '#skF_2'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_984])).

tff(c_3497,plain,(
    k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_984])).

tff(c_4432,plain,(
    ! [A_143,B_144] :
      ( k1_funct_1(A_143,'#skF_2'(A_143,B_144)) = '#skF_1'(A_143,B_144)
      | k1_funct_1(A_143,'#skF_4'(A_143,B_144)) != '#skF_3'(A_143,B_144)
      | ~ r2_hidden('#skF_4'(A_143,B_144),k1_relat_1(A_143))
      | k2_funct_1(A_143) = B_144
      | k2_relat_1(A_143) != k1_relat_1(B_144)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v2_funct_1(A_143)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4435,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_995,c_4432])).

tff(c_4438,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_42,c_40,c_34,c_3497,c_4435])).

tff(c_4439,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4438])).

tff(c_3599,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_2'(A_121,B_122),k1_relat_1(A_121))
      | k1_funct_1(A_121,'#skF_4'(A_121,B_122)) != '#skF_3'(A_121,B_122)
      | ~ r2_hidden('#skF_4'(A_121,B_122),k1_relat_1(A_121))
      | k2_funct_1(A_121) = B_122
      | k2_relat_1(A_121) != k1_relat_1(B_122)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122)
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3607,plain,(
    ! [B_122] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5',B_122))) = '#skF_2'('#skF_5',B_122)
      | k1_funct_1('#skF_5','#skF_4'('#skF_5',B_122)) != '#skF_3'('#skF_5',B_122)
      | ~ r2_hidden('#skF_4'('#skF_5',B_122),k1_relat_1('#skF_5'))
      | k2_funct_1('#skF_5') = B_122
      | k2_relat_1('#skF_5') != k1_relat_1(B_122)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3599,c_76])).

tff(c_4063,plain,(
    ! [B_135] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5',B_135))) = '#skF_2'('#skF_5',B_135)
      | k1_funct_1('#skF_5','#skF_4'('#skF_5',B_135)) != '#skF_3'('#skF_5',B_135)
      | ~ r2_hidden('#skF_4'('#skF_5',B_135),k1_relat_1('#skF_5'))
      | k2_funct_1('#skF_5') = B_135
      | k1_relat_1(B_135) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_3607])).

tff(c_4066,plain,
    ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6'))) = '#skF_2'('#skF_5','#skF_6')
    | k1_funct_1('#skF_5','#skF_4'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_995,c_4063])).

tff(c_4069,plain,
    ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6'))) = '#skF_2'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3497,c_4066])).

tff(c_4070,plain,(
    k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6'))) = '#skF_2'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4069])).

tff(c_4441,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4439,c_4070])).

tff(c_4443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3498,c_4441])).

tff(c_4445,plain,(
    ~ r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_4444,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_2'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_4573,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_1'('#skF_5',B_148),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'('#skF_5',B_148),k1_relat_1('#skF_5'))
      | k1_funct_1(B_148,'#skF_3'('#skF_5',B_148)) = '#skF_4'('#skF_5',B_148)
      | k2_funct_1('#skF_5') = B_148
      | k1_relat_1(B_148) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_519])).

tff(c_4581,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_1'('#skF_5',B_13),k1_relat_1('#skF_6'))
      | k1_relat_1(B_13) != k1_relat_1('#skF_6')
      | k1_funct_1(B_13,'#skF_3'('#skF_5',B_13)) = '#skF_4'('#skF_5',B_13)
      | k2_funct_1('#skF_5') = B_13
      | k2_relat_1('#skF_5') != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_4573])).

tff(c_4592,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_1'('#skF_5',B_149),k1_relat_1('#skF_6'))
      | k1_funct_1(B_149,'#skF_3'('#skF_5',B_149)) = '#skF_4'('#skF_5',B_149)
      | k2_funct_1('#skF_5') = B_149
      | k1_relat_1(B_149) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_4581])).

tff(c_4456,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4444,c_67])).

tff(c_4470,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4456])).

tff(c_4595,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4592,c_4470])).

tff(c_4666,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4595])).

tff(c_4667,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4666])).

tff(c_4713,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_67])).

tff(c_4745,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_4713])).

tff(c_4747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4445,c_4745])).

tff(c_4749,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4456])).

tff(c_5356,plain,(
    ! [B_169,A_170] :
      ( k1_funct_1(B_169,'#skF_1'(A_170,B_169)) != '#skF_2'(A_170,B_169)
      | ~ r2_hidden('#skF_1'(A_170,B_169),k2_relat_1(A_170))
      | k1_funct_1(B_169,'#skF_3'(A_170,B_169)) = '#skF_4'(A_170,B_169)
      | k2_funct_1(A_170) = B_169
      | k2_relat_1(A_170) != k1_relat_1(B_169)
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169)
      | ~ v2_funct_1(A_170)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5360,plain,(
    ! [B_169] :
      ( k1_funct_1(B_169,'#skF_1'('#skF_5',B_169)) != '#skF_2'('#skF_5',B_169)
      | ~ r2_hidden('#skF_1'('#skF_5',B_169),k1_relat_1('#skF_6'))
      | k1_funct_1(B_169,'#skF_3'('#skF_5',B_169)) = '#skF_4'('#skF_5',B_169)
      | k2_funct_1('#skF_5') = B_169
      | k2_relat_1('#skF_5') != k1_relat_1(B_169)
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5356])).

tff(c_5365,plain,(
    ! [B_171] :
      ( k1_funct_1(B_171,'#skF_1'('#skF_5',B_171)) != '#skF_2'('#skF_5',B_171)
      | ~ r2_hidden('#skF_1'('#skF_5',B_171),k1_relat_1('#skF_6'))
      | k1_funct_1(B_171,'#skF_3'('#skF_5',B_171)) = '#skF_4'('#skF_5',B_171)
      | k2_funct_1('#skF_5') = B_171
      | k1_relat_1(B_171) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_5360])).

tff(c_5369,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) != '#skF_2'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4749,c_5365])).

tff(c_5373,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4444,c_5369])).

tff(c_5374,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5373])).

tff(c_5406,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5374,c_67])).

tff(c_5445,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_5406])).

tff(c_5447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4445,c_5445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:19:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.66/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.32  
% 6.66/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.32  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 6.66/2.32  
% 6.66/2.32  %Foreground sorts:
% 6.66/2.32  
% 6.66/2.32  
% 6.66/2.32  %Background operators:
% 6.66/2.32  
% 6.66/2.32  
% 6.66/2.32  %Foreground operators:
% 6.66/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.66/2.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.66/2.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.66/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.66/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.66/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.66/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.66/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.66/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.66/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.66/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.66/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.66/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.66/2.32  
% 6.66/2.35  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 6.66/2.35  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 6.66/2.35  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 6.66/2.35  tff(c_32, plain, (k2_funct_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_38, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_34, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_489, plain, (![A_58, B_59]: (k1_funct_1(A_58, '#skF_2'(A_58, B_59))='#skF_1'(A_58, B_59) | k1_funct_1(B_59, '#skF_3'(A_58, B_59))='#skF_4'(A_58, B_59) | k2_funct_1(A_58)=B_59 | k2_relat_1(A_58)!=k1_relat_1(B_59) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_295, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), k1_relat_1(A_53)) | k1_funct_1(B_54, '#skF_3'(A_53, B_54))='#skF_4'(A_53, B_54) | k2_funct_1(A_53)=B_54 | k2_relat_1(A_53)!=k1_relat_1(B_54) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_59, plain, (![B_29, A_30]: (r2_hidden(k1_funct_1(B_29, A_30), k2_relat_1(B_29)) | ~r2_hidden(A_30, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.66/2.35  tff(c_65, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_5', A_30), k1_relat_1('#skF_6')) | ~r2_hidden(A_30, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_59])).
% 6.66/2.35  tff(c_72, plain, (![A_33]: (r2_hidden(k1_funct_1('#skF_5', A_33), k1_relat_1('#skF_6')) | ~r2_hidden(A_33, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_65])).
% 6.66/2.35  tff(c_50, plain, (![C_27]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_27))=C_27 | ~r2_hidden(k1_funct_1('#skF_5', C_27), k1_relat_1('#skF_6')) | ~r2_hidden(C_27, k1_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_76, plain, (![A_33]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_33))=A_33 | ~r2_hidden(A_33, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_72, c_50])).
% 6.66/2.35  tff(c_303, plain, (![B_54]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_54)))='#skF_2'('#skF_5', B_54) | k1_funct_1(B_54, '#skF_3'('#skF_5', B_54))='#skF_4'('#skF_5', B_54) | k2_funct_1('#skF_5')=B_54 | k2_relat_1('#skF_5')!=k1_relat_1(B_54) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_295, c_76])).
% 6.66/2.35  tff(c_337, plain, (![B_54]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_54)))='#skF_2'('#skF_5', B_54) | k1_funct_1(B_54, '#skF_3'('#skF_5', B_54))='#skF_4'('#skF_5', B_54) | k2_funct_1('#skF_5')=B_54 | k1_relat_1(B_54)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_303])).
% 6.66/2.35  tff(c_496, plain, (![B_59]: (k1_funct_1('#skF_6', '#skF_1'('#skF_5', B_59))='#skF_2'('#skF_5', B_59) | k1_funct_1(B_59, '#skF_3'('#skF_5', B_59))='#skF_4'('#skF_5', B_59) | k2_funct_1('#skF_5')=B_59 | k1_relat_1(B_59)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | k1_funct_1(B_59, '#skF_3'('#skF_5', B_59))='#skF_4'('#skF_5', B_59) | k2_funct_1('#skF_5')=B_59 | k2_relat_1('#skF_5')!=k1_relat_1(B_59) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_489, c_337])).
% 6.66/2.35  tff(c_613, plain, (![B_60]: (k1_funct_1('#skF_6', '#skF_1'('#skF_5', B_60))='#skF_2'('#skF_5', B_60) | k1_funct_1(B_60, '#skF_3'('#skF_5', B_60))='#skF_4'('#skF_5', B_60) | k2_funct_1('#skF_5')=B_60 | k1_relat_1(B_60)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_496])).
% 6.66/2.35  tff(c_36, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_62, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_6', A_30), k1_relat_1('#skF_5')) | ~r2_hidden(A_30, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_59])).
% 6.66/2.35  tff(c_67, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_6', A_30), k1_relat_1('#skF_5')) | ~r2_hidden(A_30, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62])).
% 6.66/2.35  tff(c_675, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_613, c_67])).
% 6.66/2.35  tff(c_727, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_675])).
% 6.66/2.35  tff(c_728, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_727])).
% 6.66/2.35  tff(c_738, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_728])).
% 6.66/2.35  tff(c_258, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), k1_relat_1(A_46)) | r2_hidden('#skF_3'(A_46, B_47), k2_relat_1(A_46)) | k2_funct_1(A_46)=B_47 | k2_relat_1(A_46)!=k1_relat_1(B_47) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_264, plain, (![B_47]: (r2_hidden('#skF_2'('#skF_5', B_47), k1_relat_1('#skF_5')) | r2_hidden('#skF_3'('#skF_5', B_47), k1_relat_1('#skF_6')) | k2_funct_1('#skF_5')=B_47 | k2_relat_1('#skF_5')!=k1_relat_1(B_47) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_258])).
% 6.66/2.35  tff(c_268, plain, (![B_47]: (r2_hidden('#skF_2'('#skF_5', B_47), k1_relat_1('#skF_5')) | r2_hidden('#skF_3'('#skF_5', B_47), k1_relat_1('#skF_6')) | k2_funct_1('#skF_5')=B_47 | k1_relat_1(B_47)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_264])).
% 6.66/2.35  tff(c_744, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_268, c_738])).
% 6.66/2.35  tff(c_751, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_744])).
% 6.66/2.35  tff(c_752, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_751])).
% 6.66/2.35  tff(c_279, plain, (![A_50, B_51]: (k1_funct_1(A_50, '#skF_2'(A_50, B_51))='#skF_1'(A_50, B_51) | r2_hidden('#skF_3'(A_50, B_51), k2_relat_1(A_50)) | k2_funct_1(A_50)=B_51 | k2_relat_1(A_50)!=k1_relat_1(B_51) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_285, plain, (![B_51]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_51))='#skF_1'('#skF_5', B_51) | r2_hidden('#skF_3'('#skF_5', B_51), k1_relat_1('#skF_6')) | k2_funct_1('#skF_5')=B_51 | k2_relat_1('#skF_5')!=k1_relat_1(B_51) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_279])).
% 6.66/2.35  tff(c_289, plain, (![B_51]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_51))='#skF_1'('#skF_5', B_51) | r2_hidden('#skF_3'('#skF_5', B_51), k1_relat_1('#skF_6')) | k2_funct_1('#skF_5')=B_51 | k1_relat_1(B_51)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_285])).
% 6.66/2.35  tff(c_741, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_289, c_738])).
% 6.66/2.35  tff(c_747, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_741])).
% 6.66/2.35  tff(c_748, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_747])).
% 6.66/2.35  tff(c_69, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_5', A_30), k1_relat_1('#skF_6')) | ~r2_hidden(A_30, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_65])).
% 6.66/2.35  tff(c_787, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_748, c_69])).
% 6.66/2.35  tff(c_809, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_787])).
% 6.66/2.35  tff(c_756, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6')))='#skF_2'('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_752, c_76])).
% 6.66/2.35  tff(c_880, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_748, c_756])).
% 6.66/2.35  tff(c_910, plain, (![B_63, A_64]: (k1_funct_1(B_63, '#skF_1'(A_64, B_63))!='#skF_2'(A_64, B_63) | ~r2_hidden('#skF_1'(A_64, B_63), k2_relat_1(A_64)) | r2_hidden('#skF_3'(A_64, B_63), k2_relat_1(A_64)) | k2_funct_1(A_64)=B_63 | k2_relat_1(A_64)!=k1_relat_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_912, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k2_relat_1('#skF_5')) | r2_hidden('#skF_3'('#skF_5', '#skF_6'), k2_relat_1('#skF_5')) | k2_funct_1('#skF_5')='#skF_6' | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_880, c_910])).
% 6.66/2.35  tff(c_916, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_42, c_40, c_34, c_34, c_809, c_34, c_912])).
% 6.66/2.35  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_738, c_916])).
% 6.66/2.35  tff(c_919, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6') | r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_728])).
% 6.66/2.35  tff(c_995, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_919])).
% 6.66/2.35  tff(c_585, plain, (![B_59]: (k1_funct_1('#skF_6', '#skF_1'('#skF_5', B_59))='#skF_2'('#skF_5', B_59) | k1_funct_1(B_59, '#skF_3'('#skF_5', B_59))='#skF_4'('#skF_5', B_59) | k2_funct_1('#skF_5')=B_59 | k1_relat_1(B_59)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_496])).
% 6.66/2.35  tff(c_920, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_728])).
% 6.66/2.35  tff(c_107, plain, (![D_36]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', D_36))=D_36 | ~r2_hidden(D_36, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_6', D_36), k1_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.66/2.35  tff(c_114, plain, (![A_30]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_30))=A_30 | ~r2_hidden(A_30, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_67, c_107])).
% 6.66/2.35  tff(c_924, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6')))='#skF_3'('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_920, c_114])).
% 6.66/2.35  tff(c_950, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_585, c_924])).
% 6.66/2.35  tff(c_983, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_950])).
% 6.66/2.35  tff(c_984, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_983])).
% 6.66/2.35  tff(c_996, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_984])).
% 6.66/2.35  tff(c_14, plain, (![A_3, B_13]: (r2_hidden('#skF_2'(A_3, B_13), k1_relat_1(A_3)) | k1_funct_1(B_13, '#skF_3'(A_3, B_13))='#skF_4'(A_3, B_13) | k2_funct_1(A_3)=B_13 | k2_relat_1(A_3)!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_519, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_5', B_59), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', B_59), k1_relat_1('#skF_5')) | k1_funct_1(B_59, '#skF_3'('#skF_5', B_59))='#skF_4'('#skF_5', B_59) | k2_funct_1('#skF_5')=B_59 | k2_relat_1('#skF_5')!=k1_relat_1(B_59) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_489, c_69])).
% 6.66/2.35  tff(c_1073, plain, (![B_67]: (r2_hidden('#skF_1'('#skF_5', B_67), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', B_67), k1_relat_1('#skF_5')) | k1_funct_1(B_67, '#skF_3'('#skF_5', B_67))='#skF_4'('#skF_5', B_67) | k2_funct_1('#skF_5')=B_67 | k1_relat_1(B_67)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_519])).
% 6.66/2.35  tff(c_1079, plain, (![B_13]: (r2_hidden('#skF_1'('#skF_5', B_13), k1_relat_1('#skF_6')) | k1_relat_1(B_13)!=k1_relat_1('#skF_6') | k1_funct_1(B_13, '#skF_3'('#skF_5', B_13))='#skF_4'('#skF_5', B_13) | k2_funct_1('#skF_5')=B_13 | k2_relat_1('#skF_5')!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_1073])).
% 6.66/2.35  tff(c_1089, plain, (![B_68]: (r2_hidden('#skF_1'('#skF_5', B_68), k1_relat_1('#skF_6')) | k1_funct_1(B_68, '#skF_3'('#skF_5', B_68))='#skF_4'('#skF_5', B_68) | k2_funct_1('#skF_5')=B_68 | k1_relat_1(B_68)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_1079])).
% 6.66/2.35  tff(c_1011, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_996, c_67])).
% 6.66/2.35  tff(c_1052, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1011])).
% 6.66/2.35  tff(c_1092, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1089, c_1052])).
% 6.66/2.35  tff(c_1157, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1092])).
% 6.66/2.35  tff(c_1158, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_1157])).
% 6.66/2.35  tff(c_1186, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_924])).
% 6.66/2.35  tff(c_8, plain, (![A_3, B_13]: (r2_hidden('#skF_2'(A_3, B_13), k1_relat_1(A_3)) | k1_funct_1(A_3, '#skF_4'(A_3, B_13))!='#skF_3'(A_3, B_13) | ~r2_hidden('#skF_4'(A_3, B_13), k1_relat_1(A_3)) | k2_funct_1(A_3)=B_13 | k2_relat_1(A_3)!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_1862, plain, (![A_84, B_85]: (k1_funct_1(A_84, '#skF_2'(A_84, B_85))='#skF_1'(A_84, B_85) | k1_funct_1(A_84, '#skF_4'(A_84, B_85))!='#skF_3'(A_84, B_85) | ~r2_hidden('#skF_4'(A_84, B_85), k1_relat_1(A_84)) | k2_funct_1(A_84)=B_85 | k2_relat_1(A_84)!=k1_relat_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_1865, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_995, c_1862])).
% 6.66/2.35  tff(c_1868, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_42, c_40, c_34, c_1186, c_1865])).
% 6.66/2.35  tff(c_1869, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_1868])).
% 6.66/2.35  tff(c_1892, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1869, c_69])).
% 6.66/2.35  tff(c_1918, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1052, c_1892])).
% 6.66/2.35  tff(c_1932, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6') | ~r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')='#skF_6' | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1918])).
% 6.66/2.35  tff(c_1945, plain, (k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_42, c_40, c_34, c_995, c_1186, c_1932])).
% 6.66/2.35  tff(c_1947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1945])).
% 6.66/2.35  tff(c_1949, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1011])).
% 6.66/2.35  tff(c_2521, plain, (![B_101, A_102]: (k1_funct_1(B_101, '#skF_1'(A_102, B_101))!='#skF_2'(A_102, B_101) | ~r2_hidden('#skF_1'(A_102, B_101), k2_relat_1(A_102)) | k1_funct_1(B_101, '#skF_3'(A_102, B_101))='#skF_4'(A_102, B_101) | k2_funct_1(A_102)=B_101 | k2_relat_1(A_102)!=k1_relat_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101) | ~v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_2525, plain, (![B_101]: (k1_funct_1(B_101, '#skF_1'('#skF_5', B_101))!='#skF_2'('#skF_5', B_101) | ~r2_hidden('#skF_1'('#skF_5', B_101), k1_relat_1('#skF_6')) | k1_funct_1(B_101, '#skF_3'('#skF_5', B_101))='#skF_4'('#skF_5', B_101) | k2_funct_1('#skF_5')=B_101 | k2_relat_1('#skF_5')!=k1_relat_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2521])).
% 6.66/2.35  tff(c_2530, plain, (![B_103]: (k1_funct_1(B_103, '#skF_1'('#skF_5', B_103))!='#skF_2'('#skF_5', B_103) | ~r2_hidden('#skF_1'('#skF_5', B_103), k1_relat_1('#skF_6')) | k1_funct_1(B_103, '#skF_3'('#skF_5', B_103))='#skF_4'('#skF_5', B_103) | k2_funct_1('#skF_5')=B_103 | k1_relat_1(B_103)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_2525])).
% 6.66/2.35  tff(c_2534, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))!='#skF_2'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1949, c_2530])).
% 6.66/2.35  tff(c_2538, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_996, c_2534])).
% 6.66/2.35  tff(c_2539, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_2538])).
% 6.66/2.35  tff(c_2540, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2539, c_924])).
% 6.66/2.35  tff(c_3488, plain, (![B_119, A_120]: (k1_funct_1(B_119, '#skF_1'(A_120, B_119))!='#skF_2'(A_120, B_119) | ~r2_hidden('#skF_1'(A_120, B_119), k2_relat_1(A_120)) | k1_funct_1(A_120, '#skF_4'(A_120, B_119))!='#skF_3'(A_120, B_119) | ~r2_hidden('#skF_4'(A_120, B_119), k1_relat_1(A_120)) | k2_funct_1(A_120)=B_119 | k2_relat_1(A_120)!=k1_relat_1(B_119) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_3490, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k2_relat_1('#skF_5')) | k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6') | ~r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')='#skF_6' | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_996, c_3488])).
% 6.66/2.35  tff(c_3494, plain, (k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_42, c_40, c_34, c_995, c_2540, c_1949, c_34, c_3490])).
% 6.66/2.35  tff(c_3496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_3494])).
% 6.66/2.35  tff(c_3498, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))!='#skF_2'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_984])).
% 6.66/2.35  tff(c_3497, plain, (k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_984])).
% 6.66/2.35  tff(c_4432, plain, (![A_143, B_144]: (k1_funct_1(A_143, '#skF_2'(A_143, B_144))='#skF_1'(A_143, B_144) | k1_funct_1(A_143, '#skF_4'(A_143, B_144))!='#skF_3'(A_143, B_144) | ~r2_hidden('#skF_4'(A_143, B_144), k1_relat_1(A_143)) | k2_funct_1(A_143)=B_144 | k2_relat_1(A_143)!=k1_relat_1(B_144) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v2_funct_1(A_143) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_4435, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | k2_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_995, c_4432])).
% 6.66/2.35  tff(c_4438, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_42, c_40, c_34, c_3497, c_4435])).
% 6.66/2.35  tff(c_4439, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_4438])).
% 6.66/2.35  tff(c_3599, plain, (![A_121, B_122]: (r2_hidden('#skF_2'(A_121, B_122), k1_relat_1(A_121)) | k1_funct_1(A_121, '#skF_4'(A_121, B_122))!='#skF_3'(A_121, B_122) | ~r2_hidden('#skF_4'(A_121, B_122), k1_relat_1(A_121)) | k2_funct_1(A_121)=B_122 | k2_relat_1(A_121)!=k1_relat_1(B_122) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_3607, plain, (![B_122]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_122)))='#skF_2'('#skF_5', B_122) | k1_funct_1('#skF_5', '#skF_4'('#skF_5', B_122))!='#skF_3'('#skF_5', B_122) | ~r2_hidden('#skF_4'('#skF_5', B_122), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')=B_122 | k2_relat_1('#skF_5')!=k1_relat_1(B_122) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3599, c_76])).
% 6.66/2.35  tff(c_4063, plain, (![B_135]: (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_135)))='#skF_2'('#skF_5', B_135) | k1_funct_1('#skF_5', '#skF_4'('#skF_5', B_135))!='#skF_3'('#skF_5', B_135) | ~r2_hidden('#skF_4'('#skF_5', B_135), k1_relat_1('#skF_5')) | k2_funct_1('#skF_5')=B_135 | k1_relat_1(B_135)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_3607])).
% 6.66/2.35  tff(c_4066, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6')))='#skF_2'('#skF_5', '#skF_6') | k1_funct_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_995, c_4063])).
% 6.66/2.35  tff(c_4069, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6')))='#skF_2'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3497, c_4066])).
% 6.66/2.35  tff(c_4070, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6')))='#skF_2'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_4069])).
% 6.66/2.35  tff(c_4441, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4439, c_4070])).
% 6.66/2.35  tff(c_4443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3498, c_4441])).
% 6.66/2.35  tff(c_4445, plain, (~r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_919])).
% 6.66/2.35  tff(c_4444, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_2'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_919])).
% 6.66/2.35  tff(c_4573, plain, (![B_148]: (r2_hidden('#skF_1'('#skF_5', B_148), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', B_148), k1_relat_1('#skF_5')) | k1_funct_1(B_148, '#skF_3'('#skF_5', B_148))='#skF_4'('#skF_5', B_148) | k2_funct_1('#skF_5')=B_148 | k1_relat_1(B_148)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_519])).
% 6.66/2.35  tff(c_4581, plain, (![B_13]: (r2_hidden('#skF_1'('#skF_5', B_13), k1_relat_1('#skF_6')) | k1_relat_1(B_13)!=k1_relat_1('#skF_6') | k1_funct_1(B_13, '#skF_3'('#skF_5', B_13))='#skF_4'('#skF_5', B_13) | k2_funct_1('#skF_5')=B_13 | k2_relat_1('#skF_5')!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_4573])).
% 6.66/2.35  tff(c_4592, plain, (![B_149]: (r2_hidden('#skF_1'('#skF_5', B_149), k1_relat_1('#skF_6')) | k1_funct_1(B_149, '#skF_3'('#skF_5', B_149))='#skF_4'('#skF_5', B_149) | k2_funct_1('#skF_5')=B_149 | k1_relat_1(B_149)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_4581])).
% 6.66/2.35  tff(c_4456, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4444, c_67])).
% 6.66/2.35  tff(c_4470, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4456])).
% 6.66/2.35  tff(c_4595, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4592, c_4470])).
% 6.66/2.35  tff(c_4666, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4595])).
% 6.66/2.35  tff(c_4667, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_4666])).
% 6.66/2.35  tff(c_4713, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4667, c_67])).
% 6.66/2.35  tff(c_4745, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_4713])).
% 6.66/2.35  tff(c_4747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4445, c_4745])).
% 6.66/2.35  tff(c_4749, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4456])).
% 6.66/2.35  tff(c_5356, plain, (![B_169, A_170]: (k1_funct_1(B_169, '#skF_1'(A_170, B_169))!='#skF_2'(A_170, B_169) | ~r2_hidden('#skF_1'(A_170, B_169), k2_relat_1(A_170)) | k1_funct_1(B_169, '#skF_3'(A_170, B_169))='#skF_4'(A_170, B_169) | k2_funct_1(A_170)=B_169 | k2_relat_1(A_170)!=k1_relat_1(B_169) | ~v1_funct_1(B_169) | ~v1_relat_1(B_169) | ~v2_funct_1(A_170) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.35  tff(c_5360, plain, (![B_169]: (k1_funct_1(B_169, '#skF_1'('#skF_5', B_169))!='#skF_2'('#skF_5', B_169) | ~r2_hidden('#skF_1'('#skF_5', B_169), k1_relat_1('#skF_6')) | k1_funct_1(B_169, '#skF_3'('#skF_5', B_169))='#skF_4'('#skF_5', B_169) | k2_funct_1('#skF_5')=B_169 | k2_relat_1('#skF_5')!=k1_relat_1(B_169) | ~v1_funct_1(B_169) | ~v1_relat_1(B_169) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5356])).
% 6.66/2.35  tff(c_5365, plain, (![B_171]: (k1_funct_1(B_171, '#skF_1'('#skF_5', B_171))!='#skF_2'('#skF_5', B_171) | ~r2_hidden('#skF_1'('#skF_5', B_171), k1_relat_1('#skF_6')) | k1_funct_1(B_171, '#skF_3'('#skF_5', B_171))='#skF_4'('#skF_5', B_171) | k2_funct_1('#skF_5')=B_171 | k1_relat_1(B_171)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_5360])).
% 6.66/2.35  tff(c_5369, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))!='#skF_2'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4749, c_5365])).
% 6.66/2.35  tff(c_5373, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4444, c_5369])).
% 6.66/2.35  tff(c_5374, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_5373])).
% 6.66/2.35  tff(c_5406, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5374, c_67])).
% 6.66/2.35  tff(c_5445, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_5406])).
% 6.66/2.35  tff(c_5447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4445, c_5445])).
% 6.66/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.35  
% 6.66/2.35  Inference rules
% 6.66/2.35  ----------------------
% 6.66/2.35  #Ref     : 0
% 6.66/2.35  #Sup     : 1020
% 6.66/2.35  #Fact    : 0
% 6.66/2.35  #Define  : 0
% 6.66/2.35  #Split   : 14
% 6.66/2.35  #Chain   : 0
% 6.66/2.35  #Close   : 0
% 6.66/2.35  
% 6.66/2.35  Ordering : KBO
% 6.66/2.35  
% 6.66/2.35  Simplification rules
% 6.66/2.35  ----------------------
% 6.66/2.35  #Subsume      : 200
% 6.66/2.35  #Demod        : 1779
% 6.66/2.35  #Tautology    : 591
% 6.66/2.35  #SimpNegUnit  : 165
% 6.66/2.35  #BackRed      : 10
% 6.66/2.35  
% 6.66/2.35  #Partial instantiations: 0
% 6.66/2.35  #Strategies tried      : 1
% 6.66/2.35  
% 6.66/2.35  Timing (in seconds)
% 6.66/2.35  ----------------------
% 6.66/2.35  Preprocessing        : 0.32
% 6.66/2.35  Parsing              : 0.16
% 6.66/2.35  CNF conversion       : 0.03
% 6.66/2.35  Main loop            : 1.26
% 6.66/2.35  Inferencing          : 0.46
% 6.92/2.35  Reduction            : 0.39
% 6.92/2.35  Demodulation         : 0.27
% 6.92/2.35  BG Simplification    : 0.07
% 6.92/2.35  Subsumption          : 0.29
% 6.92/2.35  Abstraction          : 0.09
% 6.92/2.35  MUC search           : 0.00
% 6.92/2.35  Cooper               : 0.00
% 6.92/2.35  Total                : 1.64
% 6.92/2.35  Index Insertion      : 0.00
% 6.92/2.35  Index Deletion       : 0.00
% 6.92/2.35  Index Matching       : 0.00
% 6.92/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
