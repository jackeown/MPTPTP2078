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
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 242 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 (1008 expanded)
%              Number of equality atoms :   31 ( 257 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_95,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,(
    ! [A_45,D_46] :
      ( k1_funct_1(k2_funct_1(A_45),k1_funct_1(A_45,D_46)) = D_46
      | ~ r2_hidden(D_46,k1_relat_1(A_45))
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v1_relat_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_67,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_126,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_67])).

tff(c_136,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_126])).

tff(c_138,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_141])).

tff(c_146,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_150,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_150])).

tff(c_156,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_187,plain,(
    ! [A_52,D_53] :
      ( r2_hidden(k1_funct_1(A_52,D_53),k2_relat_1(A_52))
      | ~ r2_hidden(D_53,k1_relat_1(A_52))
      | ~ v1_funct_1(k2_funct_1(A_52))
      | ~ v1_relat_1(k2_funct_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_190,plain,
    ( r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_187])).

tff(c_373,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_376,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_376])).

tff(c_382,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_40,plain,(
    ! [A_12,D_28] :
      ( r2_hidden(k1_funct_1(A_12,D_28),k2_relat_1(A_12))
      | ~ r2_hidden(D_28,k1_relat_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_162,plain,(
    ! [A_49] :
      ( k1_relat_1(k2_funct_1(A_49)) = k2_relat_1(A_49)
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_167,plain,(
    ! [A_50] :
      ( k1_relat_1(k2_funct_1(A_50)) = k2_relat_1(A_50)
      | ~ v1_funct_1(k2_funct_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_171,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_381,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_383,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_386,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_383])).

tff(c_388,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_386])).

tff(c_391,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_388])).

tff(c_394,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_382,c_44,c_391])).

tff(c_398,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_394])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_398])).

tff(c_404,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_203,plain,(
    ! [A_55,D_56] :
      ( k1_funct_1(k2_funct_1(A_55),k1_funct_1(A_55,D_56)) = D_56
      | ~ r2_hidden(D_56,k1_relat_1(A_55))
      | ~ v1_funct_1(k2_funct_1(A_55))
      | ~ v1_relat_1(k2_funct_1(A_55))
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_224,plain,
    ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_203])).

tff(c_411,plain,
    ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_404,c_224])).

tff(c_412,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_415,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_412])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_415])).

tff(c_421,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_4,plain,(
    ! [A_4] :
      ( k7_relat_1(A_4,k1_relat_1(A_4)) = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_32,A_33)),k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_4] :
      ( r1_tarski(k2_relat_1(A_4),k2_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_172,plain,(
    ! [A_51] :
      ( k1_relat_1(k2_funct_1(A_51)) = k2_relat_1(A_51)
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k1_relat_1(k5_relat_1(A_1,B_3)) = k1_relat_1(A_1)
      | ~ r1_tarski(k2_relat_1(A_1),k1_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_286,plain,(
    ! [A_61,A_62] :
      ( k1_relat_1(k5_relat_1(A_61,k2_funct_1(A_62))) = k1_relat_1(A_61)
      | ~ r1_tarski(k2_relat_1(A_61),k2_relat_1(A_62))
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v1_relat_1(A_61)
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2])).

tff(c_301,plain,(
    ! [A_66] :
      ( k1_relat_1(k5_relat_1(A_66,k2_funct_1(A_66))) = k1_relat_1(A_66)
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_65,c_286])).

tff(c_12,plain,(
    ! [C_11,B_9,A_8] :
      ( k1_funct_1(k5_relat_1(C_11,B_9),A_8) = k1_funct_1(B_9,k1_funct_1(C_11,A_8))
      | ~ r2_hidden(A_8,k1_relat_1(k5_relat_1(C_11,B_9)))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_663,plain,(
    ! [A_86,A_87] :
      ( k1_funct_1(k5_relat_1(A_86,k2_funct_1(A_86)),A_87) = k1_funct_1(k2_funct_1(A_86),k1_funct_1(A_86,A_87))
      | ~ r2_hidden(A_87,k1_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86)
      | ~ v1_funct_1(k2_funct_1(A_86))
      | ~ v1_relat_1(k2_funct_1(A_86))
      | ~ v1_relat_1(k2_funct_1(A_86))
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_12])).

tff(c_155,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_691,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_155])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_382,c_382,c_421,c_50,c_48,c_44,c_156,c_691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.49  
% 3.31/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.49  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.31/1.49  
% 3.31/1.49  %Foreground sorts:
% 3.31/1.49  
% 3.31/1.49  
% 3.31/1.49  %Background operators:
% 3.31/1.49  
% 3.31/1.49  
% 3.31/1.49  %Foreground operators:
% 3.31/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.31/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.31/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.31/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.31/1.49  
% 3.47/1.51  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 3.47/1.51  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.47/1.51  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 3.47/1.51  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.47/1.51  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 3.47/1.51  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.47/1.51  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.47/1.51  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_46, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_10, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.51  tff(c_8, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.51  tff(c_44, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_111, plain, (![A_45, D_46]: (k1_funct_1(k2_funct_1(A_45), k1_funct_1(A_45, D_46))=D_46 | ~r2_hidden(D_46, k1_relat_1(A_45)) | ~v1_funct_1(k2_funct_1(A_45)) | ~v1_relat_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.51  tff(c_42, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_67, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 3.47/1.51  tff(c_126, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_111, c_67])).
% 3.47/1.51  tff(c_136, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_126])).
% 3.47/1.51  tff(c_138, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_136])).
% 3.47/1.51  tff(c_141, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_138])).
% 3.47/1.51  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_141])).
% 3.47/1.51  tff(c_146, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_136])).
% 3.47/1.51  tff(c_150, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_146])).
% 3.47/1.51  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_150])).
% 3.47/1.51  tff(c_156, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.47/1.51  tff(c_187, plain, (![A_52, D_53]: (r2_hidden(k1_funct_1(A_52, D_53), k2_relat_1(A_52)) | ~r2_hidden(D_53, k1_relat_1(A_52)) | ~v1_funct_1(k2_funct_1(A_52)) | ~v1_relat_1(k2_funct_1(A_52)) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.51  tff(c_190, plain, (r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_187])).
% 3.47/1.51  tff(c_373, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_190])).
% 3.47/1.51  tff(c_376, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_373])).
% 3.47/1.51  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_376])).
% 3.47/1.51  tff(c_382, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_190])).
% 3.47/1.51  tff(c_40, plain, (![A_12, D_28]: (r2_hidden(k1_funct_1(A_12, D_28), k2_relat_1(A_12)) | ~r2_hidden(D_28, k1_relat_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.51  tff(c_162, plain, (![A_49]: (k1_relat_1(k2_funct_1(A_49))=k2_relat_1(A_49) | ~v1_funct_1(k2_funct_1(A_49)) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.51  tff(c_167, plain, (![A_50]: (k1_relat_1(k2_funct_1(A_50))=k2_relat_1(A_50) | ~v1_funct_1(k2_funct_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_10, c_162])).
% 3.47/1.51  tff(c_171, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_8, c_167])).
% 3.47/1.51  tff(c_381, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_190])).
% 3.47/1.51  tff(c_383, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_381])).
% 3.47/1.51  tff(c_386, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_171, c_383])).
% 3.47/1.51  tff(c_388, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_386])).
% 3.47/1.51  tff(c_391, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_388])).
% 3.47/1.51  tff(c_394, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_382, c_44, c_391])).
% 3.47/1.51  tff(c_398, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_394])).
% 3.47/1.51  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_398])).
% 3.47/1.51  tff(c_404, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_381])).
% 3.47/1.51  tff(c_203, plain, (![A_55, D_56]: (k1_funct_1(k2_funct_1(A_55), k1_funct_1(A_55, D_56))=D_56 | ~r2_hidden(D_56, k1_relat_1(A_55)) | ~v1_funct_1(k2_funct_1(A_55)) | ~v1_relat_1(k2_funct_1(A_55)) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.51  tff(c_224, plain, (k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_203])).
% 3.47/1.51  tff(c_411, plain, (k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_404, c_224])).
% 3.47/1.51  tff(c_412, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_411])).
% 3.47/1.51  tff(c_415, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_412])).
% 3.47/1.51  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_415])).
% 3.47/1.51  tff(c_421, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_411])).
% 3.47/1.51  tff(c_4, plain, (![A_4]: (k7_relat_1(A_4, k1_relat_1(A_4))=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.51  tff(c_62, plain, (![B_32, A_33]: (r1_tarski(k2_relat_1(k7_relat_1(B_32, A_33)), k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.51  tff(c_65, plain, (![A_4]: (r1_tarski(k2_relat_1(A_4), k2_relat_1(A_4)) | ~v1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 3.47/1.51  tff(c_172, plain, (![A_51]: (k1_relat_1(k2_funct_1(A_51))=k2_relat_1(A_51) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_8, c_167])).
% 3.47/1.51  tff(c_2, plain, (![A_1, B_3]: (k1_relat_1(k5_relat_1(A_1, B_3))=k1_relat_1(A_1) | ~r1_tarski(k2_relat_1(A_1), k1_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.51  tff(c_286, plain, (![A_61, A_62]: (k1_relat_1(k5_relat_1(A_61, k2_funct_1(A_62)))=k1_relat_1(A_61) | ~r1_tarski(k2_relat_1(A_61), k2_relat_1(A_62)) | ~v1_relat_1(k2_funct_1(A_62)) | ~v1_relat_1(A_61) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2])).
% 3.47/1.51  tff(c_301, plain, (![A_66]: (k1_relat_1(k5_relat_1(A_66, k2_funct_1(A_66)))=k1_relat_1(A_66) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_65, c_286])).
% 3.47/1.51  tff(c_12, plain, (![C_11, B_9, A_8]: (k1_funct_1(k5_relat_1(C_11, B_9), A_8)=k1_funct_1(B_9, k1_funct_1(C_11, A_8)) | ~r2_hidden(A_8, k1_relat_1(k5_relat_1(C_11, B_9))) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.47/1.51  tff(c_663, plain, (![A_86, A_87]: (k1_funct_1(k5_relat_1(A_86, k2_funct_1(A_86)), A_87)=k1_funct_1(k2_funct_1(A_86), k1_funct_1(A_86, A_87)) | ~r2_hidden(A_87, k1_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86) | ~v1_funct_1(k2_funct_1(A_86)) | ~v1_relat_1(k2_funct_1(A_86)) | ~v1_relat_1(k2_funct_1(A_86)) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_301, c_12])).
% 3.47/1.51  tff(c_155, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.47/1.51  tff(c_691, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_663, c_155])).
% 3.47/1.51  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_382, c_382, c_421, c_50, c_48, c_44, c_156, c_691])).
% 3.47/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.51  
% 3.47/1.51  Inference rules
% 3.47/1.51  ----------------------
% 3.47/1.51  #Ref     : 0
% 3.47/1.51  #Sup     : 165
% 3.47/1.51  #Fact    : 0
% 3.47/1.51  #Define  : 0
% 3.47/1.51  #Split   : 6
% 3.47/1.51  #Chain   : 0
% 3.47/1.51  #Close   : 0
% 3.47/1.51  
% 3.47/1.51  Ordering : KBO
% 3.47/1.51  
% 3.47/1.51  Simplification rules
% 3.47/1.51  ----------------------
% 3.47/1.51  #Subsume      : 11
% 3.47/1.51  #Demod        : 53
% 3.47/1.51  #Tautology    : 51
% 3.47/1.51  #SimpNegUnit  : 0
% 3.47/1.51  #BackRed      : 0
% 3.47/1.51  
% 3.47/1.51  #Partial instantiations: 0
% 3.47/1.51  #Strategies tried      : 1
% 3.47/1.51  
% 3.47/1.51  Timing (in seconds)
% 3.47/1.51  ----------------------
% 3.47/1.51  Preprocessing        : 0.33
% 3.47/1.51  Parsing              : 0.17
% 3.47/1.51  CNF conversion       : 0.02
% 3.47/1.51  Main loop            : 0.41
% 3.47/1.51  Inferencing          : 0.16
% 3.47/1.51  Reduction            : 0.11
% 3.47/1.51  Demodulation         : 0.08
% 3.47/1.51  BG Simplification    : 0.03
% 3.47/1.51  Subsumption          : 0.08
% 3.47/1.51  Abstraction          : 0.03
% 3.47/1.51  MUC search           : 0.00
% 3.47/1.51  Cooper               : 0.00
% 3.47/1.51  Total                : 0.77
% 3.47/1.51  Index Insertion      : 0.00
% 3.47/1.51  Index Deletion       : 0.00
% 3.47/1.51  Index Matching       : 0.00
% 3.47/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
