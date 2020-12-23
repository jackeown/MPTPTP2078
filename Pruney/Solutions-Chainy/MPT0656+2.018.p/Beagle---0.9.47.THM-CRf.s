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
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 658 expanded)
%              Number of leaves         :   27 ( 244 expanded)
%              Depth                    :   20
%              Number of atoms          :  270 (2003 expanded)
%              Number of equality atoms :   82 ( 710 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(c_34,plain,(
    k2_funct_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_16] :
      ( k1_relat_1(k6_relat_1(A_16)) = A_16
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_16] :
      ( k1_relat_1(k6_relat_1(A_16)) = A_16
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_56,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_132,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_34,A_16] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_16)) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_34)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_132])).

tff(c_143,plain,(
    ! [A_36,A_37] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_37)) = k6_relat_1(A_37)
      | ~ r1_tarski(A_37,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_197,plain,(
    ! [A_41] :
      ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k6_relat_1(A_41)) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,k1_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_143])).

tff(c_214,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2','#skF_3')) = k6_relat_1(k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_197])).

tff(c_221,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2','#skF_3')) = k5_relat_1('#skF_2','#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_214])).

tff(c_277,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_71,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_80,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_71])).

tff(c_38,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_89,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_3'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_89])).

tff(c_102,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_98])).

tff(c_30,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_120,plain,(
    ! [A_33] :
      ( k2_relat_1(k2_funct_1(A_33)) = k1_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1171,plain,(
    ! [A_71] :
      ( k5_relat_1(k2_funct_1(A_71),k6_relat_1(k1_relat_1(A_71))) = k2_funct_1(A_71)
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_6])).

tff(c_1195,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1171])).

tff(c_1206,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_1195])).

tff(c_1793,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_1796,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1793])).

tff(c_1800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1796])).

tff(c_1802,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_32,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k2_funct_1(A_22)) = k6_relat_1(k1_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_278,plain,(
    ! [A_45,B_46,C_47] :
      ( k5_relat_1(k5_relat_1(A_45,B_46),C_47) = k5_relat_1(A_45,k5_relat_1(B_46,C_47))
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2263,plain,(
    ! [A_85,C_86] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_85)),C_86) = k5_relat_1(A_85,k5_relat_1(k2_funct_1(A_85),C_86))
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(k2_funct_1(A_85))
      | ~ v1_relat_1(A_85)
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_278])).

tff(c_2515,plain,(
    ! [C_86] :
      ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_86)) = k5_relat_1(k5_relat_1('#skF_2','#skF_3'),C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2263])).

tff(c_2791,plain,(
    ! [C_87] :
      ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_87)) = k5_relat_1(k5_relat_1('#skF_2','#skF_3'),C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_48,c_1802,c_2515])).

tff(c_2842,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2'))) = k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2791])).

tff(c_2872,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_48,c_102,c_38,c_2842])).

tff(c_65,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_67,plain,(
    v1_funct_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_910,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k2_relat_1(B_63),k1_relat_1(A_64))
      | k1_relat_1(k5_relat_1(B_63,A_64)) != k1_relat_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_150,plain,(
    ! [A_36] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_36))) = k6_relat_1(A_36)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_36)),A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_6])).

tff(c_183,plain,(
    ! [A_39] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_39))) = k6_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_39)),A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_150])).

tff(c_186,plain,
    ( k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1('#skF_2')))) = k6_relat_1(k1_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_183])).

tff(c_187,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k5_relat_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_186])).

tff(c_427,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_918,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_2')) != k1_relat_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_910,c_427])).

tff(c_944,plain,(
    k1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_2')) != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_65,c_67,c_80,c_918])).

tff(c_2877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2872,c_944])).

tff(c_2878,plain,(
    k6_relat_1(k2_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k5_relat_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_2907,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2878,c_56])).

tff(c_2922,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2907])).

tff(c_2879,plain,(
    r1_tarski(k2_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_2927,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_2879])).

tff(c_2930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_2927])).

tff(c_2932,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_163,plain,(
    ! [A_36] :
      ( k5_relat_1(k6_relat_1(A_36),k5_relat_1('#skF_2','#skF_3')) = k6_relat_1(k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_143])).

tff(c_231,plain,(
    ! [A_43] :
      ( k5_relat_1(k6_relat_1(A_43),k5_relat_1('#skF_2','#skF_3')) = k5_relat_1('#skF_2','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_240,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2','#skF_3')) = k5_relat_1('#skF_2','#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_231])).

tff(c_3045,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2','#skF_3')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2932,c_240])).

tff(c_4,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2935,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2932,c_4])).

tff(c_2938,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_2935])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3018,plain,(
    ! [C_7] :
      ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2',C_7)) = k5_relat_1('#skF_2',C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2938,c_2])).

tff(c_3348,plain,(
    ! [C_97] :
      ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k5_relat_1('#skF_2',C_97)) = k5_relat_1('#skF_2',C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48,c_3018])).

tff(c_3388,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),k6_relat_1(k1_relat_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3348])).

tff(c_3415,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_3045,c_36,c_3388])).

tff(c_3420,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3415])).

tff(c_3423,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_3420])).

tff(c_3427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3423])).

tff(c_3429,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3415])).

tff(c_4054,plain,(
    ! [A_112] :
      ( k5_relat_1(k2_funct_1(A_112),k6_relat_1(k1_relat_1(A_112))) = k2_funct_1(A_112)
      | ~ v1_relat_1(k2_funct_1(A_112))
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_6])).

tff(c_4082,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4054])).

tff(c_4095,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_3429,c_4082])).

tff(c_2939,plain,(
    ! [A_88,B_89,C_90] :
      ( k5_relat_1(k5_relat_1(A_88,B_89),C_90) = k5_relat_1(A_88,k5_relat_1(B_89,C_90))
      | ~ v1_relat_1(C_90)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5528,plain,(
    ! [A_124,C_125] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_124)),C_125) = k5_relat_1(k2_funct_1(A_124),k5_relat_1(A_124,C_125))
      | ~ v1_relat_1(C_125)
      | ~ v1_relat_1(A_124)
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2939])).

tff(c_5712,plain,(
    ! [C_125] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),C_125) = k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_125))
      | ~ v1_relat_1(C_125)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5528])).

tff(c_5796,plain,(
    ! [C_126] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),C_126) = k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_126))
      | ~ v1_relat_1(C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_3429,c_48,c_5712])).

tff(c_3430,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(k2_relat_1(B_98),k1_relat_1(A_99))
      | k1_relat_1(k5_relat_1(B_98,A_99)) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3455,plain,(
    ! [A_99] :
      ( r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(A_99))
      | k1_relat_1(k5_relat_1('#skF_2',A_99)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3430])).

tff(c_3529,plain,(
    ! [A_101] :
      ( r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(A_101))
      | k1_relat_1(k5_relat_1('#skF_2',A_101)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3455])).

tff(c_3541,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_16)
      | k1_relat_1(k5_relat_1('#skF_2',k6_relat_1(A_16))) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3529])).

tff(c_3549,plain,(
    ! [A_102] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_102)
      | k1_relat_1(k5_relat_1('#skF_2',k6_relat_1(A_102))) != k1_relat_1('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_3541])).

tff(c_3564,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_3549])).

tff(c_3570,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3564,c_4])).

tff(c_3573,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3570])).

tff(c_5834,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_3573])).

tff(c_5913,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4095,c_5834])).

tff(c_5915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_5913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.22  
% 6.09/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.22  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.09/2.22  
% 6.09/2.22  %Foreground sorts:
% 6.09/2.22  
% 6.09/2.22  
% 6.09/2.22  %Background operators:
% 6.09/2.22  
% 6.09/2.22  
% 6.09/2.22  %Foreground operators:
% 6.09/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.09/2.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.09/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.09/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.09/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.09/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.09/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.09/2.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.09/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.09/2.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.09/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.09/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.09/2.22  
% 6.09/2.24  tff(f_121, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.09/2.24  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.09/2.24  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.09/2.24  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 6.09/2.24  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 6.09/2.24  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 6.09/2.24  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.09/2.24  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.09/2.24  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.09/2.24  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 6.09/2.24  tff(c_34, plain, (k2_funct_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_40, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_10, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.09/2.24  tff(c_36, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.09/2.24  tff(c_14, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.09/2.24  tff(c_24, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16 | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.09/2.24  tff(c_50, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16 | ~v1_relat_1(k6_relat_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 6.09/2.24  tff(c_56, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 6.09/2.24  tff(c_132, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.09/2.24  tff(c_138, plain, (![A_34, A_16]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_16))=k6_relat_1(A_16) | ~r1_tarski(A_16, A_34) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_132])).
% 6.09/2.24  tff(c_143, plain, (![A_36, A_37]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_37))=k6_relat_1(A_37) | ~r1_tarski(A_37, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_138])).
% 6.09/2.24  tff(c_197, plain, (![A_41]: (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k6_relat_1(A_41))=k6_relat_1(A_41) | ~r1_tarski(A_41, k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_143])).
% 6.09/2.24  tff(c_214, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))=k6_relat_1(k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_197])).
% 6.09/2.24  tff(c_221, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))=k5_relat_1('#skF_2', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_214])).
% 6.09/2.24  tff(c_277, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_221])).
% 6.09/2.24  tff(c_71, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 6.09/2.24  tff(c_80, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_71])).
% 6.09/2.24  tff(c_38, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.09/2.24  tff(c_89, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.09/2.24  tff(c_98, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_3')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_89])).
% 6.09/2.24  tff(c_102, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_98])).
% 6.09/2.24  tff(c_30, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.09/2.24  tff(c_120, plain, (![A_33]: (k2_relat_1(k2_funct_1(A_33))=k1_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.09/2.24  tff(c_6, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.09/2.24  tff(c_1171, plain, (![A_71]: (k5_relat_1(k2_funct_1(A_71), k6_relat_1(k1_relat_1(A_71)))=k2_funct_1(A_71) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_120, c_6])).
% 6.09/2.24  tff(c_1195, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1171])).
% 6.09/2.24  tff(c_1206, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_1195])).
% 6.09/2.24  tff(c_1793, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1206])).
% 6.09/2.24  tff(c_1796, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1793])).
% 6.09/2.24  tff(c_1800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1796])).
% 6.09/2.24  tff(c_1802, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1206])).
% 6.09/2.24  tff(c_32, plain, (![A_22]: (k5_relat_1(A_22, k2_funct_1(A_22))=k6_relat_1(k1_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.09/2.24  tff(c_278, plain, (![A_45, B_46, C_47]: (k5_relat_1(k5_relat_1(A_45, B_46), C_47)=k5_relat_1(A_45, k5_relat_1(B_46, C_47)) | ~v1_relat_1(C_47) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.09/2.24  tff(c_2263, plain, (![A_85, C_86]: (k5_relat_1(k6_relat_1(k1_relat_1(A_85)), C_86)=k5_relat_1(A_85, k5_relat_1(k2_funct_1(A_85), C_86)) | ~v1_relat_1(C_86) | ~v1_relat_1(k2_funct_1(A_85)) | ~v1_relat_1(A_85) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_32, c_278])).
% 6.09/2.24  tff(c_2515, plain, (![C_86]: (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_86))=k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2263])).
% 6.09/2.24  tff(c_2791, plain, (![C_87]: (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_87))=k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), C_87) | ~v1_relat_1(C_87))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_48, c_1802, c_2515])).
% 6.09/2.24  tff(c_2842, plain, (k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2')))=k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2791])).
% 6.09/2.24  tff(c_2872, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_48, c_102, c_38, c_2842])).
% 6.09/2.24  tff(c_65, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_12])).
% 6.09/2.24  tff(c_67, plain, (v1_funct_1(k5_relat_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_14])).
% 6.09/2.24  tff(c_910, plain, (![B_63, A_64]: (r1_tarski(k2_relat_1(B_63), k1_relat_1(A_64)) | k1_relat_1(k5_relat_1(B_63, A_64))!=k1_relat_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.09/2.24  tff(c_150, plain, (![A_36]: (k6_relat_1(k2_relat_1(k6_relat_1(A_36)))=k6_relat_1(A_36) | ~v1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(k2_relat_1(k6_relat_1(A_36)), A_36))), inference(superposition, [status(thm), theory('equality')], [c_143, c_6])).
% 6.09/2.24  tff(c_183, plain, (![A_39]: (k6_relat_1(k2_relat_1(k6_relat_1(A_39)))=k6_relat_1(A_39) | ~r1_tarski(k2_relat_1(k6_relat_1(A_39)), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_150])).
% 6.09/2.24  tff(c_186, plain, (k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1('#skF_2'))))=k6_relat_1(k1_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_183])).
% 6.09/2.24  tff(c_187, plain, (k6_relat_1(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k5_relat_1('#skF_2', '#skF_3') | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_186])).
% 6.09/2.24  tff(c_427, plain, (~r1_tarski(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_187])).
% 6.09/2.24  tff(c_918, plain, (k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_2'))!=k1_relat_1(k5_relat_1('#skF_2', '#skF_3')) | ~v1_funct_1(k5_relat_1('#skF_2', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_910, c_427])).
% 6.09/2.24  tff(c_944, plain, (k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_2'))!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_65, c_67, c_80, c_918])).
% 6.09/2.24  tff(c_2877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2872, c_944])).
% 6.09/2.24  tff(c_2878, plain, (k6_relat_1(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k5_relat_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_187])).
% 6.09/2.24  tff(c_2907, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2878, c_56])).
% 6.09/2.24  tff(c_2922, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2907])).
% 6.09/2.24  tff(c_2879, plain, (r1_tarski(k2_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_187])).
% 6.09/2.24  tff(c_2927, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_2879])).
% 6.09/2.24  tff(c_2930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_2927])).
% 6.09/2.24  tff(c_2932, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_221])).
% 6.09/2.24  tff(c_163, plain, (![A_36]: (k5_relat_1(k6_relat_1(A_36), k5_relat_1('#skF_2', '#skF_3'))=k6_relat_1(k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), A_36))), inference(superposition, [status(thm), theory('equality')], [c_36, c_143])).
% 6.09/2.24  tff(c_231, plain, (![A_43]: (k5_relat_1(k6_relat_1(A_43), k5_relat_1('#skF_2', '#skF_3'))=k5_relat_1('#skF_2', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_163])).
% 6.09/2.24  tff(c_240, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))=k5_relat_1('#skF_2', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_231])).
% 6.09/2.24  tff(c_3045, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2932, c_240])).
% 6.09/2.24  tff(c_4, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.09/2.24  tff(c_2935, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2932, c_4])).
% 6.09/2.24  tff(c_2938, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_2935])).
% 6.09/2.24  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.09/2.24  tff(c_3018, plain, (![C_7]: (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', C_7))=k5_relat_1('#skF_2', C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2938, c_2])).
% 6.09/2.24  tff(c_3348, plain, (![C_97]: (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k5_relat_1('#skF_2', C_97))=k5_relat_1('#skF_2', C_97) | ~v1_relat_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48, c_3018])).
% 6.09/2.24  tff(c_3388, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), k6_relat_1(k1_relat_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_3348])).
% 6.09/2.24  tff(c_3415, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_3045, c_36, c_3388])).
% 6.09/2.24  tff(c_3420, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3415])).
% 6.09/2.24  tff(c_3423, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_3420])).
% 6.09/2.24  tff(c_3427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3423])).
% 6.09/2.24  tff(c_3429, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3415])).
% 6.09/2.24  tff(c_4054, plain, (![A_112]: (k5_relat_1(k2_funct_1(A_112), k6_relat_1(k1_relat_1(A_112)))=k2_funct_1(A_112) | ~v1_relat_1(k2_funct_1(A_112)) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_120, c_6])).
% 6.09/2.24  tff(c_4082, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_4054])).
% 6.09/2.24  tff(c_4095, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_3429, c_4082])).
% 6.09/2.24  tff(c_2939, plain, (![A_88, B_89, C_90]: (k5_relat_1(k5_relat_1(A_88, B_89), C_90)=k5_relat_1(A_88, k5_relat_1(B_89, C_90)) | ~v1_relat_1(C_90) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.09/2.24  tff(c_5528, plain, (![A_124, C_125]: (k5_relat_1(k6_relat_1(k2_relat_1(A_124)), C_125)=k5_relat_1(k2_funct_1(A_124), k5_relat_1(A_124, C_125)) | ~v1_relat_1(C_125) | ~v1_relat_1(A_124) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2939])).
% 6.09/2.24  tff(c_5712, plain, (![C_125]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), C_125)=k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_125)) | ~v1_relat_1(C_125) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5528])).
% 6.09/2.24  tff(c_5796, plain, (![C_126]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), C_126)=k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_126)) | ~v1_relat_1(C_126))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_3429, c_48, c_5712])).
% 6.09/2.24  tff(c_3430, plain, (![B_98, A_99]: (r1_tarski(k2_relat_1(B_98), k1_relat_1(A_99)) | k1_relat_1(k5_relat_1(B_98, A_99))!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.09/2.24  tff(c_3455, plain, (![A_99]: (r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(A_99)) | k1_relat_1(k5_relat_1('#skF_2', A_99))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3430])).
% 6.09/2.24  tff(c_3529, plain, (![A_101]: (r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(A_101)) | k1_relat_1(k5_relat_1('#skF_2', A_101))!=k1_relat_1('#skF_2') | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3455])).
% 6.09/2.24  tff(c_3541, plain, (![A_16]: (r1_tarski(k1_relat_1('#skF_3'), A_16) | k1_relat_1(k5_relat_1('#skF_2', k6_relat_1(A_16)))!=k1_relat_1('#skF_2') | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3529])).
% 6.09/2.24  tff(c_3549, plain, (![A_102]: (r1_tarski(k1_relat_1('#skF_3'), A_102) | k1_relat_1(k5_relat_1('#skF_2', k6_relat_1(A_102)))!=k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_3541])).
% 6.09/2.24  tff(c_3564, plain, (r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_3549])).
% 6.09/2.24  tff(c_3570, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3564, c_4])).
% 6.09/2.24  tff(c_3573, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3570])).
% 6.09/2.24  tff(c_5834, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5796, c_3573])).
% 6.09/2.24  tff(c_5913, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4095, c_5834])).
% 6.09/2.24  tff(c_5915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_5913])).
% 6.09/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.24  
% 6.09/2.24  Inference rules
% 6.09/2.24  ----------------------
% 6.09/2.24  #Ref     : 0
% 6.09/2.24  #Sup     : 1247
% 6.09/2.24  #Fact    : 0
% 6.09/2.24  #Define  : 0
% 6.09/2.24  #Split   : 15
% 6.09/2.24  #Chain   : 0
% 6.09/2.24  #Close   : 0
% 6.09/2.24  
% 6.09/2.24  Ordering : KBO
% 6.09/2.24  
% 6.09/2.24  Simplification rules
% 6.09/2.24  ----------------------
% 6.09/2.24  #Subsume      : 52
% 6.09/2.24  #Demod        : 2124
% 6.09/2.24  #Tautology    : 505
% 6.09/2.24  #SimpNegUnit  : 9
% 6.09/2.24  #BackRed      : 28
% 6.09/2.24  
% 6.09/2.24  #Partial instantiations: 0
% 6.09/2.24  #Strategies tried      : 1
% 6.09/2.24  
% 6.09/2.24  Timing (in seconds)
% 6.09/2.24  ----------------------
% 6.09/2.24  Preprocessing        : 0.32
% 6.09/2.24  Parsing              : 0.16
% 6.09/2.24  CNF conversion       : 0.02
% 6.09/2.24  Main loop            : 1.12
% 6.09/2.24  Inferencing          : 0.36
% 6.09/2.24  Reduction            : 0.44
% 6.09/2.24  Demodulation         : 0.33
% 6.09/2.24  BG Simplification    : 0.05
% 6.09/2.24  Subsumption          : 0.19
% 6.09/2.24  Abstraction          : 0.07
% 6.09/2.24  MUC search           : 0.00
% 6.09/2.24  Cooper               : 0.00
% 6.09/2.24  Total                : 1.48
% 6.09/2.24  Index Insertion      : 0.00
% 6.09/2.24  Index Deletion       : 0.00
% 6.09/2.24  Index Matching       : 0.00
% 6.09/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
