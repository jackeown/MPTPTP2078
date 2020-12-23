%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 198 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 775 expanded)
%              Number of equality atoms :   26 ( 194 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_98,plain,(
    ! [A_40,D_41] :
      ( k1_funct_1(k2_funct_1(A_40),k1_funct_1(A_40,D_41)) = D_41
      | ~ r2_hidden(D_41,k1_relat_1(A_40))
      | ~ v1_funct_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_77,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_110,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_77])).

tff(c_120,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_110])).

tff(c_129,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_132,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_132])).

tff(c_137,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_141])).

tff(c_147,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_168,plain,(
    ! [A_47,D_48] :
      ( r2_hidden(k1_funct_1(A_47,D_48),k2_relat_1(A_47))
      | ~ r2_hidden(D_48,k1_relat_1(A_47))
      | ~ v1_funct_1(k2_funct_1(A_47))
      | ~ v1_relat_1(k2_funct_1(A_47))
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_174,plain,
    ( r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_168])).

tff(c_270,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_273,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_270])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_273])).

tff(c_279,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_42,plain,(
    ! [A_11,D_27] :
      ( r2_hidden(k1_funct_1(A_11,D_27),k2_relat_1(A_11))
      | ~ r2_hidden(D_27,k1_relat_1(A_11))
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    ! [A_28] :
      ( k1_relat_1(k2_funct_1(A_28)) = k2_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_278,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_350,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_353,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_350])).

tff(c_355,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_353])).

tff(c_360,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_355])).

tff(c_363,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_279,c_50,c_360])).

tff(c_366,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_366])).

tff(c_371,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_378,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_385,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_378])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_385])).

tff(c_391,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_45,B_46] :
      ( k1_relat_1(k5_relat_1(A_45,B_46)) = k1_relat_1(A_45)
      | ~ r1_tarski(k2_relat_1(A_45),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_258,plain,(
    ! [A_55,A_56] :
      ( k1_relat_1(k5_relat_1(A_55,k2_funct_1(A_56))) = k1_relat_1(A_55)
      | ~ r1_tarski(k2_relat_1(A_55),k2_relat_1(A_56))
      | ~ v1_relat_1(k2_funct_1(A_56))
      | ~ v1_relat_1(A_55)
      | ~ v2_funct_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_161])).

tff(c_269,plain,(
    ! [A_55] :
      ( k1_relat_1(k5_relat_1(A_55,k2_funct_1(A_55))) = k1_relat_1(A_55)
      | ~ v1_relat_1(k2_funct_1(A_55))
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_295,plain,(
    ! [C_58,B_59,A_60] :
      ( k1_funct_1(k5_relat_1(C_58,B_59),A_60) = k1_funct_1(B_59,k1_funct_1(C_58,A_60))
      | ~ r2_hidden(A_60,k1_relat_1(k5_relat_1(C_58,B_59)))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_697,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_269,c_295])).

tff(c_146,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_728,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_697,c_146])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_279,c_279,c_391,c_56,c_54,c_50,c_147,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.39/1.53  
% 3.39/1.53  %Foreground sorts:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Background operators:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Foreground operators:
% 3.39/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.39/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.39/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.39/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.39/1.53  
% 3.55/1.55  tff(f_116, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 3.55/1.55  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.55/1.55  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 3.55/1.55  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.55/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.55  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.55/1.55  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 3.55/1.55  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.55/1.55  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.55/1.55  tff(c_52, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.55/1.55  tff(c_12, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.55/1.55  tff(c_10, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.55/1.55  tff(c_50, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.55/1.55  tff(c_98, plain, (![A_40, D_41]: (k1_funct_1(k2_funct_1(A_40), k1_funct_1(A_40, D_41))=D_41 | ~r2_hidden(D_41, k1_relat_1(A_40)) | ~v1_funct_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.55  tff(c_48, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.55/1.55  tff(c_77, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_48])).
% 3.55/1.55  tff(c_110, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_98, c_77])).
% 3.55/1.55  tff(c_120, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_110])).
% 3.55/1.55  tff(c_129, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_120])).
% 3.55/1.55  tff(c_132, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_129])).
% 3.55/1.55  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_132])).
% 3.55/1.55  tff(c_137, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_120])).
% 3.55/1.55  tff(c_141, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_137])).
% 3.55/1.55  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_141])).
% 3.55/1.55  tff(c_147, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.55/1.55  tff(c_168, plain, (![A_47, D_48]: (r2_hidden(k1_funct_1(A_47, D_48), k2_relat_1(A_47)) | ~r2_hidden(D_48, k1_relat_1(A_47)) | ~v1_funct_1(k2_funct_1(A_47)) | ~v1_relat_1(k2_funct_1(A_47)) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.55  tff(c_174, plain, (r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_168])).
% 3.55/1.55  tff(c_270, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_174])).
% 3.55/1.55  tff(c_273, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_270])).
% 3.55/1.55  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_273])).
% 3.55/1.55  tff(c_279, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_174])).
% 3.55/1.55  tff(c_42, plain, (![A_11, D_27]: (r2_hidden(k1_funct_1(A_11, D_27), k2_relat_1(A_11)) | ~r2_hidden(D_27, k1_relat_1(A_11)) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.55  tff(c_46, plain, (![A_28]: (k1_relat_1(k2_funct_1(A_28))=k2_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.55/1.55  tff(c_278, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_174])).
% 3.55/1.55  tff(c_350, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_278])).
% 3.55/1.55  tff(c_353, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_46, c_350])).
% 3.55/1.55  tff(c_355, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_353])).
% 3.55/1.55  tff(c_360, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_355])).
% 3.55/1.55  tff(c_363, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_279, c_50, c_360])).
% 3.55/1.55  tff(c_366, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_363])).
% 3.55/1.55  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_366])).
% 3.55/1.55  tff(c_371, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_278])).
% 3.55/1.55  tff(c_378, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_371])).
% 3.55/1.55  tff(c_385, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_378])).
% 3.55/1.55  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_385])).
% 3.55/1.55  tff(c_391, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_371])).
% 3.55/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.55  tff(c_161, plain, (![A_45, B_46]: (k1_relat_1(k5_relat_1(A_45, B_46))=k1_relat_1(A_45) | ~r1_tarski(k2_relat_1(A_45), k1_relat_1(B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.55  tff(c_258, plain, (![A_55, A_56]: (k1_relat_1(k5_relat_1(A_55, k2_funct_1(A_56)))=k1_relat_1(A_55) | ~r1_tarski(k2_relat_1(A_55), k2_relat_1(A_56)) | ~v1_relat_1(k2_funct_1(A_56)) | ~v1_relat_1(A_55) | ~v2_funct_1(A_56) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_46, c_161])).
% 3.55/1.55  tff(c_269, plain, (![A_55]: (k1_relat_1(k5_relat_1(A_55, k2_funct_1(A_55)))=k1_relat_1(A_55) | ~v1_relat_1(k2_funct_1(A_55)) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_6, c_258])).
% 3.55/1.55  tff(c_295, plain, (![C_58, B_59, A_60]: (k1_funct_1(k5_relat_1(C_58, B_59), A_60)=k1_funct_1(B_59, k1_funct_1(C_58, A_60)) | ~r2_hidden(A_60, k1_relat_1(k5_relat_1(C_58, B_59))) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.55  tff(c_697, plain, (![A_86, A_87]: (k1_funct_1(k5_relat_1(A_86, k2_funct_1(A_86)), A_87)=k1_funct_1(k2_funct_1(A_86), k1_funct_1(A_86, A_87)) | ~r2_hidden(A_87, k1_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86) | ~v1_funct_1(k2_funct_1(A_86)) | ~v1_relat_1(k2_funct_1(A_86)) | ~v1_relat_1(k2_funct_1(A_86)) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_269, c_295])).
% 3.55/1.55  tff(c_146, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.55/1.55  tff(c_728, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_697, c_146])).
% 3.55/1.55  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_279, c_279, c_391, c_56, c_54, c_50, c_147, c_728])).
% 3.55/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.55  
% 3.55/1.55  Inference rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Ref     : 0
% 3.55/1.55  #Sup     : 166
% 3.55/1.55  #Fact    : 0
% 3.55/1.55  #Define  : 0
% 3.55/1.55  #Split   : 8
% 3.55/1.55  #Chain   : 0
% 3.55/1.55  #Close   : 0
% 3.55/1.55  
% 3.55/1.55  Ordering : KBO
% 3.55/1.55  
% 3.55/1.55  Simplification rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Subsume      : 5
% 3.55/1.55  #Demod        : 70
% 3.55/1.55  #Tautology    : 57
% 3.55/1.55  #SimpNegUnit  : 0
% 3.55/1.55  #BackRed      : 0
% 3.55/1.55  
% 3.55/1.55  #Partial instantiations: 0
% 3.55/1.55  #Strategies tried      : 1
% 3.55/1.55  
% 3.55/1.55  Timing (in seconds)
% 3.55/1.55  ----------------------
% 3.55/1.55  Preprocessing        : 0.34
% 3.55/1.55  Parsing              : 0.18
% 3.55/1.55  CNF conversion       : 0.03
% 3.55/1.55  Main loop            : 0.44
% 3.55/1.55  Inferencing          : 0.16
% 3.55/1.55  Reduction            : 0.12
% 3.55/1.55  Demodulation         : 0.09
% 3.55/1.55  BG Simplification    : 0.04
% 3.55/1.55  Subsumption          : 0.10
% 3.55/1.55  Abstraction          : 0.02
% 3.55/1.55  MUC search           : 0.00
% 3.55/1.55  Cooper               : 0.00
% 3.55/1.55  Total                : 0.82
% 3.55/1.55  Index Insertion      : 0.00
% 3.55/1.55  Index Deletion       : 0.00
% 3.55/1.55  Index Matching       : 0.00
% 3.55/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
