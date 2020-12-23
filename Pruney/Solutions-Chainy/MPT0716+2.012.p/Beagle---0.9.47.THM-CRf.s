%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 156 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 467 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden('#skF_1'(A_30,B_31),B_31)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_51,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_149,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_55,'#skF_5')
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_59,c_135])).

tff(c_391,plain,(
    ! [A_97,C_98,B_99] :
      ( r2_hidden(A_97,k1_relat_1(C_98))
      | ~ r2_hidden(A_97,k1_relat_1(k5_relat_1(C_98,B_99)))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98)
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_394,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_55,'#skF_5')
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_149,c_391])).

tff(c_408,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_100,'#skF_5')
      | r1_tarski(A_100,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_30,c_28,c_394])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_417,plain,(
    ! [A_102] :
      ( ~ r1_tarski(A_102,'#skF_5')
      | r1_tarski(A_102,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_408,c_4])).

tff(c_36,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_115,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_433,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_417,c_115])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_433])).

tff(c_448,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( k10_relat_1(A_12,k1_relat_1(B_14)) = k1_relat_1(k5_relat_1(A_12,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k9_relat_1(C_11,A_9),k9_relat_1(C_11,B_10))
      | ~ r1_tarski(A_9,B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k9_relat_1(B_40,k10_relat_1(B_40,A_41)),A_41)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_488,plain,(
    ! [A_106,A_107,B_108] :
      ( r1_tarski(A_106,A_107)
      | ~ r1_tarski(A_106,k9_relat_1(B_108,k10_relat_1(B_108,A_107)))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_540,plain,(
    ! [C_115,A_116,A_117] :
      ( r1_tarski(k9_relat_1(C_115,A_116),A_117)
      | ~ v1_funct_1(C_115)
      | ~ r1_tarski(A_116,k10_relat_1(C_115,A_117))
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_10,c_488])).

tff(c_447,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_463,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_551,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_540,c_463])).

tff(c_561,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_551])).

tff(c_566,plain,
    ( ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_561])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_59,c_566])).

tff(c_571,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_618,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_571,c_32])).

tff(c_570,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_34,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_700,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_571,c_34])).

tff(c_824,plain,(
    ! [A_139,C_140,B_141] :
      ( r1_tarski(A_139,k10_relat_1(C_140,B_141))
      | ~ r1_tarski(k9_relat_1(C_140,A_139),B_141)
      | ~ r1_tarski(A_139,k1_relat_1(C_140))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_833,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_700,c_824])).

tff(c_868,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_570,c_833])).

tff(c_892,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_868])).

tff(c_902,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_892])).

tff(c_904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_902])).

tff(c_906,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_910,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_906,c_38])).

tff(c_905,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_942,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_906,c_40])).

tff(c_1346,plain,(
    ! [A_207,C_208,B_209] :
      ( r1_tarski(A_207,k10_relat_1(C_208,B_209))
      | ~ r1_tarski(k9_relat_1(C_208,A_207),B_209)
      | ~ r1_tarski(A_207,k1_relat_1(C_208))
      | ~ v1_funct_1(C_208)
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1370,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_1346])).

tff(c_1393,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_905,c_1370])).

tff(c_1412,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1393])).

tff(c_1421,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1412])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_1421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  
% 3.85/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.85/1.67  
% 3.85/1.67  %Foreground sorts:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Background operators:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Foreground operators:
% 3.85/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.85/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.85/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.67  
% 3.85/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.85/1.68  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 3.85/1.68  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.85/1.68  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.85/1.68  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.85/1.68  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.85/1.68  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.85/1.68  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.85/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.68  tff(c_44, plain, (![A_30, B_31]: (~r2_hidden('#skF_1'(A_30, B_31), B_31) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.68  tff(c_49, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_44])).
% 3.85/1.68  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_42, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_59, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_42])).
% 3.85/1.68  tff(c_51, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.68  tff(c_71, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_1'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_51])).
% 3.85/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.68  tff(c_135, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_71, c_2])).
% 3.85/1.68  tff(c_149, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_55, '#skF_5') | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_59, c_135])).
% 3.85/1.68  tff(c_391, plain, (![A_97, C_98, B_99]: (r2_hidden(A_97, k1_relat_1(C_98)) | ~r2_hidden(A_97, k1_relat_1(k5_relat_1(C_98, B_99))) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.85/1.68  tff(c_394, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_55, '#skF_5') | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_149, c_391])).
% 3.85/1.68  tff(c_408, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101), k1_relat_1('#skF_2')) | ~r1_tarski(A_100, '#skF_5') | r1_tarski(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_30, c_28, c_394])).
% 3.85/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.68  tff(c_417, plain, (![A_102]: (~r1_tarski(A_102, '#skF_5') | r1_tarski(A_102, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_408, c_4])).
% 3.85/1.68  tff(c_36, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_115, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.85/1.68  tff(c_433, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_417, c_115])).
% 3.85/1.68  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_433])).
% 3.85/1.68  tff(c_448, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.85/1.68  tff(c_12, plain, (![A_12, B_14]: (k10_relat_1(A_12, k1_relat_1(B_14))=k1_relat_1(k5_relat_1(A_12, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.68  tff(c_10, plain, (![C_11, A_9, B_10]: (r1_tarski(k9_relat_1(C_11, A_9), k9_relat_1(C_11, B_10)) | ~r1_tarski(A_9, B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.68  tff(c_67, plain, (![B_40, A_41]: (r1_tarski(k9_relat_1(B_40, k10_relat_1(B_40, A_41)), A_41) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.85/1.68  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.68  tff(c_488, plain, (![A_106, A_107, B_108]: (r1_tarski(A_106, A_107) | ~r1_tarski(A_106, k9_relat_1(B_108, k10_relat_1(B_108, A_107))) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_67, c_8])).
% 3.85/1.68  tff(c_540, plain, (![C_115, A_116, A_117]: (r1_tarski(k9_relat_1(C_115, A_116), A_117) | ~v1_funct_1(C_115) | ~r1_tarski(A_116, k10_relat_1(C_115, A_117)) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_10, c_488])).
% 3.85/1.68  tff(c_447, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.85/1.68  tff(c_463, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_447])).
% 3.85/1.68  tff(c_551, plain, (~v1_funct_1('#skF_2') | ~r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_540, c_463])).
% 3.85/1.68  tff(c_561, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_551])).
% 3.85/1.68  tff(c_566, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_561])).
% 3.85/1.68  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_59, c_566])).
% 3.85/1.68  tff(c_571, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_447])).
% 3.85/1.68  tff(c_32, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_618, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_571, c_32])).
% 3.85/1.68  tff(c_570, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_447])).
% 3.85/1.68  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_700, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_571, c_34])).
% 3.85/1.68  tff(c_824, plain, (![A_139, C_140, B_141]: (r1_tarski(A_139, k10_relat_1(C_140, B_141)) | ~r1_tarski(k9_relat_1(C_140, A_139), B_141) | ~r1_tarski(A_139, k1_relat_1(C_140)) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.85/1.68  tff(c_833, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_700, c_824])).
% 3.85/1.68  tff(c_868, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_570, c_833])).
% 3.85/1.68  tff(c_892, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_868])).
% 3.85/1.68  tff(c_902, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_892])).
% 3.85/1.68  tff(c_904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_618, c_902])).
% 3.85/1.68  tff(c_906, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_42])).
% 3.85/1.68  tff(c_38, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_910, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_906, c_38])).
% 3.85/1.68  tff(c_905, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 3.85/1.68  tff(c_40, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.68  tff(c_942, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_906, c_40])).
% 3.85/1.68  tff(c_1346, plain, (![A_207, C_208, B_209]: (r1_tarski(A_207, k10_relat_1(C_208, B_209)) | ~r1_tarski(k9_relat_1(C_208, A_207), B_209) | ~r1_tarski(A_207, k1_relat_1(C_208)) | ~v1_funct_1(C_208) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.85/1.68  tff(c_1370, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_942, c_1346])).
% 3.85/1.68  tff(c_1393, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_905, c_1370])).
% 3.85/1.68  tff(c_1412, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1393])).
% 3.85/1.68  tff(c_1421, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1412])).
% 3.85/1.68  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_910, c_1421])).
% 3.85/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  Inference rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Ref     : 0
% 3.85/1.68  #Sup     : 345
% 3.85/1.68  #Fact    : 0
% 3.85/1.68  #Define  : 0
% 3.85/1.68  #Split   : 8
% 3.85/1.68  #Chain   : 0
% 3.85/1.68  #Close   : 0
% 3.85/1.68  
% 3.85/1.68  Ordering : KBO
% 3.85/1.68  
% 3.85/1.68  Simplification rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Subsume      : 82
% 3.85/1.68  #Demod        : 66
% 3.85/1.68  #Tautology    : 33
% 3.85/1.68  #SimpNegUnit  : 6
% 3.85/1.68  #BackRed      : 0
% 3.85/1.68  
% 3.85/1.68  #Partial instantiations: 0
% 3.85/1.68  #Strategies tried      : 1
% 3.85/1.68  
% 3.85/1.68  Timing (in seconds)
% 3.85/1.68  ----------------------
% 4.06/1.69  Preprocessing        : 0.34
% 4.06/1.69  Parsing              : 0.18
% 4.06/1.69  CNF conversion       : 0.03
% 4.06/1.69  Main loop            : 0.55
% 4.06/1.69  Inferencing          : 0.18
% 4.06/1.69  Reduction            : 0.15
% 4.06/1.69  Demodulation         : 0.11
% 4.06/1.69  BG Simplification    : 0.03
% 4.06/1.69  Subsumption          : 0.15
% 4.06/1.69  Abstraction          : 0.03
% 4.06/1.69  MUC search           : 0.00
% 4.06/1.69  Cooper               : 0.00
% 4.06/1.69  Total                : 0.93
% 4.06/1.69  Index Insertion      : 0.00
% 4.06/1.69  Index Deletion       : 0.00
% 4.06/1.69  Index Matching       : 0.00
% 4.06/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
