%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 8.83s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 159 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 466 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
            <=> ( r2_hidden(A,k1_relat_1(C))
                & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_67,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_91,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_91,c_46])).

tff(c_30,plain,(
    ! [A_33,B_35] :
      ( k10_relat_1(A_33,k1_relat_1(B_35)) = k1_relat_1(k5_relat_1(A_33,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_165,plain,(
    ! [A_88,C_89] :
      ( r2_hidden(k4_tarski(A_88,k1_funct_1(C_89,A_88)),C_89)
      | ~ r2_hidden(A_88,k1_relat_1(C_89))
      | ~ v1_funct_1(C_89)
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_182,plain,(
    ! [C_90,A_91] :
      ( r2_hidden(k1_funct_1(C_90,A_91),k2_relat_1(C_90))
      | ~ r2_hidden(A_91,k1_relat_1(C_90))
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_165,c_10])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [C_90,A_91,B_2] :
      ( r2_hidden(k1_funct_1(C_90,A_91),B_2)
      | ~ r1_tarski(k2_relat_1(C_90),B_2)
      | ~ r2_hidden(A_91,k1_relat_1(C_90))
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_32,plain,(
    ! [A_36,C_38] :
      ( r2_hidden(k4_tarski(A_36,k1_funct_1(C_38,A_36)),C_38)
      | ~ r2_hidden(A_36,k1_relat_1(C_38))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_707,plain,(
    ! [A_152,C_153,B_154,D_155] :
      ( r2_hidden(A_152,k10_relat_1(C_153,B_154))
      | ~ r2_hidden(D_155,B_154)
      | ~ r2_hidden(k4_tarski(A_152,D_155),C_153)
      | ~ r2_hidden(D_155,k2_relat_1(C_153))
      | ~ v1_relat_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_915,plain,(
    ! [A_164,C_165] :
      ( r2_hidden(A_164,k10_relat_1(C_165,k1_relat_1('#skF_8')))
      | ~ r2_hidden(k4_tarski(A_164,k1_funct_1('#skF_9','#skF_7')),C_165)
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1(C_165))
      | ~ v1_relat_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_91,c_707])).

tff(c_927,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_915])).

tff(c_936,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_67,c_927])).

tff(c_938,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_936])).

tff(c_941,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_185,c_938])).

tff(c_951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_67,c_64,c_941])).

tff(c_952,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_936])).

tff(c_972,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_952])).

tff(c_982,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_972])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_982])).

tff(c_985,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_986,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1078,plain,(
    ! [A_198,B_199,C_200] :
      ( r2_hidden(k4_tarski(A_198,'#skF_6'(A_198,B_199,C_200)),C_200)
      | ~ r2_hidden(A_198,k10_relat_1(C_200,B_199))
      | ~ v1_relat_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [C_38,A_36,B_37] :
      ( k1_funct_1(C_38,A_36) = B_37
      | ~ r2_hidden(k4_tarski(A_36,B_37),C_38)
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1348,plain,(
    ! [C_229,A_230,B_231] :
      ( k1_funct_1(C_229,A_230) = '#skF_6'(A_230,B_231,C_229)
      | ~ v1_funct_1(C_229)
      | ~ r2_hidden(A_230,k10_relat_1(C_229,B_231))
      | ~ v1_relat_1(C_229) ) ),
    inference(resolution,[status(thm)],[c_1078,c_34])).

tff(c_8304,plain,(
    ! [A_761,B_762,A_763] :
      ( '#skF_6'(A_761,k1_relat_1(B_762),A_763) = k1_funct_1(A_763,A_761)
      | ~ v1_funct_1(A_763)
      | ~ r2_hidden(A_761,k1_relat_1(k5_relat_1(A_763,B_762)))
      | ~ v1_relat_1(A_763)
      | ~ v1_relat_1(B_762)
      | ~ v1_relat_1(A_763) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1348])).

tff(c_8506,plain,
    ( '#skF_6'('#skF_7',k1_relat_1('#skF_8'),'#skF_9') = k1_funct_1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_985,c_8304])).

tff(c_8569,plain,(
    '#skF_6'('#skF_7',k1_relat_1('#skF_8'),'#skF_9') = k1_funct_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_38,c_8506])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_6'(A_25,B_26,C_27),B_26)
      | ~ r2_hidden(A_25,k10_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8602,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8569,c_22])).

tff(c_8624,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8602])).

tff(c_8625,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_986,c_8624])).

tff(c_8629,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8625])).

tff(c_8632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_985,c_8629])).

tff(c_8634,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8657,plain,(
    ! [A_769,B_770] :
      ( k10_relat_1(A_769,k1_relat_1(B_770)) = k1_relat_1(k5_relat_1(A_769,B_770))
      | ~ v1_relat_1(B_770)
      | ~ v1_relat_1(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k10_relat_1(B_32,A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8710,plain,(
    ! [A_789,B_790] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_789,B_790)),k1_relat_1(A_789))
      | ~ v1_relat_1(A_789)
      | ~ v1_relat_1(B_790)
      | ~ v1_relat_1(A_789) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8657,c_28])).

tff(c_8633,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8636,plain,(
    ! [C_764,B_765,A_766] :
      ( r2_hidden(C_764,B_765)
      | ~ r2_hidden(C_764,A_766)
      | ~ r1_tarski(A_766,B_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8644,plain,(
    ! [B_765] :
      ( r2_hidden('#skF_7',B_765)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_9','#skF_8')),B_765) ) ),
    inference(resolution,[status(thm)],[c_8633,c_8636])).

tff(c_8716,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8710,c_8644])).

tff(c_8720,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_8716])).

tff(c_8722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8634,c_8720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.83/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.83/2.99  
% 8.83/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.83/2.99  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.83/2.99  
% 8.83/2.99  %Foreground sorts:
% 8.83/2.99  
% 8.83/2.99  
% 8.83/2.99  %Background operators:
% 8.83/2.99  
% 8.83/2.99  
% 8.83/2.99  %Foreground operators:
% 8.83/2.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.83/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.83/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.83/2.99  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.83/2.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.83/2.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.83/2.99  tff('#skF_7', type, '#skF_7': $i).
% 8.83/2.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.83/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.83/2.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.83/2.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.83/2.99  tff('#skF_9', type, '#skF_9': $i).
% 8.83/2.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.83/2.99  tff('#skF_8', type, '#skF_8': $i).
% 8.83/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.83/2.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.83/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.83/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.83/2.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.83/2.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.83/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.83/2.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.83/2.99  
% 8.83/3.00  tff(f_88, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 8.83/3.00  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 8.83/3.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.83/3.00  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 8.83/3.00  tff(f_40, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.83/3.00  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 8.83/3.00  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 8.83/3.00  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_56, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_67, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.83/3.00  tff(c_52, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_91, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 8.83/3.00  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_119, plain, (~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_91, c_46])).
% 8.83/3.00  tff(c_30, plain, (![A_33, B_35]: (k10_relat_1(A_33, k1_relat_1(B_35))=k1_relat_1(k5_relat_1(A_33, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.83/3.00  tff(c_38, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.83/3.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.83/3.00  tff(c_59, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.83/3.00  tff(c_64, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_59])).
% 8.83/3.00  tff(c_165, plain, (![A_88, C_89]: (r2_hidden(k4_tarski(A_88, k1_funct_1(C_89, A_88)), C_89) | ~r2_hidden(A_88, k1_relat_1(C_89)) | ~v1_funct_1(C_89) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.83/3.00  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k2_relat_1(A_6)) | ~r2_hidden(k4_tarski(D_24, C_21), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.83/3.00  tff(c_182, plain, (![C_90, A_91]: (r2_hidden(k1_funct_1(C_90, A_91), k2_relat_1(C_90)) | ~r2_hidden(A_91, k1_relat_1(C_90)) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_165, c_10])).
% 8.83/3.00  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.83/3.00  tff(c_185, plain, (![C_90, A_91, B_2]: (r2_hidden(k1_funct_1(C_90, A_91), B_2) | ~r1_tarski(k2_relat_1(C_90), B_2) | ~r2_hidden(A_91, k1_relat_1(C_90)) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_182, c_2])).
% 8.83/3.00  tff(c_32, plain, (![A_36, C_38]: (r2_hidden(k4_tarski(A_36, k1_funct_1(C_38, A_36)), C_38) | ~r2_hidden(A_36, k1_relat_1(C_38)) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.83/3.00  tff(c_707, plain, (![A_152, C_153, B_154, D_155]: (r2_hidden(A_152, k10_relat_1(C_153, B_154)) | ~r2_hidden(D_155, B_154) | ~r2_hidden(k4_tarski(A_152, D_155), C_153) | ~r2_hidden(D_155, k2_relat_1(C_153)) | ~v1_relat_1(C_153))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.83/3.00  tff(c_915, plain, (![A_164, C_165]: (r2_hidden(A_164, k10_relat_1(C_165, k1_relat_1('#skF_8'))) | ~r2_hidden(k4_tarski(A_164, k1_funct_1('#skF_9', '#skF_7')), C_165) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1(C_165)) | ~v1_relat_1(C_165))), inference(resolution, [status(thm)], [c_91, c_707])).
% 8.83/3.00  tff(c_927, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_915])).
% 8.83/3.00  tff(c_936, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_67, c_927])).
% 8.83/3.00  tff(c_938, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_936])).
% 8.83/3.00  tff(c_941, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_185, c_938])).
% 8.83/3.00  tff(c_951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_67, c_64, c_941])).
% 8.83/3.00  tff(c_952, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_936])).
% 8.83/3.00  tff(c_972, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_30, c_952])).
% 8.83/3.00  tff(c_982, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_972])).
% 8.83/3.00  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_982])).
% 8.83/3.00  tff(c_985, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_52])).
% 8.83/3.00  tff(c_986, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 8.83/3.00  tff(c_1078, plain, (![A_198, B_199, C_200]: (r2_hidden(k4_tarski(A_198, '#skF_6'(A_198, B_199, C_200)), C_200) | ~r2_hidden(A_198, k10_relat_1(C_200, B_199)) | ~v1_relat_1(C_200))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.83/3.00  tff(c_34, plain, (![C_38, A_36, B_37]: (k1_funct_1(C_38, A_36)=B_37 | ~r2_hidden(k4_tarski(A_36, B_37), C_38) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.83/3.00  tff(c_1348, plain, (![C_229, A_230, B_231]: (k1_funct_1(C_229, A_230)='#skF_6'(A_230, B_231, C_229) | ~v1_funct_1(C_229) | ~r2_hidden(A_230, k10_relat_1(C_229, B_231)) | ~v1_relat_1(C_229))), inference(resolution, [status(thm)], [c_1078, c_34])).
% 8.83/3.00  tff(c_8304, plain, (![A_761, B_762, A_763]: ('#skF_6'(A_761, k1_relat_1(B_762), A_763)=k1_funct_1(A_763, A_761) | ~v1_funct_1(A_763) | ~r2_hidden(A_761, k1_relat_1(k5_relat_1(A_763, B_762))) | ~v1_relat_1(A_763) | ~v1_relat_1(B_762) | ~v1_relat_1(A_763))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1348])).
% 8.83/3.00  tff(c_8506, plain, ('#skF_6'('#skF_7', k1_relat_1('#skF_8'), '#skF_9')=k1_funct_1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_985, c_8304])).
% 8.83/3.00  tff(c_8569, plain, ('#skF_6'('#skF_7', k1_relat_1('#skF_8'), '#skF_9')=k1_funct_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_38, c_8506])).
% 8.83/3.00  tff(c_22, plain, (![A_25, B_26, C_27]: (r2_hidden('#skF_6'(A_25, B_26, C_27), B_26) | ~r2_hidden(A_25, k10_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.83/3.00  tff(c_8602, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8569, c_22])).
% 8.83/3.00  tff(c_8624, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8602])).
% 8.83/3.00  tff(c_8625, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_986, c_8624])).
% 8.83/3.00  tff(c_8629, plain, (~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_30, c_8625])).
% 8.83/3.00  tff(c_8632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_985, c_8629])).
% 8.83/3.00  tff(c_8634, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_56])).
% 8.83/3.00  tff(c_8657, plain, (![A_769, B_770]: (k10_relat_1(A_769, k1_relat_1(B_770))=k1_relat_1(k5_relat_1(A_769, B_770)) | ~v1_relat_1(B_770) | ~v1_relat_1(A_769))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.83/3.00  tff(c_28, plain, (![B_32, A_31]: (r1_tarski(k10_relat_1(B_32, A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.83/3.00  tff(c_8710, plain, (![A_789, B_790]: (r1_tarski(k1_relat_1(k5_relat_1(A_789, B_790)), k1_relat_1(A_789)) | ~v1_relat_1(A_789) | ~v1_relat_1(B_790) | ~v1_relat_1(A_789))), inference(superposition, [status(thm), theory('equality')], [c_8657, c_28])).
% 8.83/3.00  tff(c_8633, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_56])).
% 8.83/3.00  tff(c_8636, plain, (![C_764, B_765, A_766]: (r2_hidden(C_764, B_765) | ~r2_hidden(C_764, A_766) | ~r1_tarski(A_766, B_765))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.83/3.00  tff(c_8644, plain, (![B_765]: (r2_hidden('#skF_7', B_765) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_9', '#skF_8')), B_765))), inference(resolution, [status(thm)], [c_8633, c_8636])).
% 8.83/3.00  tff(c_8716, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_8710, c_8644])).
% 8.83/3.00  tff(c_8720, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_8716])).
% 8.83/3.00  tff(c_8722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8634, c_8720])).
% 8.83/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.83/3.00  
% 8.83/3.00  Inference rules
% 8.83/3.00  ----------------------
% 8.83/3.00  #Ref     : 0
% 8.83/3.00  #Sup     : 2044
% 8.83/3.00  #Fact    : 0
% 8.83/3.00  #Define  : 0
% 8.83/3.00  #Split   : 5
% 8.83/3.00  #Chain   : 0
% 8.83/3.00  #Close   : 0
% 8.83/3.00  
% 8.83/3.00  Ordering : KBO
% 8.83/3.00  
% 8.83/3.00  Simplification rules
% 8.83/3.00  ----------------------
% 8.83/3.00  #Subsume      : 166
% 8.83/3.00  #Demod        : 150
% 8.83/3.00  #Tautology    : 100
% 8.83/3.00  #SimpNegUnit  : 3
% 8.83/3.00  #BackRed      : 0
% 8.83/3.00  
% 8.83/3.00  #Partial instantiations: 0
% 8.83/3.00  #Strategies tried      : 1
% 8.83/3.00  
% 8.83/3.00  Timing (in seconds)
% 8.83/3.01  ----------------------
% 8.83/3.01  Preprocessing        : 0.31
% 8.83/3.01  Parsing              : 0.16
% 8.83/3.01  CNF conversion       : 0.02
% 8.83/3.01  Main loop            : 1.92
% 8.83/3.01  Inferencing          : 0.60
% 8.83/3.01  Reduction            : 0.43
% 8.83/3.01  Demodulation         : 0.29
% 8.83/3.01  BG Simplification    : 0.08
% 8.83/3.01  Subsumption          : 0.62
% 8.83/3.01  Abstraction          : 0.11
% 8.83/3.01  MUC search           : 0.00
% 8.83/3.01  Cooper               : 0.00
% 8.83/3.01  Total                : 2.26
% 8.83/3.01  Index Insertion      : 0.00
% 8.83/3.01  Index Deletion       : 0.00
% 8.83/3.01  Index Matching       : 0.00
% 8.83/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
