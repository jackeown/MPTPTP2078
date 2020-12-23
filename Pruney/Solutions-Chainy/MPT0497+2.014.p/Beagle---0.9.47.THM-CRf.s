%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 169 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 351 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_40,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_69,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_288,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(A_64,B_65)
      | ~ r2_hidden(A_64,k1_relat_1(k7_relat_1(C_66,B_65)))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_313,plain,(
    ! [C_66,B_65] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_66,B_65))),B_65)
      | ~ v1_relat_1(C_66)
      | v1_xboole_0(k1_relat_1(k7_relat_1(C_66,B_65))) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_400,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(A_73,k1_relat_1(C_74))
      | ~ r2_hidden(A_73,k1_relat_1(k7_relat_1(C_74,B_75)))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_890,plain,(
    ! [C_100,B_101] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_100,B_101))),k1_relat_1(C_100))
      | ~ v1_relat_1(C_100)
      | v1_xboole_0(k1_relat_1(k7_relat_1(C_100,B_101))) ) ),
    inference(resolution,[status(thm)],[c_4,c_400])).

tff(c_46,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_156,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_46])).

tff(c_257,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,B_61)
      | ~ r2_hidden(C_62,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_269,plain,(
    ! [C_62] :
      ( ~ r2_hidden(C_62,'#skF_3')
      | ~ r2_hidden(C_62,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_156,c_257])).

tff(c_902,plain,(
    ! [B_101] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4',B_101))),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4',B_101))) ) ),
    inference(resolution,[status(thm)],[c_890,c_269])).

tff(c_2116,plain,(
    ! [B_151] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4',B_151))),'#skF_3')
      | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4',B_151))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_902])).

tff(c_2132,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_313,c_2116])).

tff(c_2152,plain,(
    v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2132])).

tff(c_28,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_202,plain,(
    ! [A_58,B_59] :
      ( k5_relat_1(k6_relat_1(A_58),B_59) = k7_relat_1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_354,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_relat_1(A_69)) = A_69
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_202])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_xboole_0(k7_relat_1(A_15,B_16))
      | ~ v1_xboole_0(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_366,plain,(
    ! [A_69] :
      ( v1_xboole_0(A_69)
      | ~ v1_xboole_0(k1_relat_1(A_69))
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_22])).

tff(c_2177,plain,
    ( v1_xboole_0(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2152,c_366])).

tff(c_2312,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2177])).

tff(c_2315,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_2312])).

tff(c_2319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2315])).

tff(c_2320,plain,(
    v1_xboole_0(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2177])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2413,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2320,c_8])).

tff(c_2418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_2413])).

tff(c_2419,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2420,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2424,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_18])).

tff(c_2428,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2424])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2432,plain,(
    ! [A_155,B_156] :
      ( v1_xboole_0(k7_relat_1(A_155,B_156))
      | ~ v1_xboole_0(B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2486,plain,(
    ! [A_166,B_167] :
      ( k7_relat_1(A_166,B_167) = k1_xboole_0
      | ~ v1_xboole_0(B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(resolution,[status(thm)],[c_2432,c_8])).

tff(c_2493,plain,(
    ! [A_168] :
      ( k7_relat_1(A_168,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_6,c_2486])).

tff(c_2503,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2428,c_2493])).

tff(c_2803,plain,(
    ! [A_191,C_192,B_193] :
      ( r2_hidden(A_191,k1_relat_1(k7_relat_1(C_192,B_193)))
      | ~ r2_hidden(A_191,k1_relat_1(C_192))
      | ~ r2_hidden(A_191,B_193)
      | ~ v1_relat_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2865,plain,(
    ! [C_195,B_196,A_197] :
      ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(C_195,B_196)))
      | ~ r2_hidden(A_197,k1_relat_1(C_195))
      | ~ r2_hidden(A_197,B_196)
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_2803,c_2])).

tff(c_2875,plain,(
    ! [A_197] :
      ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_197,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_197,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2503,c_2865])).

tff(c_2885,plain,(
    ! [A_197] : ~ r2_hidden(A_197,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_26,c_6,c_26,c_2875])).

tff(c_2830,plain,(
    ! [A_191] :
      ( r2_hidden(A_191,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_191,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_191,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_2803])).

tff(c_2841,plain,(
    ! [A_191] :
      ( r2_hidden(A_191,k1_xboole_0)
      | ~ r2_hidden(A_191,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_191,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26,c_2830])).

tff(c_2906,plain,(
    ! [A_199] :
      ( ~ r2_hidden(A_199,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_199,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2885,c_2841])).

tff(c_2941,plain,(
    ! [A_202] :
      ( ~ r2_hidden('#skF_2'(A_202,k1_relat_1('#skF_4')),'#skF_3')
      | r1_xboole_0(A_202,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_2906])).

tff(c_2946,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_2941])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2950,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2946,c_10])).

tff(c_2955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2419,c_2950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.75  
% 3.64/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.76  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.64/1.76  
% 3.64/1.76  %Foreground sorts:
% 3.64/1.76  
% 3.64/1.76  
% 3.64/1.76  %Background operators:
% 3.64/1.76  
% 3.64/1.76  
% 3.64/1.76  %Foreground operators:
% 3.64/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.64/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.64/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.64/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.64/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.64/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.76  
% 3.64/1.77  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.64/1.77  tff(f_62, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.64/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.64/1.77  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 3.64/1.77  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.64/1.77  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 3.64/1.77  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.64/1.77  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 3.64/1.77  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.64/1.77  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.64/1.77  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.64/1.77  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.64/1.77  tff(c_40, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.77  tff(c_69, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.64/1.77  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.77  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.64/1.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.77  tff(c_288, plain, (![A_64, B_65, C_66]: (r2_hidden(A_64, B_65) | ~r2_hidden(A_64, k1_relat_1(k7_relat_1(C_66, B_65))) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.77  tff(c_313, plain, (![C_66, B_65]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_66, B_65))), B_65) | ~v1_relat_1(C_66) | v1_xboole_0(k1_relat_1(k7_relat_1(C_66, B_65))))), inference(resolution, [status(thm)], [c_4, c_288])).
% 3.64/1.77  tff(c_400, plain, (![A_73, C_74, B_75]: (r2_hidden(A_73, k1_relat_1(C_74)) | ~r2_hidden(A_73, k1_relat_1(k7_relat_1(C_74, B_75))) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.77  tff(c_890, plain, (![C_100, B_101]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_100, B_101))), k1_relat_1(C_100)) | ~v1_relat_1(C_100) | v1_xboole_0(k1_relat_1(k7_relat_1(C_100, B_101))))), inference(resolution, [status(thm)], [c_4, c_400])).
% 3.64/1.77  tff(c_46, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.77  tff(c_156, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_69, c_46])).
% 3.64/1.77  tff(c_257, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, B_61) | ~r2_hidden(C_62, A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.77  tff(c_269, plain, (![C_62]: (~r2_hidden(C_62, '#skF_3') | ~r2_hidden(C_62, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_156, c_257])).
% 3.64/1.77  tff(c_902, plain, (![B_101]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4', B_101))), '#skF_3') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', B_101))))), inference(resolution, [status(thm)], [c_890, c_269])).
% 3.64/1.77  tff(c_2116, plain, (![B_151]: (~r2_hidden('#skF_1'(k1_relat_1(k7_relat_1('#skF_4', B_151))), '#skF_3') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', B_151))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_902])).
% 3.64/1.77  tff(c_2132, plain, (~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_313, c_2116])).
% 3.64/1.77  tff(c_2152, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2132])).
% 3.64/1.77  tff(c_28, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.64/1.77  tff(c_202, plain, (![A_58, B_59]: (k5_relat_1(k6_relat_1(A_58), B_59)=k7_relat_1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.77  tff(c_354, plain, (![A_69]: (k7_relat_1(A_69, k1_relat_1(A_69))=A_69 | ~v1_relat_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_28, c_202])).
% 3.64/1.77  tff(c_22, plain, (![A_15, B_16]: (v1_xboole_0(k7_relat_1(A_15, B_16)) | ~v1_xboole_0(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.77  tff(c_366, plain, (![A_69]: (v1_xboole_0(A_69) | ~v1_xboole_0(k1_relat_1(A_69)) | ~v1_relat_1(A_69) | ~v1_relat_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_354, c_22])).
% 3.64/1.77  tff(c_2177, plain, (v1_xboole_0(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2152, c_366])).
% 3.64/1.77  tff(c_2312, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2177])).
% 3.64/1.77  tff(c_2315, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_2312])).
% 3.64/1.77  tff(c_2319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_2315])).
% 3.64/1.77  tff(c_2320, plain, (v1_xboole_0(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_2177])).
% 3.64/1.77  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.64/1.77  tff(c_2413, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2320, c_8])).
% 3.64/1.77  tff(c_2418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_2413])).
% 3.64/1.77  tff(c_2419, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.64/1.77  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.77  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.77  tff(c_2420, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.64/1.77  tff(c_2424, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2420, c_18])).
% 3.64/1.77  tff(c_2428, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2424])).
% 3.64/1.77  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.64/1.77  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.77  tff(c_2432, plain, (![A_155, B_156]: (v1_xboole_0(k7_relat_1(A_155, B_156)) | ~v1_xboole_0(B_156) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.77  tff(c_2486, plain, (![A_166, B_167]: (k7_relat_1(A_166, B_167)=k1_xboole_0 | ~v1_xboole_0(B_167) | ~v1_relat_1(A_166))), inference(resolution, [status(thm)], [c_2432, c_8])).
% 3.64/1.77  tff(c_2493, plain, (![A_168]: (k7_relat_1(A_168, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_6, c_2486])).
% 3.64/1.77  tff(c_2503, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2428, c_2493])).
% 3.64/1.77  tff(c_2803, plain, (![A_191, C_192, B_193]: (r2_hidden(A_191, k1_relat_1(k7_relat_1(C_192, B_193))) | ~r2_hidden(A_191, k1_relat_1(C_192)) | ~r2_hidden(A_191, B_193) | ~v1_relat_1(C_192))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.77  tff(c_2865, plain, (![C_195, B_196, A_197]: (~v1_xboole_0(k1_relat_1(k7_relat_1(C_195, B_196))) | ~r2_hidden(A_197, k1_relat_1(C_195)) | ~r2_hidden(A_197, B_196) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_2803, c_2])).
% 3.64/1.77  tff(c_2875, plain, (![A_197]: (~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_197, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_197, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2503, c_2865])).
% 3.64/1.77  tff(c_2885, plain, (![A_197]: (~r2_hidden(A_197, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_26, c_6, c_26, c_2875])).
% 3.64/1.77  tff(c_2830, plain, (![A_191]: (r2_hidden(A_191, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_191, k1_relat_1('#skF_4')) | ~r2_hidden(A_191, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2420, c_2803])).
% 3.64/1.77  tff(c_2841, plain, (![A_191]: (r2_hidden(A_191, k1_xboole_0) | ~r2_hidden(A_191, k1_relat_1('#skF_4')) | ~r2_hidden(A_191, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26, c_2830])).
% 3.64/1.77  tff(c_2906, plain, (![A_199]: (~r2_hidden(A_199, k1_relat_1('#skF_4')) | ~r2_hidden(A_199, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2885, c_2841])).
% 3.64/1.77  tff(c_2941, plain, (![A_202]: (~r2_hidden('#skF_2'(A_202, k1_relat_1('#skF_4')), '#skF_3') | r1_xboole_0(A_202, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_14, c_2906])).
% 3.64/1.77  tff(c_2946, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_2941])).
% 3.64/1.77  tff(c_10, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.64/1.77  tff(c_2950, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2946, c_10])).
% 3.64/1.77  tff(c_2955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2419, c_2950])).
% 3.64/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.77  
% 3.64/1.77  Inference rules
% 3.64/1.77  ----------------------
% 3.64/1.77  #Ref     : 0
% 3.64/1.77  #Sup     : 641
% 3.64/1.77  #Fact    : 0
% 3.64/1.77  #Define  : 0
% 3.64/1.77  #Split   : 6
% 3.64/1.77  #Chain   : 0
% 3.64/1.77  #Close   : 0
% 3.64/1.77  
% 3.64/1.77  Ordering : KBO
% 3.64/1.77  
% 3.64/1.77  Simplification rules
% 3.64/1.77  ----------------------
% 3.64/1.77  #Subsume      : 142
% 3.64/1.77  #Demod        : 724
% 3.64/1.77  #Tautology    : 301
% 3.64/1.77  #SimpNegUnit  : 43
% 3.64/1.77  #BackRed      : 5
% 3.64/1.77  
% 3.64/1.77  #Partial instantiations: 0
% 3.64/1.77  #Strategies tried      : 1
% 3.64/1.77  
% 3.64/1.77  Timing (in seconds)
% 3.64/1.77  ----------------------
% 3.64/1.78  Preprocessing        : 0.30
% 3.64/1.78  Parsing              : 0.18
% 3.64/1.78  CNF conversion       : 0.02
% 3.64/1.78  Main loop            : 0.61
% 3.64/1.78  Inferencing          : 0.22
% 3.64/1.78  Reduction            : 0.19
% 3.64/1.78  Demodulation         : 0.13
% 3.64/1.78  BG Simplification    : 0.02
% 3.64/1.78  Subsumption          : 0.13
% 3.64/1.78  Abstraction          : 0.03
% 3.64/1.78  MUC search           : 0.00
% 3.64/1.78  Cooper               : 0.00
% 3.64/1.78  Total                : 0.95
% 3.64/1.78  Index Insertion      : 0.00
% 3.64/1.78  Index Deletion       : 0.00
% 3.64/1.78  Index Matching       : 0.00
% 3.64/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
