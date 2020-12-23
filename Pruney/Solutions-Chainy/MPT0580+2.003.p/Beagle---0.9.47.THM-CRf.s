%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   68 (  97 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 178 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [B_34,C_35,A_36] :
      ( r2_hidden(B_34,C_35)
      | ~ r1_tarski(k2_tarski(A_36,B_34),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    ! [B_37,A_38] : r2_hidden(B_37,k2_tarski(A_38,B_37)) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_122,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_146,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [B_21] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_21
      | ~ r2_hidden(B_21,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,(
    ! [B_21] :
      ( k1_xboole_0 = B_21
      | ~ r2_hidden(B_21,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_50])).

tff(c_155,plain,(
    ! [B_45] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_45) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_45) ) ),
    inference(resolution,[status(thm)],[c_146,c_75])).

tff(c_427,plain,(
    ! [A_70] :
      ( v3_relat_1(A_70)
      | ~ r1_tarski(k2_relat_1(A_70),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_431,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155,c_427])).

tff(c_437,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_431])).

tff(c_438,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_437])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_465,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_4])).

tff(c_477,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_465])).

tff(c_34,plain,(
    ! [A_18] :
      ( v3_relat_1(A_18)
      | ~ r1_tarski(k2_relat_1(A_18),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_484,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_477,c_34])).

tff(c_495,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_484])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_495])).

tff(c_498,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_499,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,(
    ! [A_18] :
      ( r1_tarski(k2_relat_1(A_18),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_500,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_500])).

tff(c_503,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_692,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_709,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_3',B_112)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_112) ) ),
    inference(resolution,[status(thm)],[c_503,c_692])).

tff(c_713,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_709])).

tff(c_724,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_499,c_713])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_515,plain,(
    ! [C_73,B_74] : ~ r2_hidden(C_73,k4_xboole_0(B_74,k1_tarski(C_73))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_518,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_515])).

tff(c_522,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_530,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_522])).

tff(c_806,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden(A_125,k4_xboole_0(B_126,k1_tarski(C_127)))
      | C_127 = A_125
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_823,plain,(
    ! [A_125,C_127] :
      ( r2_hidden(A_125,k1_xboole_0)
      | C_127 = A_125
      | ~ r2_hidden(A_125,k1_tarski(C_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_806])).

tff(c_835,plain,(
    ! [C_128,A_129] :
      ( C_128 = A_129
      | ~ r2_hidden(A_129,k1_tarski(C_128)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_823])).

tff(c_838,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_724,c_835])).

tff(c_849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.43  
% 2.47/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.43  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.43  
% 2.47/1.43  %Foreground sorts:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Background operators:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Foreground operators:
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.43  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 2.47/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.43  
% 2.80/1.45  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 2.80/1.45  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.45  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.80/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.45  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 2.80/1.45  tff(f_44, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.80/1.45  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.80/1.45  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.80/1.45  tff(c_40, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.45  tff(c_60, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.80/1.45  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.45  tff(c_20, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.80/1.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.45  tff(c_105, plain, (![B_34, C_35, A_36]: (r2_hidden(B_34, C_35) | ~r1_tarski(k2_tarski(A_36, B_34), C_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.80/1.45  tff(c_119, plain, (![B_37, A_38]: (r2_hidden(B_37, k2_tarski(A_38, B_37)))), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.80/1.45  tff(c_122, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 2.80/1.45  tff(c_146, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.45  tff(c_50, plain, (![B_21]: (v3_relat_1('#skF_2') | k1_xboole_0=B_21 | ~r2_hidden(B_21, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.45  tff(c_75, plain, (![B_21]: (k1_xboole_0=B_21 | ~r2_hidden(B_21, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_50])).
% 2.80/1.45  tff(c_155, plain, (![B_45]: ('#skF_1'(k2_relat_1('#skF_2'), B_45)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_45))), inference(resolution, [status(thm)], [c_146, c_75])).
% 2.80/1.45  tff(c_427, plain, (![A_70]: (v3_relat_1(A_70) | ~r1_tarski(k2_relat_1(A_70), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.45  tff(c_431, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_155, c_427])).
% 2.80/1.45  tff(c_437, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_431])).
% 2.80/1.45  tff(c_438, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_437])).
% 2.80/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.45  tff(c_465, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_438, c_4])).
% 2.80/1.45  tff(c_477, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_465])).
% 2.80/1.45  tff(c_34, plain, (![A_18]: (v3_relat_1(A_18) | ~r1_tarski(k2_relat_1(A_18), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.45  tff(c_484, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_477, c_34])).
% 2.80/1.45  tff(c_495, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_484])).
% 2.80/1.45  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_495])).
% 2.80/1.45  tff(c_498, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 2.80/1.45  tff(c_499, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.80/1.45  tff(c_36, plain, (![A_18]: (r1_tarski(k2_relat_1(A_18), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.45  tff(c_42, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.45  tff(c_500, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.80/1.45  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_499, c_500])).
% 2.80/1.45  tff(c_503, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.80/1.45  tff(c_692, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.45  tff(c_709, plain, (![B_112]: (r2_hidden('#skF_3', B_112) | ~r1_tarski(k2_relat_1('#skF_2'), B_112))), inference(resolution, [status(thm)], [c_503, c_692])).
% 2.80/1.45  tff(c_713, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_709])).
% 2.80/1.45  tff(c_724, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_499, c_713])).
% 2.80/1.45  tff(c_18, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.45  tff(c_515, plain, (![C_73, B_74]: (~r2_hidden(C_73, k4_xboole_0(B_74, k1_tarski(C_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.45  tff(c_518, plain, (![C_73]: (~r2_hidden(C_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_515])).
% 2.80/1.45  tff(c_522, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.45  tff(c_530, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_522])).
% 2.80/1.45  tff(c_806, plain, (![A_125, B_126, C_127]: (r2_hidden(A_125, k4_xboole_0(B_126, k1_tarski(C_127))) | C_127=A_125 | ~r2_hidden(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.45  tff(c_823, plain, (![A_125, C_127]: (r2_hidden(A_125, k1_xboole_0) | C_127=A_125 | ~r2_hidden(A_125, k1_tarski(C_127)))), inference(superposition, [status(thm), theory('equality')], [c_530, c_806])).
% 2.80/1.45  tff(c_835, plain, (![C_128, A_129]: (C_128=A_129 | ~r2_hidden(A_129, k1_tarski(C_128)))), inference(negUnitSimplification, [status(thm)], [c_518, c_823])).
% 2.80/1.45  tff(c_838, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_724, c_835])).
% 2.80/1.45  tff(c_849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_838])).
% 2.80/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.45  
% 2.80/1.45  Inference rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Ref     : 0
% 2.80/1.45  #Sup     : 164
% 2.80/1.45  #Fact    : 0
% 2.80/1.45  #Define  : 0
% 2.80/1.45  #Split   : 4
% 2.80/1.45  #Chain   : 0
% 2.80/1.45  #Close   : 0
% 2.80/1.45  
% 2.80/1.45  Ordering : KBO
% 2.80/1.45  
% 2.80/1.45  Simplification rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Subsume      : 28
% 2.80/1.45  #Demod        : 50
% 2.80/1.45  #Tautology    : 79
% 2.80/1.45  #SimpNegUnit  : 11
% 2.80/1.45  #BackRed      : 4
% 2.80/1.45  
% 2.80/1.45  #Partial instantiations: 0
% 2.80/1.45  #Strategies tried      : 1
% 2.80/1.45  
% 2.80/1.45  Timing (in seconds)
% 2.80/1.45  ----------------------
% 2.80/1.45  Preprocessing        : 0.31
% 2.80/1.45  Parsing              : 0.17
% 2.80/1.45  CNF conversion       : 0.02
% 2.80/1.45  Main loop            : 0.30
% 2.80/1.45  Inferencing          : 0.11
% 2.80/1.45  Reduction            : 0.09
% 2.80/1.45  Demodulation         : 0.06
% 2.80/1.45  BG Simplification    : 0.02
% 2.80/1.45  Subsumption          : 0.06
% 2.80/1.45  Abstraction          : 0.01
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.65
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
