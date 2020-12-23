%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 193 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          :  182 ( 452 expanded)
%              Number of equality atoms :  103 ( 247 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_99,plain,(
    ! [A_82] :
      ( k1_relat_1(A_82) = k1_xboole_0
      | k2_relat_1(A_82) != k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_103,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_99])).

tff(c_104,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_23,C_59] :
      ( r2_hidden('#skF_7'(A_23,k2_relat_1(A_23),C_59),k1_relat_1(A_23))
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_23,D_62] :
      ( r2_hidden(k1_funct_1(A_23,D_62),k2_relat_1(A_23))
      | ~ r2_hidden(D_62,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [F_112,D_111,B_114,A_115,C_113] :
      ( F_112 = D_111
      | F_112 = C_113
      | F_112 = B_114
      | F_112 = A_115
      | ~ r2_hidden(F_112,k2_enumset1(A_115,B_114,C_113,D_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_202,plain,(
    ! [F_118,C_119,B_120,A_121] :
      ( F_118 = C_119
      | F_118 = B_120
      | F_118 = A_121
      | F_118 = A_121
      | ~ r2_hidden(F_118,k1_enumset1(A_121,B_120,C_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_226,plain,(
    ! [F_122,B_123,A_124] :
      ( F_122 = B_123
      | F_122 = A_124
      | F_122 = A_124
      | F_122 = A_124
      | ~ r2_hidden(F_122,k2_tarski(A_124,B_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_245,plain,(
    ! [F_125,A_126] :
      ( F_125 = A_126
      | F_125 = A_126
      | F_125 = A_126
      | F_125 = A_126
      | ~ r2_hidden(F_125,k1_tarski(A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_367,plain,(
    ! [F_135] :
      ( F_135 = '#skF_8'
      | F_135 = '#skF_8'
      | F_135 = '#skF_8'
      | F_135 = '#skF_8'
      | ~ r2_hidden(F_135,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_245])).

tff(c_374,plain,(
    ! [C_59] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_59) = '#skF_8'
      | ~ r2_hidden(C_59,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_367])).

tff(c_385,plain,(
    ! [C_136] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_136) = '#skF_8'
      | ~ r2_hidden(C_136,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_374])).

tff(c_389,plain,(
    ! [D_62] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_62)) = '#skF_8'
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_385])).

tff(c_400,plain,(
    ! [D_137] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_137)) = '#skF_8'
      | ~ r2_hidden(D_137,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_389])).

tff(c_50,plain,(
    ! [A_23,C_59] :
      ( k1_funct_1(A_23,'#skF_7'(A_23,k2_relat_1(A_23),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_406,plain,(
    ! [D_137] :
      ( k1_funct_1('#skF_9',D_137) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_137),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_137,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_50])).

tff(c_8018,plain,(
    ! [D_14970] :
      ( k1_funct_1('#skF_9',D_14970) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_14970),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_14970,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_406])).

tff(c_8043,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9',D_62) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_8018])).

tff(c_8049,plain,(
    ! [D_15171] :
      ( k1_funct_1('#skF_9',D_15171) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_15171,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8043])).

tff(c_8076,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_59)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_59,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_8049])).

tff(c_9336,plain,(
    ! [C_17793] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_17793)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_17793,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8076])).

tff(c_9369,plain,(
    ! [C_17793] :
      ( k1_funct_1('#skF_9','#skF_8') = C_17793
      | ~ r2_hidden(C_17793,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_17793,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9336,c_50])).

tff(c_9444,plain,(
    ! [C_17994] :
      ( k1_funct_1('#skF_9','#skF_8') = C_17994
      | ~ r2_hidden(C_17994,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_9369])).

tff(c_9471,plain,(
    ! [B_12] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_12) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_9444])).

tff(c_9484,plain,(
    ! [B_18195] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_18195) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_18195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_9471])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( '#skF_1'(A_11,B_12) != B_12
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_9495,plain,(
    ! [B_18195] :
      ( k1_funct_1('#skF_9','#skF_8') != B_18195
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_18195)
      | k2_relat_1('#skF_9') = k1_tarski(B_18195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9484,c_10])).

tff(c_9646,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_9495])).

tff(c_66,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9646,c_66])).

tff(c_9651,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_9653,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9651,c_68])).

tff(c_9675,plain,(
    ! [A_18602,B_18603,C_18604] : k2_enumset1(A_18602,A_18602,B_18603,C_18604) = k1_enumset1(A_18602,B_18603,C_18604) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [F_21,B_15,C_16,D_17] : r2_hidden(F_21,k2_enumset1(F_21,B_15,C_16,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9696,plain,(
    ! [A_18605,B_18606,C_18607] : r2_hidden(A_18605,k1_enumset1(A_18605,B_18606,C_18607)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9675,c_22])).

tff(c_9701,plain,(
    ! [A_18610,B_18611] : r2_hidden(A_18610,k2_tarski(A_18610,B_18611)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_9696])).

tff(c_9705,plain,(
    ! [A_18612] : r2_hidden(A_18612,k1_tarski(A_18612)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9701])).

tff(c_9708,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9653,c_9705])).

tff(c_9652,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_9733,plain,(
    ! [A_18625,D_18626] :
      ( r2_hidden(k1_funct_1(A_18625,D_18626),k2_relat_1(A_18625))
      | ~ r2_hidden(D_18626,k1_relat_1(A_18625))
      | ~ v1_funct_1(A_18625)
      | ~ v1_relat_1(A_18625) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9736,plain,(
    ! [D_18626] :
      ( r2_hidden(k1_funct_1('#skF_9',D_18626),k1_xboole_0)
      | ~ r2_hidden(D_18626,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9652,c_9733])).

tff(c_9738,plain,(
    ! [D_18626] :
      ( r2_hidden(k1_funct_1('#skF_9',D_18626),k1_xboole_0)
      | ~ r2_hidden(D_18626,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_9651,c_9736])).

tff(c_9739,plain,(
    ! [D_18627,C_18629,F_18628,B_18630,A_18631] :
      ( F_18628 = D_18627
      | F_18628 = C_18629
      | F_18628 = B_18630
      | F_18628 = A_18631
      | ~ r2_hidden(F_18628,k2_enumset1(A_18631,B_18630,C_18629,D_18627)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9769,plain,(
    ! [F_18633,C_18634,B_18635,A_18636] :
      ( F_18633 = C_18634
      | F_18633 = B_18635
      | F_18633 = A_18636
      | F_18633 = A_18636
      | ~ r2_hidden(F_18633,k1_enumset1(A_18636,B_18635,C_18634)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_9739])).

tff(c_9793,plain,(
    ! [F_18637,B_18638,A_18639] :
      ( F_18637 = B_18638
      | F_18637 = A_18639
      | F_18637 = A_18639
      | F_18637 = A_18639
      | ~ r2_hidden(F_18637,k2_tarski(A_18639,B_18638)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_9769])).

tff(c_9824,plain,(
    ! [F_18643,A_18644] :
      ( F_18643 = A_18644
      | F_18643 = A_18644
      | F_18643 = A_18644
      | F_18643 = A_18644
      | ~ r2_hidden(F_18643,k1_tarski(A_18644)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9793])).

tff(c_9838,plain,(
    ! [F_18645] :
      ( F_18645 = '#skF_8'
      | F_18645 = '#skF_8'
      | F_18645 = '#skF_8'
      | F_18645 = '#skF_8'
      | ~ r2_hidden(F_18645,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9653,c_9824])).

tff(c_9858,plain,(
    ! [D_18646] :
      ( k1_funct_1('#skF_9',D_18646) = '#skF_8'
      | ~ r2_hidden(D_18646,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9738,c_9838])).

tff(c_9874,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9708,c_9858])).

tff(c_9658,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9652,c_66])).

tff(c_9900,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9874,c_9658])).

tff(c_9903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9653,c_9900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.75  
% 7.47/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.75  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 7.47/2.75  
% 7.47/2.75  %Foreground sorts:
% 7.47/2.75  
% 7.47/2.75  
% 7.47/2.75  %Background operators:
% 7.47/2.75  
% 7.47/2.75  
% 7.47/2.75  %Foreground operators:
% 7.47/2.75  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.47/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.47/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.47/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 7.47/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.47/2.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.47/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.47/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.47/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.47/2.75  tff('#skF_9', type, '#skF_9': $i).
% 7.47/2.75  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.47/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.47/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.47/2.75  tff('#skF_8', type, '#skF_8': $i).
% 7.47/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.47/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.47/2.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.47/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.47/2.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.47/2.75  
% 7.47/2.78  tff(f_95, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 7.47/2.78  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.47/2.78  tff(f_47, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 7.47/2.78  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.47/2.78  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.47/2.78  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.47/2.78  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.47/2.78  tff(f_65, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 7.47/2.78  tff(c_72, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.78  tff(c_99, plain, (![A_82]: (k1_relat_1(A_82)=k1_xboole_0 | k2_relat_1(A_82)!=k1_xboole_0 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.47/2.78  tff(c_103, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_99])).
% 7.47/2.78  tff(c_104, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_103])).
% 7.47/2.78  tff(c_12, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.47/2.78  tff(c_70, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.78  tff(c_52, plain, (![A_23, C_59]: (r2_hidden('#skF_7'(A_23, k2_relat_1(A_23), C_59), k1_relat_1(A_23)) | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.47/2.78  tff(c_48, plain, (![A_23, D_62]: (r2_hidden(k1_funct_1(A_23, D_62), k2_relat_1(A_23)) | ~r2_hidden(D_62, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.47/2.78  tff(c_68, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.78  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.47/2.78  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.47/2.78  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.47/2.78  tff(c_172, plain, (![F_112, D_111, B_114, A_115, C_113]: (F_112=D_111 | F_112=C_113 | F_112=B_114 | F_112=A_115 | ~r2_hidden(F_112, k2_enumset1(A_115, B_114, C_113, D_111)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.47/2.78  tff(c_202, plain, (![F_118, C_119, B_120, A_121]: (F_118=C_119 | F_118=B_120 | F_118=A_121 | F_118=A_121 | ~r2_hidden(F_118, k1_enumset1(A_121, B_120, C_119)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_172])).
% 7.47/2.78  tff(c_226, plain, (![F_122, B_123, A_124]: (F_122=B_123 | F_122=A_124 | F_122=A_124 | F_122=A_124 | ~r2_hidden(F_122, k2_tarski(A_124, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 7.47/2.78  tff(c_245, plain, (![F_125, A_126]: (F_125=A_126 | F_125=A_126 | F_125=A_126 | F_125=A_126 | ~r2_hidden(F_125, k1_tarski(A_126)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_226])).
% 7.47/2.78  tff(c_367, plain, (![F_135]: (F_135='#skF_8' | F_135='#skF_8' | F_135='#skF_8' | F_135='#skF_8' | ~r2_hidden(F_135, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_245])).
% 7.47/2.78  tff(c_374, plain, (![C_59]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_59)='#skF_8' | ~r2_hidden(C_59, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_367])).
% 7.47/2.78  tff(c_385, plain, (![C_136]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_136)='#skF_8' | ~r2_hidden(C_136, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_374])).
% 7.47/2.78  tff(c_389, plain, (![D_62]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_62))='#skF_8' | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_385])).
% 7.47/2.78  tff(c_400, plain, (![D_137]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_137))='#skF_8' | ~r2_hidden(D_137, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_389])).
% 7.47/2.78  tff(c_50, plain, (![A_23, C_59]: (k1_funct_1(A_23, '#skF_7'(A_23, k2_relat_1(A_23), C_59))=C_59 | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.47/2.78  tff(c_406, plain, (![D_137]: (k1_funct_1('#skF_9', D_137)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_137), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_137, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_400, c_50])).
% 7.47/2.78  tff(c_8018, plain, (![D_14970]: (k1_funct_1('#skF_9', D_14970)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_14970), k2_relat_1('#skF_9')) | ~r2_hidden(D_14970, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_406])).
% 7.47/2.78  tff(c_8043, plain, (![D_62]: (k1_funct_1('#skF_9', D_62)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_8018])).
% 7.47/2.78  tff(c_8049, plain, (![D_15171]: (k1_funct_1('#skF_9', D_15171)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_15171, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8043])).
% 7.47/2.78  tff(c_8076, plain, (![C_59]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_59))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_59, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_8049])).
% 7.47/2.78  tff(c_9336, plain, (![C_17793]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_17793))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_17793, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8076])).
% 7.47/2.78  tff(c_9369, plain, (![C_17793]: (k1_funct_1('#skF_9', '#skF_8')=C_17793 | ~r2_hidden(C_17793, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_17793, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_9336, c_50])).
% 7.47/2.78  tff(c_9444, plain, (![C_17994]: (k1_funct_1('#skF_9', '#skF_8')=C_17994 | ~r2_hidden(C_17994, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_9369])).
% 7.47/2.78  tff(c_9471, plain, (![B_12]: ('#skF_1'(k2_relat_1('#skF_9'), B_12)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_12))), inference(resolution, [status(thm)], [c_12, c_9444])).
% 7.47/2.78  tff(c_9484, plain, (![B_18195]: ('#skF_1'(k2_relat_1('#skF_9'), B_18195)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_18195))), inference(negUnitSimplification, [status(thm)], [c_104, c_9471])).
% 7.47/2.78  tff(c_10, plain, (![A_11, B_12]: ('#skF_1'(A_11, B_12)!=B_12 | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.47/2.78  tff(c_9495, plain, (![B_18195]: (k1_funct_1('#skF_9', '#skF_8')!=B_18195 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_18195) | k2_relat_1('#skF_9')=k1_tarski(B_18195))), inference(superposition, [status(thm), theory('equality')], [c_9484, c_10])).
% 7.47/2.78  tff(c_9646, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_104, c_9495])).
% 7.47/2.78  tff(c_66, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.78  tff(c_9650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9646, c_66])).
% 7.47/2.78  tff(c_9651, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_103])).
% 7.47/2.78  tff(c_9653, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9651, c_68])).
% 7.47/2.78  tff(c_9675, plain, (![A_18602, B_18603, C_18604]: (k2_enumset1(A_18602, A_18602, B_18603, C_18604)=k1_enumset1(A_18602, B_18603, C_18604))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.47/2.78  tff(c_22, plain, (![F_21, B_15, C_16, D_17]: (r2_hidden(F_21, k2_enumset1(F_21, B_15, C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.47/2.78  tff(c_9696, plain, (![A_18605, B_18606, C_18607]: (r2_hidden(A_18605, k1_enumset1(A_18605, B_18606, C_18607)))), inference(superposition, [status(thm), theory('equality')], [c_9675, c_22])).
% 7.47/2.78  tff(c_9701, plain, (![A_18610, B_18611]: (r2_hidden(A_18610, k2_tarski(A_18610, B_18611)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_9696])).
% 7.47/2.78  tff(c_9705, plain, (![A_18612]: (r2_hidden(A_18612, k1_tarski(A_18612)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9701])).
% 7.47/2.78  tff(c_9708, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9653, c_9705])).
% 7.47/2.78  tff(c_9652, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_103])).
% 7.47/2.78  tff(c_9733, plain, (![A_18625, D_18626]: (r2_hidden(k1_funct_1(A_18625, D_18626), k2_relat_1(A_18625)) | ~r2_hidden(D_18626, k1_relat_1(A_18625)) | ~v1_funct_1(A_18625) | ~v1_relat_1(A_18625))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.47/2.78  tff(c_9736, plain, (![D_18626]: (r2_hidden(k1_funct_1('#skF_9', D_18626), k1_xboole_0) | ~r2_hidden(D_18626, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9652, c_9733])).
% 7.47/2.78  tff(c_9738, plain, (![D_18626]: (r2_hidden(k1_funct_1('#skF_9', D_18626), k1_xboole_0) | ~r2_hidden(D_18626, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_9651, c_9736])).
% 7.47/2.78  tff(c_9739, plain, (![D_18627, C_18629, F_18628, B_18630, A_18631]: (F_18628=D_18627 | F_18628=C_18629 | F_18628=B_18630 | F_18628=A_18631 | ~r2_hidden(F_18628, k2_enumset1(A_18631, B_18630, C_18629, D_18627)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.47/2.78  tff(c_9769, plain, (![F_18633, C_18634, B_18635, A_18636]: (F_18633=C_18634 | F_18633=B_18635 | F_18633=A_18636 | F_18633=A_18636 | ~r2_hidden(F_18633, k1_enumset1(A_18636, B_18635, C_18634)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_9739])).
% 7.47/2.78  tff(c_9793, plain, (![F_18637, B_18638, A_18639]: (F_18637=B_18638 | F_18637=A_18639 | F_18637=A_18639 | F_18637=A_18639 | ~r2_hidden(F_18637, k2_tarski(A_18639, B_18638)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_9769])).
% 7.47/2.78  tff(c_9824, plain, (![F_18643, A_18644]: (F_18643=A_18644 | F_18643=A_18644 | F_18643=A_18644 | F_18643=A_18644 | ~r2_hidden(F_18643, k1_tarski(A_18644)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9793])).
% 7.47/2.78  tff(c_9838, plain, (![F_18645]: (F_18645='#skF_8' | F_18645='#skF_8' | F_18645='#skF_8' | F_18645='#skF_8' | ~r2_hidden(F_18645, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9653, c_9824])).
% 7.47/2.78  tff(c_9858, plain, (![D_18646]: (k1_funct_1('#skF_9', D_18646)='#skF_8' | ~r2_hidden(D_18646, k1_xboole_0))), inference(resolution, [status(thm)], [c_9738, c_9838])).
% 7.47/2.78  tff(c_9874, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_9708, c_9858])).
% 7.47/2.78  tff(c_9658, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9652, c_66])).
% 7.47/2.78  tff(c_9900, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9874, c_9658])).
% 7.47/2.78  tff(c_9903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9653, c_9900])).
% 7.47/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.78  
% 7.47/2.78  Inference rules
% 7.47/2.78  ----------------------
% 7.47/2.78  #Ref     : 6
% 7.47/2.78  #Sup     : 1962
% 7.47/2.78  #Fact    : 5
% 7.47/2.78  #Define  : 0
% 7.47/2.78  #Split   : 5
% 7.47/2.78  #Chain   : 0
% 7.47/2.78  #Close   : 0
% 7.47/2.78  
% 7.47/2.78  Ordering : KBO
% 7.47/2.78  
% 7.47/2.78  Simplification rules
% 7.47/2.78  ----------------------
% 7.47/2.78  #Subsume      : 708
% 7.47/2.78  #Demod        : 314
% 7.47/2.78  #Tautology    : 482
% 7.47/2.78  #SimpNegUnit  : 157
% 7.47/2.78  #BackRed      : 14
% 7.47/2.78  
% 7.47/2.79  #Partial instantiations: 8244
% 7.47/2.79  #Strategies tried      : 1
% 7.47/2.79  
% 7.47/2.79  Timing (in seconds)
% 7.47/2.79  ----------------------
% 7.47/2.79  Preprocessing        : 0.33
% 7.47/2.79  Parsing              : 0.16
% 7.47/2.79  CNF conversion       : 0.03
% 7.47/2.79  Main loop            : 1.55
% 7.47/2.79  Inferencing          : 0.57
% 7.47/2.79  Reduction            : 0.44
% 7.47/2.79  Demodulation         : 0.31
% 7.47/2.79  BG Simplification    : 0.06
% 7.47/2.79  Subsumption          : 0.37
% 7.47/2.79  Abstraction          : 0.08
% 7.47/2.79  MUC search           : 0.00
% 7.47/2.79  Cooper               : 0.00
% 7.47/2.79  Total                : 1.93
% 7.47/2.79  Index Insertion      : 0.00
% 7.47/2.79  Index Deletion       : 0.00
% 7.47/2.79  Index Matching       : 0.00
% 7.47/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
