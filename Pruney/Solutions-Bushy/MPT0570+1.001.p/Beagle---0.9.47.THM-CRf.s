%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0570+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:31 EST 2020

% Result     : Theorem 33.78s
% Output     : CNFRefutation 33.87s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 348 expanded)
%              Number of equality atoms :   12 (  59 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > o_1_4_relat_1 > k2_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(o_1_4_relat_1,type,(
    o_1_4_relat_1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(o_1_4_relat_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_4_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_25] : m1_subset_1(o_1_4_relat_1(A_25),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_144,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_6'(A_72,B_73,C_74),B_73)
      | ~ r2_hidden(A_72,k10_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [B_36,A_35] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    ! [B_75,A_76,C_77] :
      ( ~ v1_xboole_0(B_75)
      | ~ r2_hidden(A_76,k10_relat_1(C_77,B_75))
      | ~ v1_relat_1(C_77) ) ),
    inference(resolution,[status(thm)],[c_144,c_36])).

tff(c_171,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_76,k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_152])).

tff(c_177,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_76,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_40,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden(A_69,B_70)
      | ~ r1_tarski(B_71,B_70)
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(A_69,B_71) ) ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_143,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,k2_relat_1('#skF_8'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_134])).

tff(c_179,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,k2_relat_1('#skF_8'))
      | ~ m1_subset_1(A_69,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_143])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20])).

tff(c_243,plain,(
    ! [A_91,C_92] :
      ( r2_hidden(k4_tarski('#skF_5'(A_91,k2_relat_1(A_91),C_92),C_92),A_91)
      | ~ r2_hidden(C_92,k2_relat_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_260,plain,(
    ! [A_93,C_94] :
      ( ~ v1_xboole_0(A_93)
      | ~ r2_hidden(C_94,k2_relat_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_243,c_36])).

tff(c_442,plain,(
    ! [A_112,A_113] :
      ( ~ v1_xboole_0(A_112)
      | v1_xboole_0(k2_relat_1(A_112))
      | ~ m1_subset_1(A_113,k2_relat_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_447,plain,(
    ! [A_114] :
      ( ~ v1_xboole_0(A_114)
      | v1_xboole_0(k2_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_22,c_442])).

tff(c_34,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_484,plain,(
    ! [A_117] :
      ( k2_relat_1(A_117) = k1_xboole_0
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_447,c_34])).

tff(c_492,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_484])).

tff(c_8,plain,(
    ! [A_6,C_21] :
      ( r2_hidden(k4_tarski('#skF_5'(A_6,k2_relat_1(A_6),C_21),C_21),A_6)
      | ~ r2_hidden(C_21,k2_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_318,plain,(
    ! [A_98,C_99] :
      ( ~ v1_xboole_0(A_98)
      | ~ r2_hidden(C_99,k2_relat_1(k2_relat_1(A_98))) ) ),
    inference(resolution,[status(thm)],[c_8,c_260])).

tff(c_339,plain,(
    ! [A_98,C_21] :
      ( ~ v1_xboole_0(A_98)
      | ~ r2_hidden(C_21,k2_relat_1(k2_relat_1(k2_relat_1(A_98)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_318])).

tff(c_507,plain,(
    ! [C_21] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_21,k2_relat_1(k2_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_339])).

tff(c_532,plain,(
    ! [C_21] : ~ r2_hidden(C_21,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_492,c_55,c_507])).

tff(c_2013,plain,(
    ! [A_177,C_178,B_179,D_180] :
      ( r2_hidden(A_177,k10_relat_1(C_178,B_179))
      | ~ r2_hidden(D_180,B_179)
      | ~ r2_hidden(k4_tarski(A_177,D_180),C_178)
      | ~ r2_hidden(D_180,k2_relat_1(C_178))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_13635,plain,(
    ! [A_370,C_371,B_372,A_373] :
      ( r2_hidden(A_370,k10_relat_1(C_371,B_372))
      | ~ r2_hidden(k4_tarski(A_370,A_373),C_371)
      | ~ r2_hidden(A_373,k2_relat_1(C_371))
      | ~ v1_relat_1(C_371)
      | v1_xboole_0(B_372)
      | ~ m1_subset_1(A_373,B_372) ) ),
    inference(resolution,[status(thm)],[c_32,c_2013])).

tff(c_120217,plain,(
    ! [A_1297,C_1298,B_1299] :
      ( r2_hidden('#skF_5'(A_1297,k2_relat_1(A_1297),C_1298),k10_relat_1(A_1297,B_1299))
      | ~ v1_relat_1(A_1297)
      | v1_xboole_0(B_1299)
      | ~ m1_subset_1(C_1298,B_1299)
      | ~ r2_hidden(C_1298,k2_relat_1(A_1297)) ) ),
    inference(resolution,[status(thm)],[c_8,c_13635])).

tff(c_120534,plain,(
    ! [C_1298] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1298),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_1298,'#skF_7')
      | ~ r2_hidden(C_1298,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_120217])).

tff(c_120580,plain,(
    ! [C_1298] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1298),k1_xboole_0)
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_1298,'#skF_7')
      | ~ r2_hidden(C_1298,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_120534])).

tff(c_120582,plain,(
    ! [C_1300] :
      ( ~ m1_subset_1(C_1300,'#skF_7')
      | ~ r2_hidden(C_1300,k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_532,c_120580])).

tff(c_120871,plain,(
    ! [A_1301] : ~ m1_subset_1(A_1301,'#skF_7') ),
    inference(resolution,[status(thm)],[c_179,c_120582])).

tff(c_120876,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_120871])).

tff(c_120878,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_120881,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_120878,c_34])).

tff(c_120885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_120881])).

%------------------------------------------------------------------------------
