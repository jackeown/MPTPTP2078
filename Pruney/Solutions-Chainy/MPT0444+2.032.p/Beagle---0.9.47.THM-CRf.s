%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:24 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 236 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 650 expanded)
%              Number of equality atoms :   29 ( 157 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r2_hidden('#skF_1'(A_55,B_56,C_57),C_57)
      | r2_hidden('#skF_2'(A_55,B_56,C_57),C_57)
      | k3_xboole_0(A_55,B_56) = C_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_171,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_157])).

tff(c_115,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | r2_hidden('#skF_2'(A_49,B_50,C_51),C_51)
      | k3_xboole_0(A_49,B_50) = C_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_600,plain,(
    ! [A_108,B_109,A_110,B_111] :
      ( r2_hidden('#skF_2'(A_108,B_109,k3_xboole_0(A_110,B_111)),B_111)
      | r2_hidden('#skF_1'(A_108,B_109,k3_xboole_0(A_110,B_111)),B_109)
      | k3_xboole_0(A_110,B_111) = k3_xboole_0(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_634,plain,(
    ! [B_111,B_109,A_110] :
      ( ~ r2_hidden('#skF_2'(B_111,B_109,k3_xboole_0(A_110,B_111)),B_109)
      | r2_hidden('#skF_1'(B_111,B_109,k3_xboole_0(A_110,B_111)),B_109)
      | k3_xboole_0(B_111,B_109) = k3_xboole_0(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_600,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_535,plain,(
    ! [A_101,A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(A_101,k3_xboole_0(A_102,B_103),C_104),A_102)
      | r2_hidden('#skF_2'(A_101,k3_xboole_0(A_102,B_103),C_104),C_104)
      | k3_xboole_0(A_101,k3_xboole_0(A_102,B_103)) = C_104 ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_578,plain,(
    ! [A_102,B_103,B_2,A_1,A_101] :
      ( r2_hidden('#skF_2'(A_101,k3_xboole_0(A_102,B_103),k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_101,k3_xboole_0(A_102,B_103),k3_xboole_0(A_1,B_2)),A_102)
      | k3_xboole_0(A_101,k3_xboole_0(A_102,B_103)) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_535,c_4])).

tff(c_136,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_54),A_52)
      | r2_hidden('#skF_2'(A_52,B_53,C_54),C_54)
      | k3_xboole_0(A_52,B_53) = C_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,(
    ! [A_52,B_53,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_52,B_53,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_52,B_53,k3_xboole_0(A_1,B_2)),A_52)
      | k3_xboole_0(A_52,B_53) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_840,plain,(
    ! [A_131,B_132,A_133,B_134] :
      ( r2_hidden('#skF_2'(A_131,B_132,k3_xboole_0(A_133,B_134)),k3_xboole_0(A_133,B_134))
      | k3_xboole_0(A_133,B_134) = k3_xboole_0(A_131,B_132)
      | ~ r2_hidden('#skF_1'(A_131,B_132,k3_xboole_0(A_133,B_134)),B_134)
      | ~ r2_hidden('#skF_1'(A_131,B_132,k3_xboole_0(A_133,B_134)),A_133) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_6867,plain,(
    ! [A_546,B_547,A_548,B_549] :
      ( r2_hidden('#skF_2'(A_546,B_547,k3_xboole_0(A_548,B_549)),B_549)
      | k3_xboole_0(A_548,B_549) = k3_xboole_0(A_546,B_547)
      | ~ r2_hidden('#skF_1'(A_546,B_547,k3_xboole_0(A_548,B_549)),B_549)
      | ~ r2_hidden('#skF_1'(A_546,B_547,k3_xboole_0(A_548,B_549)),A_548) ) ),
    inference(resolution,[status(thm)],[c_840,c_4])).

tff(c_7028,plain,(
    ! [A_550,B_551,A_552] :
      ( ~ r2_hidden('#skF_1'(A_550,B_551,k3_xboole_0(A_552,A_550)),A_552)
      | r2_hidden('#skF_2'(A_550,B_551,k3_xboole_0(A_552,A_550)),A_550)
      | k3_xboole_0(A_552,A_550) = k3_xboole_0(A_550,B_551) ) ),
    inference(resolution,[status(thm)],[c_156,c_6867])).

tff(c_7155,plain,(
    ! [B_2,A_102,B_103] :
      ( r2_hidden('#skF_2'(B_2,k3_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_2)),B_2)
      | k3_xboole_0(B_2,k3_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_2) ) ),
    inference(resolution,[status(thm)],[c_578,c_7028])).

tff(c_252,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_1'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden('#skF_2'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden('#skF_2'(A_77,B_78,C_79),A_77)
      | k3_xboole_0(A_77,B_78) = C_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_277,plain,(
    ! [C_80,B_81] :
      ( ~ r2_hidden('#skF_2'(C_80,B_81,C_80),B_81)
      | r2_hidden('#skF_1'(C_80,B_81,C_80),B_81)
      | k3_xboole_0(C_80,B_81) = C_80 ) ),
    inference(resolution,[status(thm)],[c_16,c_252])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_322,plain,(
    ! [B_85] :
      ( ~ r2_hidden('#skF_2'(B_85,B_85,B_85),B_85)
      | k3_xboole_0(B_85,B_85) = B_85 ) ),
    inference(resolution,[status(thm)],[c_277,c_8])).

tff(c_339,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_171,c_322])).

tff(c_206,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66,C_67),C_67)
      | ~ r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | ~ r2_hidden('#skF_2'(A_65,B_66,C_67),A_65)
      | k3_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1659,plain,(
    ! [A_202,B_203,A_204,B_205] :
      ( ~ r2_hidden('#skF_2'(A_202,B_203,k3_xboole_0(A_204,B_205)),B_203)
      | ~ r2_hidden('#skF_2'(A_202,B_203,k3_xboole_0(A_204,B_205)),A_202)
      | k3_xboole_0(A_204,B_205) = k3_xboole_0(A_202,B_203)
      | ~ r2_hidden('#skF_1'(A_202,B_203,k3_xboole_0(A_204,B_205)),B_205)
      | ~ r2_hidden('#skF_1'(A_202,B_203,k3_xboole_0(A_204,B_205)),A_204) ) ),
    inference(resolution,[status(thm)],[c_2,c_206])).

tff(c_7606,plain,(
    ! [A_573,A_574,B_575] :
      ( ~ r2_hidden('#skF_2'(A_573,k3_xboole_0(A_574,B_575),k3_xboole_0(A_574,B_575)),A_573)
      | ~ r2_hidden('#skF_1'(A_573,k3_xboole_0(A_574,B_575),k3_xboole_0(A_574,B_575)),B_575)
      | ~ r2_hidden('#skF_1'(A_573,k3_xboole_0(A_574,B_575),k3_xboole_0(A_574,B_575)),A_574)
      | k3_xboole_0(A_573,k3_xboole_0(A_574,B_575)) = k3_xboole_0(A_574,B_575) ) ),
    inference(resolution,[status(thm)],[c_171,c_1659])).

tff(c_7703,plain,(
    ! [A_573,B_2] :
      ( ~ r2_hidden('#skF_2'(A_573,B_2,k3_xboole_0(B_2,B_2)),A_573)
      | ~ r2_hidden('#skF_1'(A_573,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_573,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | k3_xboole_0(A_573,k3_xboole_0(B_2,B_2)) = k3_xboole_0(B_2,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_7606])).

tff(c_7809,plain,(
    ! [A_579,B_580] :
      ( ~ r2_hidden('#skF_2'(A_579,B_580,B_580),A_579)
      | ~ r2_hidden('#skF_1'(A_579,B_580,B_580),B_580)
      | ~ r2_hidden('#skF_1'(A_579,B_580,B_580),B_580)
      | k3_xboole_0(A_579,B_580) = B_580 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_339,c_339,c_339,c_339,c_339,c_339,c_7703])).

tff(c_7972,plain,(
    ! [B_581,A_582] :
      ( ~ r2_hidden('#skF_1'(B_581,k3_xboole_0(A_582,B_581),k3_xboole_0(A_582,B_581)),k3_xboole_0(A_582,B_581))
      | k3_xboole_0(B_581,k3_xboole_0(A_582,B_581)) = k3_xboole_0(A_582,B_581) ) ),
    inference(resolution,[status(thm)],[c_7155,c_7809])).

tff(c_8159,plain,(
    ! [B_588,A_589] :
      ( ~ r2_hidden('#skF_2'(B_588,k3_xboole_0(A_589,B_588),k3_xboole_0(A_589,B_588)),k3_xboole_0(A_589,B_588))
      | k3_xboole_0(B_588,k3_xboole_0(A_589,B_588)) = k3_xboole_0(A_589,B_588) ) ),
    inference(resolution,[status(thm)],[c_634,c_7972])).

tff(c_8258,plain,(
    ! [A_590,A_591] : k3_xboole_0(A_590,k3_xboole_0(A_591,A_590)) = k3_xboole_0(A_591,A_590) ),
    inference(resolution,[status(thm)],[c_171,c_8159])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9352,plain,(
    ! [A_591,A_590] : r1_tarski(k3_xboole_0(A_591,A_590),A_590) ),
    inference(superposition,[status(thm),theory(equality)],[c_8258,c_20])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k2_relat_1(A_18),k2_relat_1(B_20))
      | ~ r1_tarski(A_18,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,k3_xboole_0(B_40,C_41))
      | ~ r1_tarski(A_39,C_41)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_34])).

tff(c_77,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_83,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20,c_80])).

tff(c_92,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_92])).

tff(c_97,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_101,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_97])).

tff(c_104,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101])).

tff(c_105,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_108,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_108])).

tff(c_113,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_9708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9352,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.73/3.01  
% 8.73/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.73/3.01  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.73/3.01  
% 8.73/3.01  %Foreground sorts:
% 8.73/3.01  
% 8.73/3.01  
% 8.73/3.01  %Background operators:
% 8.73/3.01  
% 8.73/3.01  
% 8.73/3.01  %Foreground operators:
% 8.73/3.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.73/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.73/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.73/3.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.73/3.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.73/3.01  tff('#skF_3', type, '#skF_3': $i).
% 8.73/3.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.73/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.73/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.73/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.73/3.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.73/3.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.73/3.01  
% 8.73/3.03  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.73/3.03  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.73/3.03  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 8.73/3.03  tff(f_50, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 8.73/3.03  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.73/3.03  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 8.73/3.03  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_157, plain, (![A_55, B_56, C_57]: (~r2_hidden('#skF_1'(A_55, B_56, C_57), C_57) | r2_hidden('#skF_2'(A_55, B_56, C_57), C_57) | k3_xboole_0(A_55, B_56)=C_57)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_171, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_157])).
% 8.73/3.03  tff(c_115, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_1'(A_49, B_50, C_51), B_50) | r2_hidden('#skF_2'(A_49, B_50, C_51), C_51) | k3_xboole_0(A_49, B_50)=C_51)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_600, plain, (![A_108, B_109, A_110, B_111]: (r2_hidden('#skF_2'(A_108, B_109, k3_xboole_0(A_110, B_111)), B_111) | r2_hidden('#skF_1'(A_108, B_109, k3_xboole_0(A_110, B_111)), B_109) | k3_xboole_0(A_110, B_111)=k3_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_115, c_4])).
% 8.73/3.03  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_634, plain, (![B_111, B_109, A_110]: (~r2_hidden('#skF_2'(B_111, B_109, k3_xboole_0(A_110, B_111)), B_109) | r2_hidden('#skF_1'(B_111, B_109, k3_xboole_0(A_110, B_111)), B_109) | k3_xboole_0(B_111, B_109)=k3_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_600, c_10])).
% 8.73/3.03  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_535, plain, (![A_101, A_102, B_103, C_104]: (r2_hidden('#skF_1'(A_101, k3_xboole_0(A_102, B_103), C_104), A_102) | r2_hidden('#skF_2'(A_101, k3_xboole_0(A_102, B_103), C_104), C_104) | k3_xboole_0(A_101, k3_xboole_0(A_102, B_103))=C_104)), inference(resolution, [status(thm)], [c_115, c_6])).
% 8.73/3.03  tff(c_578, plain, (![A_102, B_103, B_2, A_1, A_101]: (r2_hidden('#skF_2'(A_101, k3_xboole_0(A_102, B_103), k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_101, k3_xboole_0(A_102, B_103), k3_xboole_0(A_1, B_2)), A_102) | k3_xboole_0(A_101, k3_xboole_0(A_102, B_103))=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_535, c_4])).
% 8.73/3.03  tff(c_136, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_1'(A_52, B_53, C_54), A_52) | r2_hidden('#skF_2'(A_52, B_53, C_54), C_54) | k3_xboole_0(A_52, B_53)=C_54)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_156, plain, (![A_52, B_53, A_1, B_2]: (r2_hidden('#skF_2'(A_52, B_53, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_52, B_53, k3_xboole_0(A_1, B_2)), A_52) | k3_xboole_0(A_52, B_53)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_136, c_4])).
% 8.73/3.03  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_840, plain, (![A_131, B_132, A_133, B_134]: (r2_hidden('#skF_2'(A_131, B_132, k3_xboole_0(A_133, B_134)), k3_xboole_0(A_133, B_134)) | k3_xboole_0(A_133, B_134)=k3_xboole_0(A_131, B_132) | ~r2_hidden('#skF_1'(A_131, B_132, k3_xboole_0(A_133, B_134)), B_134) | ~r2_hidden('#skF_1'(A_131, B_132, k3_xboole_0(A_133, B_134)), A_133))), inference(resolution, [status(thm)], [c_2, c_157])).
% 8.73/3.03  tff(c_6867, plain, (![A_546, B_547, A_548, B_549]: (r2_hidden('#skF_2'(A_546, B_547, k3_xboole_0(A_548, B_549)), B_549) | k3_xboole_0(A_548, B_549)=k3_xboole_0(A_546, B_547) | ~r2_hidden('#skF_1'(A_546, B_547, k3_xboole_0(A_548, B_549)), B_549) | ~r2_hidden('#skF_1'(A_546, B_547, k3_xboole_0(A_548, B_549)), A_548))), inference(resolution, [status(thm)], [c_840, c_4])).
% 8.73/3.03  tff(c_7028, plain, (![A_550, B_551, A_552]: (~r2_hidden('#skF_1'(A_550, B_551, k3_xboole_0(A_552, A_550)), A_552) | r2_hidden('#skF_2'(A_550, B_551, k3_xboole_0(A_552, A_550)), A_550) | k3_xboole_0(A_552, A_550)=k3_xboole_0(A_550, B_551))), inference(resolution, [status(thm)], [c_156, c_6867])).
% 8.73/3.03  tff(c_7155, plain, (![B_2, A_102, B_103]: (r2_hidden('#skF_2'(B_2, k3_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_2)), B_2) | k3_xboole_0(B_2, k3_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_2))), inference(resolution, [status(thm)], [c_578, c_7028])).
% 8.73/3.03  tff(c_252, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_1'(A_77, B_78, C_79), B_78) | ~r2_hidden('#skF_2'(A_77, B_78, C_79), B_78) | ~r2_hidden('#skF_2'(A_77, B_78, C_79), A_77) | k3_xboole_0(A_77, B_78)=C_79)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_277, plain, (![C_80, B_81]: (~r2_hidden('#skF_2'(C_80, B_81, C_80), B_81) | r2_hidden('#skF_1'(C_80, B_81, C_80), B_81) | k3_xboole_0(C_80, B_81)=C_80)), inference(resolution, [status(thm)], [c_16, c_252])).
% 8.73/3.03  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_322, plain, (![B_85]: (~r2_hidden('#skF_2'(B_85, B_85, B_85), B_85) | k3_xboole_0(B_85, B_85)=B_85)), inference(resolution, [status(thm)], [c_277, c_8])).
% 8.73/3.03  tff(c_339, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_171, c_322])).
% 8.73/3.03  tff(c_206, plain, (![A_65, B_66, C_67]: (~r2_hidden('#skF_1'(A_65, B_66, C_67), C_67) | ~r2_hidden('#skF_2'(A_65, B_66, C_67), B_66) | ~r2_hidden('#skF_2'(A_65, B_66, C_67), A_65) | k3_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.73/3.03  tff(c_1659, plain, (![A_202, B_203, A_204, B_205]: (~r2_hidden('#skF_2'(A_202, B_203, k3_xboole_0(A_204, B_205)), B_203) | ~r2_hidden('#skF_2'(A_202, B_203, k3_xboole_0(A_204, B_205)), A_202) | k3_xboole_0(A_204, B_205)=k3_xboole_0(A_202, B_203) | ~r2_hidden('#skF_1'(A_202, B_203, k3_xboole_0(A_204, B_205)), B_205) | ~r2_hidden('#skF_1'(A_202, B_203, k3_xboole_0(A_204, B_205)), A_204))), inference(resolution, [status(thm)], [c_2, c_206])).
% 8.73/3.03  tff(c_7606, plain, (![A_573, A_574, B_575]: (~r2_hidden('#skF_2'(A_573, k3_xboole_0(A_574, B_575), k3_xboole_0(A_574, B_575)), A_573) | ~r2_hidden('#skF_1'(A_573, k3_xboole_0(A_574, B_575), k3_xboole_0(A_574, B_575)), B_575) | ~r2_hidden('#skF_1'(A_573, k3_xboole_0(A_574, B_575), k3_xboole_0(A_574, B_575)), A_574) | k3_xboole_0(A_573, k3_xboole_0(A_574, B_575))=k3_xboole_0(A_574, B_575))), inference(resolution, [status(thm)], [c_171, c_1659])).
% 8.73/3.03  tff(c_7703, plain, (![A_573, B_2]: (~r2_hidden('#skF_2'(A_573, B_2, k3_xboole_0(B_2, B_2)), A_573) | ~r2_hidden('#skF_1'(A_573, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | ~r2_hidden('#skF_1'(A_573, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | k3_xboole_0(A_573, k3_xboole_0(B_2, B_2))=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_339, c_7606])).
% 8.73/3.03  tff(c_7809, plain, (![A_579, B_580]: (~r2_hidden('#skF_2'(A_579, B_580, B_580), A_579) | ~r2_hidden('#skF_1'(A_579, B_580, B_580), B_580) | ~r2_hidden('#skF_1'(A_579, B_580, B_580), B_580) | k3_xboole_0(A_579, B_580)=B_580)), inference(demodulation, [status(thm), theory('equality')], [c_339, c_339, c_339, c_339, c_339, c_339, c_339, c_7703])).
% 8.73/3.03  tff(c_7972, plain, (![B_581, A_582]: (~r2_hidden('#skF_1'(B_581, k3_xboole_0(A_582, B_581), k3_xboole_0(A_582, B_581)), k3_xboole_0(A_582, B_581)) | k3_xboole_0(B_581, k3_xboole_0(A_582, B_581))=k3_xboole_0(A_582, B_581))), inference(resolution, [status(thm)], [c_7155, c_7809])).
% 8.73/3.03  tff(c_8159, plain, (![B_588, A_589]: (~r2_hidden('#skF_2'(B_588, k3_xboole_0(A_589, B_588), k3_xboole_0(A_589, B_588)), k3_xboole_0(A_589, B_588)) | k3_xboole_0(B_588, k3_xboole_0(A_589, B_588))=k3_xboole_0(A_589, B_588))), inference(resolution, [status(thm)], [c_634, c_7972])).
% 8.73/3.03  tff(c_8258, plain, (![A_590, A_591]: (k3_xboole_0(A_590, k3_xboole_0(A_591, A_590))=k3_xboole_0(A_591, A_590))), inference(resolution, [status(thm)], [c_171, c_8159])).
% 8.73/3.03  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.73/3.03  tff(c_9352, plain, (![A_591, A_590]: (r1_tarski(k3_xboole_0(A_591, A_590), A_590))), inference(superposition, [status(thm), theory('equality')], [c_8258, c_20])).
% 8.73/3.03  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.73/3.03  tff(c_28, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.73/3.03  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.73/3.03  tff(c_30, plain, (![A_18, B_20]: (r1_tarski(k2_relat_1(A_18), k2_relat_1(B_20)) | ~r1_tarski(A_18, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.73/3.03  tff(c_70, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, k3_xboole_0(B_40, C_41)) | ~r1_tarski(A_39, C_41) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.73/3.03  tff(c_34, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.73/3.03  tff(c_74, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_34])).
% 8.73/3.03  tff(c_77, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 8.73/3.03  tff(c_80, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_77])).
% 8.73/3.03  tff(c_83, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20, c_80])).
% 8.73/3.03  tff(c_92, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_83])).
% 8.73/3.03  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_92])).
% 8.73/3.03  tff(c_97, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 8.73/3.03  tff(c_101, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_97])).
% 8.73/3.03  tff(c_104, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_101])).
% 8.73/3.03  tff(c_105, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_104])).
% 8.73/3.03  tff(c_108, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_105])).
% 8.73/3.03  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_108])).
% 8.73/3.03  tff(c_113, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_104])).
% 8.73/3.03  tff(c_9708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9352, c_113])).
% 8.73/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.73/3.03  
% 8.73/3.03  Inference rules
% 8.73/3.03  ----------------------
% 8.73/3.03  #Ref     : 0
% 8.73/3.03  #Sup     : 2035
% 8.73/3.03  #Fact    : 0
% 8.73/3.03  #Define  : 0
% 8.73/3.03  #Split   : 2
% 8.73/3.03  #Chain   : 0
% 8.73/3.03  #Close   : 0
% 8.73/3.03  
% 8.73/3.03  Ordering : KBO
% 8.73/3.03  
% 8.73/3.03  Simplification rules
% 8.73/3.03  ----------------------
% 8.73/3.03  #Subsume      : 1007
% 8.73/3.03  #Demod        : 2232
% 8.73/3.03  #Tautology    : 224
% 8.73/3.03  #SimpNegUnit  : 0
% 8.73/3.03  #BackRed      : 3
% 8.73/3.03  
% 8.73/3.03  #Partial instantiations: 0
% 8.73/3.03  #Strategies tried      : 1
% 8.73/3.03  
% 8.73/3.03  Timing (in seconds)
% 8.73/3.03  ----------------------
% 8.73/3.03  Preprocessing        : 0.30
% 8.73/3.03  Parsing              : 0.16
% 8.73/3.03  CNF conversion       : 0.02
% 8.73/3.03  Main loop            : 1.98
% 8.73/3.03  Inferencing          : 0.70
% 8.73/3.03  Reduction            : 0.45
% 8.73/3.03  Demodulation         : 0.32
% 8.73/3.03  BG Simplification    : 0.06
% 8.73/3.03  Subsumption          : 0.65
% 8.73/3.03  Abstraction          : 0.15
% 8.73/3.03  MUC search           : 0.00
% 8.73/3.03  Cooper               : 0.00
% 8.73/3.03  Total                : 2.32
% 8.73/3.03  Index Insertion      : 0.00
% 8.73/3.03  Index Deletion       : 0.00
% 8.73/3.03  Index Matching       : 0.00
% 8.73/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
