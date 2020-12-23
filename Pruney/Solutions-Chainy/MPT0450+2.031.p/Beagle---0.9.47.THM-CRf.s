%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 10.78s
% Output     : CNFRefutation 10.78s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 236 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 649 expanded)
%              Number of equality atoms :   31 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_165,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r2_hidden('#skF_1'(A_59,B_60,C_61),C_61)
      | r2_hidden('#skF_2'(A_59,B_60,C_61),C_61)
      | k3_xboole_0(A_59,B_60) = C_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_178,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_144,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden('#skF_1'(A_56,B_57,C_58),B_57)
      | r2_hidden('#skF_2'(A_56,B_57,C_58),C_58)
      | k3_xboole_0(A_56,B_57) = C_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_716,plain,(
    ! [A_123,B_124,A_125,B_126] :
      ( r2_hidden('#skF_2'(A_123,B_124,k3_xboole_0(A_125,B_126)),B_126)
      | r2_hidden('#skF_1'(A_123,B_124,k3_xboole_0(A_125,B_126)),B_124)
      | k3_xboole_0(A_125,B_126) = k3_xboole_0(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_750,plain,(
    ! [B_126,B_124,A_125] :
      ( ~ r2_hidden('#skF_2'(B_126,B_124,k3_xboole_0(A_125,B_126)),B_124)
      | r2_hidden('#skF_1'(B_126,B_124,k3_xboole_0(A_125,B_126)),B_124)
      | k3_xboole_0(B_126,B_124) = k3_xboole_0(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_716,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_755,plain,(
    ! [B_126,B_2,A_1,A_123,A_125] :
      ( r2_hidden('#skF_1'(A_123,k3_xboole_0(A_1,B_2),k3_xboole_0(A_125,B_126)),A_1)
      | r2_hidden('#skF_2'(A_123,k3_xboole_0(A_1,B_2),k3_xboole_0(A_125,B_126)),B_126)
      | k3_xboole_0(A_125,B_126) = k3_xboole_0(A_123,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_716,c_6])).

tff(c_123,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_1'(A_53,B_54,C_55),A_53)
      | r2_hidden('#skF_2'(A_53,B_54,C_55),C_55)
      | k3_xboole_0(A_53,B_54) = C_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_53,B_54,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_53,B_54,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_53,B_54,k3_xboole_0(A_1,B_2)),A_53)
      | k3_xboole_0(A_53,B_54) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_848,plain,(
    ! [A_135,B_136,A_137,B_138] :
      ( r2_hidden('#skF_2'(A_135,B_136,k3_xboole_0(A_137,B_138)),k3_xboole_0(A_137,B_138))
      | k3_xboole_0(A_137,B_138) = k3_xboole_0(A_135,B_136)
      | ~ r2_hidden('#skF_1'(A_135,B_136,k3_xboole_0(A_137,B_138)),B_138)
      | ~ r2_hidden('#skF_1'(A_135,B_136,k3_xboole_0(A_137,B_138)),A_137) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_6804,plain,(
    ! [A_554,B_555,A_556,B_557] :
      ( r2_hidden('#skF_2'(A_554,B_555,k3_xboole_0(A_556,B_557)),B_557)
      | k3_xboole_0(A_556,B_557) = k3_xboole_0(A_554,B_555)
      | ~ r2_hidden('#skF_1'(A_554,B_555,k3_xboole_0(A_556,B_557)),B_557)
      | ~ r2_hidden('#skF_1'(A_554,B_555,k3_xboole_0(A_556,B_557)),A_556) ) ),
    inference(resolution,[status(thm)],[c_848,c_4])).

tff(c_7277,plain,(
    ! [A_571,B_572,A_573] :
      ( ~ r2_hidden('#skF_1'(A_571,B_572,k3_xboole_0(A_573,A_571)),A_573)
      | r2_hidden('#skF_2'(A_571,B_572,k3_xboole_0(A_573,A_571)),A_571)
      | k3_xboole_0(A_573,A_571) = k3_xboole_0(A_571,B_572) ) ),
    inference(resolution,[status(thm)],[c_143,c_6804])).

tff(c_7410,plain,(
    ! [B_126,A_1,B_2] :
      ( r2_hidden('#skF_2'(B_126,k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_126)),B_126)
      | k3_xboole_0(B_126,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_126) ) ),
    inference(resolution,[status(thm)],[c_755,c_7277])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k3_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_165])).

tff(c_260,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),A_81)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),A_81)
      | k3_xboole_0(A_81,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_285,plain,(
    ! [A_84,C_85] :
      ( ~ r2_hidden('#skF_2'(A_84,C_85,C_85),A_84)
      | r2_hidden('#skF_1'(A_84,C_85,C_85),A_84)
      | k3_xboole_0(A_84,C_85) = C_85 ) ),
    inference(resolution,[status(thm)],[c_18,c_260])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_330,plain,(
    ! [A_89] :
      ( ~ r2_hidden('#skF_2'(A_89,A_89,A_89),A_89)
      | k3_xboole_0(A_89,A_89) = A_89 ) ),
    inference(resolution,[status(thm)],[c_285,c_8])).

tff(c_347,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_179,c_330])).

tff(c_180,plain,(
    ! [A_59,B_60,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_59,B_60,k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2))
      | k3_xboole_0(A_59,B_60) = k3_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_59,B_60,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_59,B_60,k3_xboole_0(A_1,B_2)),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_214,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r2_hidden('#skF_1'(A_69,B_70,C_71),C_71)
      | ~ r2_hidden('#skF_2'(A_69,B_70,C_71),B_70)
      | ~ r2_hidden('#skF_2'(A_69,B_70,C_71),A_69)
      | k3_xboole_0(A_69,B_70) = C_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1667,plain,(
    ! [A_206,B_207,A_208,B_209] :
      ( ~ r2_hidden('#skF_2'(A_206,B_207,k3_xboole_0(A_208,B_209)),B_207)
      | ~ r2_hidden('#skF_2'(A_206,B_207,k3_xboole_0(A_208,B_209)),A_206)
      | k3_xboole_0(A_208,B_209) = k3_xboole_0(A_206,B_207)
      | ~ r2_hidden('#skF_1'(A_206,B_207,k3_xboole_0(A_208,B_209)),B_209)
      | ~ r2_hidden('#skF_1'(A_206,B_207,k3_xboole_0(A_208,B_209)),A_208) ) ),
    inference(resolution,[status(thm)],[c_2,c_214])).

tff(c_8299,plain,(
    ! [A_648,A_649,B_650] :
      ( ~ r2_hidden('#skF_2'(A_648,k3_xboole_0(A_649,B_650),k3_xboole_0(A_649,B_650)),A_648)
      | k3_xboole_0(A_648,k3_xboole_0(A_649,B_650)) = k3_xboole_0(A_649,B_650)
      | ~ r2_hidden('#skF_1'(A_648,k3_xboole_0(A_649,B_650),k3_xboole_0(A_649,B_650)),B_650)
      | ~ r2_hidden('#skF_1'(A_648,k3_xboole_0(A_649,B_650),k3_xboole_0(A_649,B_650)),A_649) ) ),
    inference(resolution,[status(thm)],[c_180,c_1667])).

tff(c_8402,plain,(
    ! [A_648,B_2] :
      ( ~ r2_hidden('#skF_2'(A_648,B_2,k3_xboole_0(B_2,B_2)),A_648)
      | k3_xboole_0(A_648,k3_xboole_0(B_2,B_2)) = k3_xboole_0(B_2,B_2)
      | ~ r2_hidden('#skF_1'(A_648,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_648,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_8299])).

tff(c_8476,plain,(
    ! [A_651,B_652] :
      ( ~ r2_hidden('#skF_2'(A_651,B_652,B_652),A_651)
      | k3_xboole_0(A_651,B_652) = B_652
      | ~ r2_hidden('#skF_1'(A_651,B_652,B_652),B_652)
      | ~ r2_hidden('#skF_1'(A_651,B_652,B_652),B_652) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_347,c_347,c_347,c_347,c_347,c_8402])).

tff(c_8647,plain,(
    ! [B_653,A_654] :
      ( ~ r2_hidden('#skF_1'(B_653,k3_xboole_0(A_654,B_653),k3_xboole_0(A_654,B_653)),k3_xboole_0(A_654,B_653))
      | k3_xboole_0(B_653,k3_xboole_0(A_654,B_653)) = k3_xboole_0(A_654,B_653) ) ),
    inference(resolution,[status(thm)],[c_7410,c_8476])).

tff(c_8832,plain,(
    ! [B_661,A_662] :
      ( ~ r2_hidden('#skF_2'(B_661,k3_xboole_0(A_662,B_661),k3_xboole_0(A_662,B_661)),k3_xboole_0(A_662,B_661))
      | k3_xboole_0(B_661,k3_xboole_0(A_662,B_661)) = k3_xboole_0(A_662,B_661) ) ),
    inference(resolution,[status(thm)],[c_750,c_8647])).

tff(c_8931,plain,(
    ! [A_663,A_664] : k3_xboole_0(A_663,k3_xboole_0(A_664,A_663)) = k3_xboole_0(A_664,A_663) ),
    inference(resolution,[status(thm)],[c_178,c_8832])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10250,plain,(
    ! [A_664,A_663] : r1_tarski(k3_xboole_0(A_664,A_663),A_663) ),
    inference(superposition,[status(thm),theory(equality)],[c_8931,c_20])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k3_xboole_0(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k3_relat_1(A_21),k3_relat_1(B_23))
      | ~ r1_tarski(A_21,B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k3_xboole_0(B_46,C_47))
      | ~ r1_tarski(A_45,C_47)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_79,c_34])).

tff(c_85,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_88,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_91,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20,c_88])).

tff(c_100,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_105,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_109,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_112,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_109])).

tff(c_113,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_116,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_121,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_10677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10250,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.78/3.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.78/3.52  
% 10.78/3.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.78/3.52  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 10.78/3.52  
% 10.78/3.52  %Foreground sorts:
% 10.78/3.52  
% 10.78/3.52  
% 10.78/3.52  %Background operators:
% 10.78/3.52  
% 10.78/3.52  
% 10.78/3.52  %Foreground operators:
% 10.78/3.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.78/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.78/3.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.78/3.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 10.78/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.78/3.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.78/3.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.78/3.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.78/3.52  tff('#skF_3', type, '#skF_3': $i).
% 10.78/3.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.78/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.78/3.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.78/3.52  tff('#skF_4', type, '#skF_4': $i).
% 10.78/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.78/3.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.78/3.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.78/3.52  
% 10.78/3.54  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.78/3.54  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.78/3.54  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 10.78/3.54  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 10.78/3.54  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 10.78/3.54  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.78/3.54  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_165, plain, (![A_59, B_60, C_61]: (~r2_hidden('#skF_1'(A_59, B_60, C_61), C_61) | r2_hidden('#skF_2'(A_59, B_60, C_61), C_61) | k3_xboole_0(A_59, B_60)=C_61)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_178, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_165])).
% 10.78/3.54  tff(c_144, plain, (![A_56, B_57, C_58]: (r2_hidden('#skF_1'(A_56, B_57, C_58), B_57) | r2_hidden('#skF_2'(A_56, B_57, C_58), C_58) | k3_xboole_0(A_56, B_57)=C_58)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_716, plain, (![A_123, B_124, A_125, B_126]: (r2_hidden('#skF_2'(A_123, B_124, k3_xboole_0(A_125, B_126)), B_126) | r2_hidden('#skF_1'(A_123, B_124, k3_xboole_0(A_125, B_126)), B_124) | k3_xboole_0(A_125, B_126)=k3_xboole_0(A_123, B_124))), inference(resolution, [status(thm)], [c_144, c_4])).
% 10.78/3.54  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_750, plain, (![B_126, B_124, A_125]: (~r2_hidden('#skF_2'(B_126, B_124, k3_xboole_0(A_125, B_126)), B_124) | r2_hidden('#skF_1'(B_126, B_124, k3_xboole_0(A_125, B_126)), B_124) | k3_xboole_0(B_126, B_124)=k3_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_716, c_10])).
% 10.78/3.54  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_755, plain, (![B_126, B_2, A_1, A_123, A_125]: (r2_hidden('#skF_1'(A_123, k3_xboole_0(A_1, B_2), k3_xboole_0(A_125, B_126)), A_1) | r2_hidden('#skF_2'(A_123, k3_xboole_0(A_1, B_2), k3_xboole_0(A_125, B_126)), B_126) | k3_xboole_0(A_125, B_126)=k3_xboole_0(A_123, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_716, c_6])).
% 10.78/3.54  tff(c_123, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_1'(A_53, B_54, C_55), A_53) | r2_hidden('#skF_2'(A_53, B_54, C_55), C_55) | k3_xboole_0(A_53, B_54)=C_55)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_143, plain, (![A_53, B_54, A_1, B_2]: (r2_hidden('#skF_2'(A_53, B_54, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_53, B_54, k3_xboole_0(A_1, B_2)), A_53) | k3_xboole_0(A_53, B_54)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_123, c_4])).
% 10.78/3.54  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_848, plain, (![A_135, B_136, A_137, B_138]: (r2_hidden('#skF_2'(A_135, B_136, k3_xboole_0(A_137, B_138)), k3_xboole_0(A_137, B_138)) | k3_xboole_0(A_137, B_138)=k3_xboole_0(A_135, B_136) | ~r2_hidden('#skF_1'(A_135, B_136, k3_xboole_0(A_137, B_138)), B_138) | ~r2_hidden('#skF_1'(A_135, B_136, k3_xboole_0(A_137, B_138)), A_137))), inference(resolution, [status(thm)], [c_2, c_165])).
% 10.78/3.54  tff(c_6804, plain, (![A_554, B_555, A_556, B_557]: (r2_hidden('#skF_2'(A_554, B_555, k3_xboole_0(A_556, B_557)), B_557) | k3_xboole_0(A_556, B_557)=k3_xboole_0(A_554, B_555) | ~r2_hidden('#skF_1'(A_554, B_555, k3_xboole_0(A_556, B_557)), B_557) | ~r2_hidden('#skF_1'(A_554, B_555, k3_xboole_0(A_556, B_557)), A_556))), inference(resolution, [status(thm)], [c_848, c_4])).
% 10.78/3.54  tff(c_7277, plain, (![A_571, B_572, A_573]: (~r2_hidden('#skF_1'(A_571, B_572, k3_xboole_0(A_573, A_571)), A_573) | r2_hidden('#skF_2'(A_571, B_572, k3_xboole_0(A_573, A_571)), A_571) | k3_xboole_0(A_573, A_571)=k3_xboole_0(A_571, B_572))), inference(resolution, [status(thm)], [c_143, c_6804])).
% 10.78/3.54  tff(c_7410, plain, (![B_126, A_1, B_2]: (r2_hidden('#skF_2'(B_126, k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_126)), B_126) | k3_xboole_0(B_126, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_126))), inference(resolution, [status(thm)], [c_755, c_7277])).
% 10.78/3.54  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_179, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k3_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_165])).
% 10.78/3.54  tff(c_260, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), A_81) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), B_82) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), A_81) | k3_xboole_0(A_81, B_82)=C_83)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_285, plain, (![A_84, C_85]: (~r2_hidden('#skF_2'(A_84, C_85, C_85), A_84) | r2_hidden('#skF_1'(A_84, C_85, C_85), A_84) | k3_xboole_0(A_84, C_85)=C_85)), inference(resolution, [status(thm)], [c_18, c_260])).
% 10.78/3.54  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_330, plain, (![A_89]: (~r2_hidden('#skF_2'(A_89, A_89, A_89), A_89) | k3_xboole_0(A_89, A_89)=A_89)), inference(resolution, [status(thm)], [c_285, c_8])).
% 10.78/3.54  tff(c_347, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_179, c_330])).
% 10.78/3.54  tff(c_180, plain, (![A_59, B_60, A_1, B_2]: (r2_hidden('#skF_2'(A_59, B_60, k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2)) | k3_xboole_0(A_59, B_60)=k3_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_59, B_60, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden('#skF_1'(A_59, B_60, k3_xboole_0(A_1, B_2)), A_1))), inference(resolution, [status(thm)], [c_2, c_165])).
% 10.78/3.54  tff(c_214, plain, (![A_69, B_70, C_71]: (~r2_hidden('#skF_1'(A_69, B_70, C_71), C_71) | ~r2_hidden('#skF_2'(A_69, B_70, C_71), B_70) | ~r2_hidden('#skF_2'(A_69, B_70, C_71), A_69) | k3_xboole_0(A_69, B_70)=C_71)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.54  tff(c_1667, plain, (![A_206, B_207, A_208, B_209]: (~r2_hidden('#skF_2'(A_206, B_207, k3_xboole_0(A_208, B_209)), B_207) | ~r2_hidden('#skF_2'(A_206, B_207, k3_xboole_0(A_208, B_209)), A_206) | k3_xboole_0(A_208, B_209)=k3_xboole_0(A_206, B_207) | ~r2_hidden('#skF_1'(A_206, B_207, k3_xboole_0(A_208, B_209)), B_209) | ~r2_hidden('#skF_1'(A_206, B_207, k3_xboole_0(A_208, B_209)), A_208))), inference(resolution, [status(thm)], [c_2, c_214])).
% 10.78/3.54  tff(c_8299, plain, (![A_648, A_649, B_650]: (~r2_hidden('#skF_2'(A_648, k3_xboole_0(A_649, B_650), k3_xboole_0(A_649, B_650)), A_648) | k3_xboole_0(A_648, k3_xboole_0(A_649, B_650))=k3_xboole_0(A_649, B_650) | ~r2_hidden('#skF_1'(A_648, k3_xboole_0(A_649, B_650), k3_xboole_0(A_649, B_650)), B_650) | ~r2_hidden('#skF_1'(A_648, k3_xboole_0(A_649, B_650), k3_xboole_0(A_649, B_650)), A_649))), inference(resolution, [status(thm)], [c_180, c_1667])).
% 10.78/3.54  tff(c_8402, plain, (![A_648, B_2]: (~r2_hidden('#skF_2'(A_648, B_2, k3_xboole_0(B_2, B_2)), A_648) | k3_xboole_0(A_648, k3_xboole_0(B_2, B_2))=k3_xboole_0(B_2, B_2) | ~r2_hidden('#skF_1'(A_648, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | ~r2_hidden('#skF_1'(A_648, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_347, c_8299])).
% 10.78/3.54  tff(c_8476, plain, (![A_651, B_652]: (~r2_hidden('#skF_2'(A_651, B_652, B_652), A_651) | k3_xboole_0(A_651, B_652)=B_652 | ~r2_hidden('#skF_1'(A_651, B_652, B_652), B_652) | ~r2_hidden('#skF_1'(A_651, B_652, B_652), B_652))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_347, c_347, c_347, c_347, c_347, c_8402])).
% 10.78/3.54  tff(c_8647, plain, (![B_653, A_654]: (~r2_hidden('#skF_1'(B_653, k3_xboole_0(A_654, B_653), k3_xboole_0(A_654, B_653)), k3_xboole_0(A_654, B_653)) | k3_xboole_0(B_653, k3_xboole_0(A_654, B_653))=k3_xboole_0(A_654, B_653))), inference(resolution, [status(thm)], [c_7410, c_8476])).
% 10.78/3.54  tff(c_8832, plain, (![B_661, A_662]: (~r2_hidden('#skF_2'(B_661, k3_xboole_0(A_662, B_661), k3_xboole_0(A_662, B_661)), k3_xboole_0(A_662, B_661)) | k3_xboole_0(B_661, k3_xboole_0(A_662, B_661))=k3_xboole_0(A_662, B_661))), inference(resolution, [status(thm)], [c_750, c_8647])).
% 10.78/3.54  tff(c_8931, plain, (![A_663, A_664]: (k3_xboole_0(A_663, k3_xboole_0(A_664, A_663))=k3_xboole_0(A_664, A_663))), inference(resolution, [status(thm)], [c_178, c_8832])).
% 10.78/3.54  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.78/3.54  tff(c_10250, plain, (![A_664, A_663]: (r1_tarski(k3_xboole_0(A_664, A_663), A_663))), inference(superposition, [status(thm), theory('equality')], [c_8931, c_20])).
% 10.78/3.54  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.78/3.54  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k3_xboole_0(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.78/3.54  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.78/3.54  tff(c_32, plain, (![A_21, B_23]: (r1_tarski(k3_relat_1(A_21), k3_relat_1(B_23)) | ~r1_tarski(A_21, B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.78/3.54  tff(c_79, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k3_xboole_0(B_46, C_47)) | ~r1_tarski(A_45, C_47) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.78/3.54  tff(c_34, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.78/3.54  tff(c_83, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_34])).
% 10.78/3.54  tff(c_85, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_83])).
% 10.78/3.54  tff(c_88, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_85])).
% 10.78/3.54  tff(c_91, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20, c_88])).
% 10.78/3.54  tff(c_100, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_91])).
% 10.78/3.54  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_100])).
% 10.78/3.54  tff(c_105, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_83])).
% 10.78/3.54  tff(c_109, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_105])).
% 10.78/3.54  tff(c_112, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_109])).
% 10.78/3.54  tff(c_113, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 10.78/3.54  tff(c_116, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_113])).
% 10.78/3.54  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 10.78/3.54  tff(c_121, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_112])).
% 10.78/3.54  tff(c_10677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10250, c_121])).
% 10.78/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.78/3.54  
% 10.78/3.54  Inference rules
% 10.78/3.54  ----------------------
% 10.78/3.54  #Ref     : 0
% 10.78/3.54  #Sup     : 2261
% 10.78/3.54  #Fact    : 0
% 10.78/3.54  #Define  : 0
% 10.78/3.54  #Split   : 2
% 10.78/3.54  #Chain   : 0
% 10.78/3.54  #Close   : 0
% 10.78/3.54  
% 10.78/3.54  Ordering : KBO
% 10.78/3.54  
% 10.78/3.54  Simplification rules
% 10.78/3.54  ----------------------
% 10.78/3.54  #Subsume      : 1166
% 10.78/3.54  #Demod        : 2501
% 10.78/3.54  #Tautology    : 231
% 10.78/3.54  #SimpNegUnit  : 0
% 10.78/3.54  #BackRed      : 3
% 10.78/3.54  
% 10.78/3.54  #Partial instantiations: 0
% 10.78/3.54  #Strategies tried      : 1
% 10.78/3.54  
% 10.78/3.54  Timing (in seconds)
% 10.78/3.54  ----------------------
% 10.99/3.54  Preprocessing        : 0.31
% 10.99/3.54  Parsing              : 0.16
% 10.99/3.54  CNF conversion       : 0.02
% 10.99/3.54  Main loop            : 2.45
% 10.99/3.54  Inferencing          : 0.87
% 10.99/3.55  Reduction            : 0.55
% 10.99/3.55  Demodulation         : 0.39
% 10.99/3.55  BG Simplification    : 0.07
% 10.99/3.55  Subsumption          : 0.82
% 10.99/3.55  Abstraction          : 0.18
% 10.99/3.55  MUC search           : 0.00
% 10.99/3.55  Cooper               : 0.00
% 10.99/3.55  Total                : 2.80
% 10.99/3.55  Index Insertion      : 0.00
% 10.99/3.55  Index Deletion       : 0.00
% 10.99/3.55  Index Matching       : 0.00
% 10.99/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
