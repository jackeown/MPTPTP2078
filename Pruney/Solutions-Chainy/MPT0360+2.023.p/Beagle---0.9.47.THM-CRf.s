%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 10.65s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 692 expanded)
%              Number of leaves         :   31 ( 238 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 (1368 expanded)
%              Number of equality atoms :   29 ( 267 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    ! [B_47,A_8] :
      ( r1_tarski(B_47,A_8)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_125,c_8])).

tff(c_137,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_129])).

tff(c_150,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_137])).

tff(c_188,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_234,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,'#skF_4')
      | ~ r1_tarski(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_150,c_188])).

tff(c_258,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_234])).

tff(c_28,plain,(
    ! [A_15] : k1_subset_1(A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = k2_subset_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_59,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_xboole_0) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_55])).

tff(c_32,plain,(
    ! [A_17] : m1_subset_1(k1_subset_1(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_333,plain,(
    ! [A_68,B_69] :
      ( k3_subset_1(A_68,k3_subset_1(A_68,B_69)) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_343,plain,(
    ! [A_17] : k3_subset_1(A_17,k3_subset_1(A_17,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_333])).

tff(c_352,plain,(
    ! [A_17] : k3_subset_1(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_343])).

tff(c_470,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k3_subset_1(A_75,B_76),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_487,plain,(
    ! [A_23] :
      ( m1_subset_1(A_23,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_470])).

tff(c_495,plain,(
    ! [A_77] : m1_subset_1(A_77,k1_zfmisc_1(A_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_487])).

tff(c_135,plain,(
    ! [B_47,A_8] :
      ( r1_tarski(B_47,A_8)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_129])).

tff(c_506,plain,(
    ! [A_77] : r1_tarski(A_77,A_77) ),
    inference(resolution,[status(thm)],[c_495,c_135])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(B_52,A_53)
      | ~ r2_hidden(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_165,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_158])).

tff(c_50,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1565,plain,(
    ! [C_113,A_114,B_115] :
      ( r1_tarski(C_113,k3_subset_1(A_114,B_115))
      | ~ r1_tarski(B_115,k3_subset_1(A_114,C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1601,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_1565])).

tff(c_1626,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1601])).

tff(c_1629,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1626])).

tff(c_1632,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_1629])).

tff(c_1639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_1632])).

tff(c_1641,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1626])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_262,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_63,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_188])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_542,plain,(
    ! [A_79,A_80] :
      ( r1_tarski(A_79,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_79,A_80)
      | ~ r1_tarski(A_80,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_262,c_6])).

tff(c_592,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_542])).

tff(c_636,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1650,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1641,c_38])).

tff(c_494,plain,(
    ! [A_23] : m1_subset_1(A_23,k1_zfmisc_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_487])).

tff(c_1591,plain,(
    ! [A_17,B_115] :
      ( r1_tarski(A_17,k3_subset_1(A_17,B_115))
      | ~ r1_tarski(B_115,k1_xboole_0)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_1565])).

tff(c_4637,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,k3_subset_1(A_177,B_178))
      | ~ r1_tarski(B_178,k1_xboole_0)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_1591])).

tff(c_4666,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_4637])).

tff(c_4691,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_4666])).

tff(c_4726,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4691])).

tff(c_4729,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_4726])).

tff(c_4739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1641,c_4729])).

tff(c_4741,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4691])).

tff(c_1640,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1626])).

tff(c_1700,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_116,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1640,c_6])).

tff(c_2525,plain,(
    ! [A_140,A_141] :
      ( r1_tarski(A_140,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_140,A_141)
      | ~ r1_tarski(A_141,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1700,c_6])).

tff(c_2601,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2525])).

tff(c_2654,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_2601])).

tff(c_2163,plain,(
    ! [A_132,B_133] :
      ( k3_subset_1(A_132,k3_subset_1(A_132,k3_subset_1(A_132,B_133))) = k3_subset_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_470,c_38])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k2_subset_1(A_28) = B_29
      | ~ r1_tarski(k3_subset_1(A_28,B_29),B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(k3_subset_1(A_28,B_29),B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_46])).

tff(c_19875,plain,(
    ! [A_339,B_340] :
      ( k3_subset_1(A_339,k3_subset_1(A_339,B_340)) = A_339
      | ~ r1_tarski(k3_subset_1(A_339,B_340),k3_subset_1(A_339,k3_subset_1(A_339,B_340)))
      | ~ m1_subset_1(k3_subset_1(A_339,k3_subset_1(A_339,B_340)),k1_zfmisc_1(A_339))
      | ~ m1_subset_1(B_340,k1_zfmisc_1(A_339)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2163,c_56])).

tff(c_19954,plain,
    ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))) = '#skF_4'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_19875])).

tff(c_20021,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4741,c_4741,c_1650,c_2654,c_1650,c_1650,c_19954])).

tff(c_489,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k3_subset_1(A_75,B_76),A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_470,c_135])).

tff(c_4752,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4741,c_135])).

tff(c_4869,plain,(
    ! [A_183] :
      ( r1_tarski(A_183,'#skF_4')
      | ~ r1_tarski(A_183,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4752,c_6])).

tff(c_14596,plain,(
    ! [B_310] :
      ( r1_tarski(k3_subset_1(k3_subset_1('#skF_4','#skF_5'),B_310),'#skF_4')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_489,c_4869])).

tff(c_14631,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_14596,c_56])).

tff(c_14639,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_14631])).

tff(c_14646,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_165,c_14639])).

tff(c_20042,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20021,c_14646])).

tff(c_20088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_20042])).

tff(c_20089,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14631])).

tff(c_346,plain,(
    ! [A_8,C_12] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,C_12)) = C_12
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_165,c_333])).

tff(c_20195,plain,
    ( k3_subset_1('#skF_4','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20089,c_346])).

tff(c_20236,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_352,c_20195])).

tff(c_20238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.65/4.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.73/4.27  
% 10.73/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.73/4.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 10.73/4.27  
% 10.73/4.27  %Foreground sorts:
% 10.73/4.27  
% 10.73/4.27  
% 10.73/4.27  %Background operators:
% 10.73/4.27  
% 10.73/4.27  
% 10.73/4.27  %Foreground operators:
% 10.73/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.73/4.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.73/4.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.73/4.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.73/4.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.73/4.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.73/4.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.73/4.27  tff('#skF_5', type, '#skF_5': $i).
% 10.73/4.27  tff('#skF_6', type, '#skF_6': $i).
% 10.73/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.73/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.73/4.27  tff('#skF_4', type, '#skF_4': $i).
% 10.73/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.73/4.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.73/4.27  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 10.73/4.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.73/4.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.73/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.73/4.27  
% 10.73/4.29  tff(f_100, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 10.73/4.29  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.73/4.29  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.73/4.29  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.73/4.29  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.73/4.29  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 10.73/4.29  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.73/4.29  tff(f_76, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 10.73/4.29  tff(f_63, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 10.73/4.29  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.73/4.29  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.73/4.29  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 10.73/4.29  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 10.73/4.29  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.73/4.29  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.73/4.29  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.73/4.29  tff(c_36, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.73/4.29  tff(c_125, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.73/4.29  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.73/4.29  tff(c_129, plain, (![B_47, A_8]: (r1_tarski(B_47, A_8) | ~m1_subset_1(B_47, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_125, c_8])).
% 10.73/4.29  tff(c_137, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_36, c_129])).
% 10.73/4.29  tff(c_150, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_137])).
% 10.73/4.29  tff(c_188, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.73/4.29  tff(c_234, plain, (![A_62]: (r1_tarski(A_62, '#skF_4') | ~r1_tarski(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_150, c_188])).
% 10.73/4.29  tff(c_258, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_234])).
% 10.73/4.29  tff(c_28, plain, (![A_15]: (k1_subset_1(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.73/4.29  tff(c_30, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.73/4.29  tff(c_40, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=k2_subset_1(A_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.73/4.29  tff(c_55, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 10.73/4.29  tff(c_59, plain, (![A_23]: (k3_subset_1(A_23, k1_xboole_0)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_55])).
% 10.73/4.29  tff(c_32, plain, (![A_17]: (m1_subset_1(k1_subset_1(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.73/4.29  tff(c_58, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 10.73/4.29  tff(c_333, plain, (![A_68, B_69]: (k3_subset_1(A_68, k3_subset_1(A_68, B_69))=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.73/4.29  tff(c_343, plain, (![A_17]: (k3_subset_1(A_17, k3_subset_1(A_17, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_333])).
% 10.73/4.29  tff(c_352, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_343])).
% 10.73/4.29  tff(c_470, plain, (![A_75, B_76]: (m1_subset_1(k3_subset_1(A_75, B_76), k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.73/4.29  tff(c_487, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(A_23)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_470])).
% 10.73/4.29  tff(c_495, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_487])).
% 10.73/4.29  tff(c_135, plain, (![B_47, A_8]: (r1_tarski(B_47, A_8) | ~m1_subset_1(B_47, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_36, c_129])).
% 10.73/4.29  tff(c_506, plain, (![A_77]: (r1_tarski(A_77, A_77))), inference(resolution, [status(thm)], [c_495, c_135])).
% 10.73/4.29  tff(c_10, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.73/4.29  tff(c_152, plain, (![B_52, A_53]: (m1_subset_1(B_52, A_53) | ~r2_hidden(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.73/4.29  tff(c_158, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_10, c_152])).
% 10.73/4.29  tff(c_165, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_36, c_158])).
% 10.73/4.29  tff(c_50, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.73/4.29  tff(c_1565, plain, (![C_113, A_114, B_115]: (r1_tarski(C_113, k3_subset_1(A_114, B_115)) | ~r1_tarski(B_115, k3_subset_1(A_114, C_113)) | ~m1_subset_1(C_113, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.73/4.29  tff(c_1601, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_1565])).
% 10.73/4.29  tff(c_1626, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1601])).
% 10.73/4.29  tff(c_1629, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1626])).
% 10.73/4.29  tff(c_1632, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_165, c_1629])).
% 10.73/4.29  tff(c_1639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_1632])).
% 10.73/4.29  tff(c_1641, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1626])).
% 10.73/4.29  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.73/4.29  tff(c_262, plain, (![A_63]: (r1_tarski(A_63, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_63, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_188])).
% 10.73/4.29  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.73/4.29  tff(c_542, plain, (![A_79, A_80]: (r1_tarski(A_79, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_79, A_80) | ~r1_tarski(A_80, '#skF_5'))), inference(resolution, [status(thm)], [c_262, c_6])).
% 10.73/4.29  tff(c_592, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_150, c_542])).
% 10.73/4.29  tff(c_636, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_592])).
% 10.73/4.29  tff(c_38, plain, (![A_21, B_22]: (k3_subset_1(A_21, k3_subset_1(A_21, B_22))=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.73/4.29  tff(c_1650, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_1641, c_38])).
% 10.73/4.29  tff(c_494, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_487])).
% 10.73/4.29  tff(c_1591, plain, (![A_17, B_115]: (r1_tarski(A_17, k3_subset_1(A_17, B_115)) | ~r1_tarski(B_115, k1_xboole_0) | ~m1_subset_1(A_17, k1_zfmisc_1(A_17)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_352, c_1565])).
% 10.73/4.29  tff(c_4637, plain, (![A_177, B_178]: (r1_tarski(A_177, k3_subset_1(A_177, B_178)) | ~r1_tarski(B_178, k1_xboole_0) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_1591])).
% 10.73/4.29  tff(c_4666, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_4637])).
% 10.73/4.29  tff(c_4691, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_636, c_4666])).
% 10.73/4.29  tff(c_4726, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4691])).
% 10.73/4.29  tff(c_4729, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_4726])).
% 10.73/4.29  tff(c_4739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1641, c_4729])).
% 10.73/4.29  tff(c_4741, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4691])).
% 10.73/4.29  tff(c_1640, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1626])).
% 10.73/4.29  tff(c_1700, plain, (![A_116]: (r1_tarski(A_116, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_116, '#skF_6'))), inference(resolution, [status(thm)], [c_1640, c_6])).
% 10.73/4.29  tff(c_2525, plain, (![A_140, A_141]: (r1_tarski(A_140, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_140, A_141) | ~r1_tarski(A_141, '#skF_6'))), inference(resolution, [status(thm)], [c_1700, c_6])).
% 10.73/4.29  tff(c_2601, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_2525])).
% 10.73/4.29  tff(c_2654, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_2601])).
% 10.73/4.29  tff(c_2163, plain, (![A_132, B_133]: (k3_subset_1(A_132, k3_subset_1(A_132, k3_subset_1(A_132, B_133)))=k3_subset_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_470, c_38])).
% 10.73/4.29  tff(c_46, plain, (![A_28, B_29]: (k2_subset_1(A_28)=B_29 | ~r1_tarski(k3_subset_1(A_28, B_29), B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.73/4.29  tff(c_56, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(k3_subset_1(A_28, B_29), B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_46])).
% 10.73/4.29  tff(c_19875, plain, (![A_339, B_340]: (k3_subset_1(A_339, k3_subset_1(A_339, B_340))=A_339 | ~r1_tarski(k3_subset_1(A_339, B_340), k3_subset_1(A_339, k3_subset_1(A_339, B_340))) | ~m1_subset_1(k3_subset_1(A_339, k3_subset_1(A_339, B_340)), k1_zfmisc_1(A_339)) | ~m1_subset_1(B_340, k1_zfmisc_1(A_339)))), inference(superposition, [status(thm), theory('equality')], [c_2163, c_56])).
% 10.73/4.29  tff(c_19954, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))='#skF_4' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))) | ~m1_subset_1(k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_19875])).
% 10.73/4.29  tff(c_20021, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4741, c_4741, c_1650, c_2654, c_1650, c_1650, c_19954])).
% 10.73/4.29  tff(c_489, plain, (![A_75, B_76]: (r1_tarski(k3_subset_1(A_75, B_76), A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_470, c_135])).
% 10.73/4.29  tff(c_4752, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4741, c_135])).
% 10.73/4.29  tff(c_4869, plain, (![A_183]: (r1_tarski(A_183, '#skF_4') | ~r1_tarski(A_183, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_4752, c_6])).
% 10.73/4.29  tff(c_14596, plain, (![B_310]: (r1_tarski(k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), B_310), '#skF_4') | ~m1_subset_1(B_310, k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_489, c_4869])).
% 10.73/4.29  tff(c_14631, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_14596, c_56])).
% 10.73/4.29  tff(c_14639, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_14631])).
% 10.73/4.29  tff(c_14646, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_165, c_14639])).
% 10.73/4.29  tff(c_20042, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20021, c_14646])).
% 10.73/4.29  tff(c_20088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_506, c_20042])).
% 10.73/4.29  tff(c_20089, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_14631])).
% 10.73/4.29  tff(c_346, plain, (![A_8, C_12]: (k3_subset_1(A_8, k3_subset_1(A_8, C_12))=C_12 | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_165, c_333])).
% 10.73/4.29  tff(c_20195, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20089, c_346])).
% 10.73/4.29  tff(c_20236, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_352, c_20195])).
% 10.73/4.29  tff(c_20238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_20236])).
% 10.73/4.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.73/4.29  
% 10.73/4.29  Inference rules
% 10.73/4.29  ----------------------
% 10.73/4.29  #Ref     : 0
% 10.73/4.29  #Sup     : 4590
% 10.73/4.29  #Fact    : 0
% 10.73/4.29  #Define  : 0
% 10.73/4.29  #Split   : 21
% 10.73/4.29  #Chain   : 0
% 10.73/4.29  #Close   : 0
% 10.73/4.29  
% 10.73/4.29  Ordering : KBO
% 10.73/4.29  
% 10.73/4.29  Simplification rules
% 10.73/4.29  ----------------------
% 10.73/4.29  #Subsume      : 1649
% 10.73/4.29  #Demod        : 2680
% 10.73/4.29  #Tautology    : 1216
% 10.73/4.29  #SimpNegUnit  : 86
% 10.73/4.29  #BackRed      : 152
% 10.73/4.29  
% 10.73/4.29  #Partial instantiations: 0
% 10.73/4.29  #Strategies tried      : 1
% 10.73/4.29  
% 10.73/4.29  Timing (in seconds)
% 10.73/4.29  ----------------------
% 10.73/4.29  Preprocessing        : 0.30
% 10.73/4.29  Parsing              : 0.15
% 10.73/4.29  CNF conversion       : 0.02
% 10.73/4.29  Main loop            : 3.20
% 10.73/4.29  Inferencing          : 0.72
% 10.73/4.29  Reduction            : 1.26
% 10.73/4.29  Demodulation         : 0.96
% 10.73/4.29  BG Simplification    : 0.08
% 10.73/4.29  Subsumption          : 0.96
% 10.73/4.29  Abstraction          : 0.11
% 10.73/4.29  MUC search           : 0.00
% 10.73/4.29  Cooper               : 0.00
% 10.73/4.29  Total                : 3.54
% 10.73/4.29  Index Insertion      : 0.00
% 10.73/4.29  Index Deletion       : 0.00
% 10.73/4.29  Index Matching       : 0.00
% 10.73/4.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
