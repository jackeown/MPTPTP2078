%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0354+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 25.73s
% Output     : CNFRefutation 25.83s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 141 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 203 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_61,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_231,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_248,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_231])).

tff(c_36,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_14,B_15] : m1_subset_1(k6_subset_1(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    ! [A_14,B_15] : m1_subset_1(k4_xboole_0(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_269,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_51])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1654,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_subset_1(A_125,B_126,C_127) = k2_xboole_0(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2090,plain,(
    ! [B_138] :
      ( k4_subset_1('#skF_3',B_138,'#skF_5') = k2_xboole_0(B_138,'#skF_5')
      | ~ m1_subset_1(B_138,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1654])).

tff(c_2125,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_269,c_2090])).

tff(c_2163,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') = k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2125])).

tff(c_32,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_154,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | ~ m1_subset_1(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [B_56,A_5] :
      ( r1_tarski(B_56,A_5)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_162,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_158])).

tff(c_178,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_162])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_194,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_178,c_42])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_696,plain,(
    ! [A_91,B_92,C_93] : k2_xboole_0(k4_xboole_0(A_91,B_92),k3_xboole_0(A_91,C_93)) = k4_xboole_0(A_91,k4_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3163,plain,(
    ! [A_181,C_182,B_183] : k2_xboole_0(k3_xboole_0(A_181,C_182),k4_xboole_0(A_181,B_183)) = k4_xboole_0(A_181,k4_xboole_0(B_183,C_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2])).

tff(c_10825,plain,(
    ! [A_395,B_396,B_397] : k2_xboole_0(k3_xboole_0(A_395,B_396),k4_xboole_0(B_396,B_397)) = k4_xboole_0(B_396,k4_xboole_0(B_397,A_395)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3163])).

tff(c_36528,plain,(
    ! [B_789] : k4_xboole_0('#skF_3',k4_xboole_0(B_789,'#skF_5')) = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3',B_789)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_10825])).

tff(c_226,plain,(
    ! [A_62,B_63] : r1_tarski(k4_xboole_0(A_62,B_63),A_62) ),
    inference(resolution,[status(thm)],[c_51,c_162])).

tff(c_316,plain,(
    ! [A_68,B_69] : k3_xboole_0(k4_xboole_0(A_68,B_69),A_68) = k4_xboole_0(A_68,B_69) ),
    inference(resolution,[status(thm)],[c_226,c_42])).

tff(c_322,plain,(
    ! [A_68,B_69] : k3_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_4])).

tff(c_230,plain,(
    ! [A_62,B_63] : k3_xboole_0(k4_xboole_0(A_62,B_63),A_62) = k4_xboole_0(A_62,B_63) ),
    inference(resolution,[status(thm)],[c_226,c_42])).

tff(c_508,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_536,plain,(
    ! [B_81] : k9_subset_1('#skF_3',B_81,'#skF_4') = k3_xboole_0(B_81,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_508])).

tff(c_442,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k9_subset_1(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k3_subset_1(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6008,plain,(
    ! [A_250,B_251,C_252] :
      ( k4_xboole_0(A_250,k9_subset_1(A_250,B_251,C_252)) = k3_subset_1(A_250,k9_subset_1(A_250,B_251,C_252))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250)) ) ),
    inference(resolution,[status(thm)],[c_442,c_26])).

tff(c_6074,plain,(
    ! [B_251] : k4_xboole_0('#skF_3',k9_subset_1('#skF_3',B_251,'#skF_4')) = k3_subset_1('#skF_3',k9_subset_1('#skF_3',B_251,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_6008])).

tff(c_6244,plain,(
    ! [B_257] : k4_xboole_0('#skF_3',k3_xboole_0(B_257,'#skF_4')) = k3_subset_1('#skF_3',k3_xboole_0(B_257,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_536,c_6074])).

tff(c_6326,plain,(
    ! [B_63] : k3_subset_1('#skF_3',k3_xboole_0(k4_xboole_0('#skF_4',B_63),'#skF_4')) = k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_6244])).

tff(c_6344,plain,(
    ! [B_63] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_63)) = k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_4,c_6326])).

tff(c_36572,plain,(
    k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36528,c_6344])).

tff(c_36784,plain,(
    k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_36572])).

tff(c_363,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_385,plain,(
    ! [C_72] : k7_subset_1('#skF_3','#skF_4',C_72) = k4_xboole_0('#skF_4',C_72) ),
    inference(resolution,[status(thm)],[c_50,c_363])).

tff(c_46,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k3_subset_1('#skF_3',k7_subset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_395,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k3_subset_1('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_46])).

tff(c_44159,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_5') != k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36784,c_395])).

tff(c_52911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2163,c_44159])).

%------------------------------------------------------------------------------
