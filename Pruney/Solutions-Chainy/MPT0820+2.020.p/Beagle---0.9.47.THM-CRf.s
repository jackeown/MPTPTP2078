%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:03 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 180 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 271 expanded)
%              Number of equality atoms :   13 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_42,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_112,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_115,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_112])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_115])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_97])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_16])).

tff(c_542,plain,(
    ! [C_130,A_131,B_132] : k2_xboole_0(k2_zfmisc_1(C_130,A_131),k2_zfmisc_1(C_130,B_132)) = k2_zfmisc_1(C_130,k2_xboole_0(A_131,B_132)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_595,plain,(
    ! [C_133,A_134,B_135] : r1_tarski(k2_zfmisc_1(C_133,A_134),k2_zfmisc_1(C_133,k2_xboole_0(A_134,B_135))) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_8])).

tff(c_609,plain,(
    ! [C_133,A_56,B_55] : r1_tarski(k2_zfmisc_1(C_133,A_56),k2_zfmisc_1(C_133,k2_xboole_0(B_55,A_56))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_595])).

tff(c_24,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k1_zfmisc_1(A_20),k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_318,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_379,plain,(
    ! [A_109,B_110,B_111] :
      ( r2_hidden(A_109,B_110)
      | ~ r1_tarski(B_111,B_110)
      | v1_xboole_0(B_111)
      | ~ m1_subset_1(A_109,B_111) ) ),
    inference(resolution,[status(thm)],[c_28,c_318])).

tff(c_393,plain,(
    ! [A_109,B_21,A_20] :
      ( r2_hidden(A_109,k1_zfmisc_1(B_21))
      | v1_xboole_0(k1_zfmisc_1(A_20))
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_20))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_379])).

tff(c_831,plain,(
    ! [A_149,B_150,A_151] :
      ( r2_hidden(A_149,k1_zfmisc_1(B_150))
      | ~ m1_subset_1(A_149,k1_zfmisc_1(A_151))
      | ~ r1_tarski(A_151,B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_393])).

tff(c_839,plain,(
    ! [B_152] :
      ( r2_hidden('#skF_4',k1_zfmisc_1(B_152))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_152) ) ),
    inference(resolution,[status(thm)],[c_50,c_831])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_857,plain,(
    ! [B_155] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_155))
      | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),B_155) ) ),
    inference(resolution,[status(thm)],[c_839,c_26])).

tff(c_894,plain,(
    ! [B_156] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_xboole_0(B_156,'#skF_3')))) ),
    inference(resolution,[status(thm)],[c_609,c_857])).

tff(c_44,plain,(
    ! [C_39,B_38,A_37] :
      ( v5_relat_1(C_39,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_921,plain,(
    ! [B_157] : v5_relat_1('#skF_4',k2_xboole_0(B_157,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_894,c_44])).

tff(c_925,plain,(
    ! [A_56] : v5_relat_1('#skF_4',k2_xboole_0('#skF_3',A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_921])).

tff(c_38,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v5_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_468,plain,(
    ! [A_121,C_122,B_123] : k2_xboole_0(k2_zfmisc_1(A_121,C_122),k2_zfmisc_1(B_123,C_122)) = k2_zfmisc_1(k2_xboole_0(A_121,B_123),C_122) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_507,plain,(
    ! [A_124,C_125,B_126] : r1_tarski(k2_zfmisc_1(A_124,C_125),k2_zfmisc_1(k2_xboole_0(A_124,B_126),C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_8])).

tff(c_518,plain,(
    ! [A_56,C_125,B_55] : r1_tarski(k2_zfmisc_1(A_56,C_125),k2_zfmisc_1(k2_xboole_0(B_55,A_56),C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_507])).

tff(c_958,plain,(
    ! [B_161] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(B_161,'#skF_2'),'#skF_3'))) ),
    inference(resolution,[status(thm)],[c_518,c_857])).

tff(c_46,plain,(
    ! [C_39,A_37,B_38] :
      ( v4_relat_1(C_39,A_37)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_983,plain,(
    ! [B_161] : v4_relat_1('#skF_4',k2_xboole_0(B_161,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_958,c_46])).

tff(c_34,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(B_31),A_30)
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_34] :
      ( k2_xboole_0(k1_relat_1(A_34),k2_relat_1(A_34)) = k3_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_369,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_tarski(k2_xboole_0(A_106,C_107),B_108)
      | ~ r1_tarski(C_107,B_108)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_847,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k3_relat_1(A_153),B_154)
      | ~ r1_tarski(k2_relat_1(A_153),B_154)
      | ~ r1_tarski(k1_relat_1(A_153),B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_369])).

tff(c_48,plain,(
    ~ r1_tarski(k3_relat_1('#skF_4'),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,(
    ~ r1_tarski(k3_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_48])).

tff(c_852,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_847,c_142])).

tff(c_856,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_852])).

tff(c_1405,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_1408,plain,
    ( ~ v4_relat_1('#skF_4',k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1405])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_983,c_1408])).

tff(c_1413,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_1417,plain,
    ( ~ v5_relat_1('#skF_4',k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1413])).

tff(c_1421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_925,c_1417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.60  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.49/1.60  
% 3.49/1.60  %Foreground sorts:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Background operators:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Foreground operators:
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.60  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.49/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.49/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.49/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.60  
% 3.75/1.61  tff(f_92, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.75/1.61  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.75/1.61  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.75/1.61  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.75/1.61  tff(f_46, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.75/1.61  tff(f_50, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.75/1.61  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.75/1.61  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.75/1.61  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.75/1.61  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.75/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.75/1.61  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.75/1.61  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.75/1.61  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.75/1.61  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.75/1.61  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.75/1.61  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.75/1.61  tff(c_42, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.75/1.61  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.61  tff(c_112, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.75/1.61  tff(c_115, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_112])).
% 3.75/1.61  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_115])).
% 3.75/1.61  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.75/1.61  tff(c_97, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.61  tff(c_119, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_97])).
% 3.75/1.61  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.61  tff(c_125, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_119, c_16])).
% 3.75/1.61  tff(c_542, plain, (![C_130, A_131, B_132]: (k2_xboole_0(k2_zfmisc_1(C_130, A_131), k2_zfmisc_1(C_130, B_132))=k2_zfmisc_1(C_130, k2_xboole_0(A_131, B_132)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.61  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.75/1.61  tff(c_595, plain, (![C_133, A_134, B_135]: (r1_tarski(k2_zfmisc_1(C_133, A_134), k2_zfmisc_1(C_133, k2_xboole_0(A_134, B_135))))), inference(superposition, [status(thm), theory('equality')], [c_542, c_8])).
% 3.75/1.61  tff(c_609, plain, (![C_133, A_56, B_55]: (r1_tarski(k2_zfmisc_1(C_133, A_56), k2_zfmisc_1(C_133, k2_xboole_0(B_55, A_56))))), inference(superposition, [status(thm), theory('equality')], [c_125, c_595])).
% 3.75/1.61  tff(c_24, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.61  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(k1_zfmisc_1(A_20), k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.75/1.61  tff(c_28, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.61  tff(c_318, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.61  tff(c_379, plain, (![A_109, B_110, B_111]: (r2_hidden(A_109, B_110) | ~r1_tarski(B_111, B_110) | v1_xboole_0(B_111) | ~m1_subset_1(A_109, B_111))), inference(resolution, [status(thm)], [c_28, c_318])).
% 3.75/1.61  tff(c_393, plain, (![A_109, B_21, A_20]: (r2_hidden(A_109, k1_zfmisc_1(B_21)) | v1_xboole_0(k1_zfmisc_1(A_20)) | ~m1_subset_1(A_109, k1_zfmisc_1(A_20)) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_22, c_379])).
% 3.75/1.61  tff(c_831, plain, (![A_149, B_150, A_151]: (r2_hidden(A_149, k1_zfmisc_1(B_150)) | ~m1_subset_1(A_149, k1_zfmisc_1(A_151)) | ~r1_tarski(A_151, B_150))), inference(negUnitSimplification, [status(thm)], [c_24, c_393])).
% 3.75/1.61  tff(c_839, plain, (![B_152]: (r2_hidden('#skF_4', k1_zfmisc_1(B_152)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_152))), inference(resolution, [status(thm)], [c_50, c_831])).
% 3.75/1.61  tff(c_26, plain, (![A_23, B_24]: (m1_subset_1(A_23, B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.75/1.61  tff(c_857, plain, (![B_155]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_155)) | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), B_155))), inference(resolution, [status(thm)], [c_839, c_26])).
% 3.75/1.61  tff(c_894, plain, (![B_156]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_xboole_0(B_156, '#skF_3')))))), inference(resolution, [status(thm)], [c_609, c_857])).
% 3.75/1.61  tff(c_44, plain, (![C_39, B_38, A_37]: (v5_relat_1(C_39, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.75/1.61  tff(c_921, plain, (![B_157]: (v5_relat_1('#skF_4', k2_xboole_0(B_157, '#skF_3')))), inference(resolution, [status(thm)], [c_894, c_44])).
% 3.75/1.61  tff(c_925, plain, (![A_56]: (v5_relat_1('#skF_4', k2_xboole_0('#skF_3', A_56)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_921])).
% 3.75/1.61  tff(c_38, plain, (![B_33, A_32]: (r1_tarski(k2_relat_1(B_33), A_32) | ~v5_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.75/1.61  tff(c_468, plain, (![A_121, C_122, B_123]: (k2_xboole_0(k2_zfmisc_1(A_121, C_122), k2_zfmisc_1(B_123, C_122))=k2_zfmisc_1(k2_xboole_0(A_121, B_123), C_122))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.61  tff(c_507, plain, (![A_124, C_125, B_126]: (r1_tarski(k2_zfmisc_1(A_124, C_125), k2_zfmisc_1(k2_xboole_0(A_124, B_126), C_125)))), inference(superposition, [status(thm), theory('equality')], [c_468, c_8])).
% 3.75/1.61  tff(c_518, plain, (![A_56, C_125, B_55]: (r1_tarski(k2_zfmisc_1(A_56, C_125), k2_zfmisc_1(k2_xboole_0(B_55, A_56), C_125)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_507])).
% 3.75/1.61  tff(c_958, plain, (![B_161]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(B_161, '#skF_2'), '#skF_3'))))), inference(resolution, [status(thm)], [c_518, c_857])).
% 3.75/1.61  tff(c_46, plain, (![C_39, A_37, B_38]: (v4_relat_1(C_39, A_37) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.75/1.61  tff(c_983, plain, (![B_161]: (v4_relat_1('#skF_4', k2_xboole_0(B_161, '#skF_2')))), inference(resolution, [status(thm)], [c_958, c_46])).
% 3.75/1.61  tff(c_34, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(B_31), A_30) | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.75/1.61  tff(c_40, plain, (![A_34]: (k2_xboole_0(k1_relat_1(A_34), k2_relat_1(A_34))=k3_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.61  tff(c_369, plain, (![A_106, C_107, B_108]: (r1_tarski(k2_xboole_0(A_106, C_107), B_108) | ~r1_tarski(C_107, B_108) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.75/1.61  tff(c_847, plain, (![A_153, B_154]: (r1_tarski(k3_relat_1(A_153), B_154) | ~r1_tarski(k2_relat_1(A_153), B_154) | ~r1_tarski(k1_relat_1(A_153), B_154) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_40, c_369])).
% 3.75/1.61  tff(c_48, plain, (~r1_tarski(k3_relat_1('#skF_4'), k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.61  tff(c_142, plain, (~r1_tarski(k3_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_48])).
% 3.75/1.61  tff(c_852, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_847, c_142])).
% 3.75/1.61  tff(c_856, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_852])).
% 3.75/1.61  tff(c_1405, plain, (~r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_856])).
% 3.75/1.61  tff(c_1408, plain, (~v4_relat_1('#skF_4', k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1405])).
% 3.75/1.61  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_983, c_1408])).
% 3.75/1.61  tff(c_1413, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_856])).
% 3.75/1.61  tff(c_1417, plain, (~v5_relat_1('#skF_4', k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1413])).
% 3.75/1.61  tff(c_1421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_925, c_1417])).
% 3.75/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.61  
% 3.75/1.61  Inference rules
% 3.75/1.61  ----------------------
% 3.75/1.61  #Ref     : 0
% 3.75/1.61  #Sup     : 331
% 3.75/1.61  #Fact    : 0
% 3.75/1.61  #Define  : 0
% 3.75/1.61  #Split   : 1
% 3.75/1.61  #Chain   : 0
% 3.75/1.61  #Close   : 0
% 3.75/1.61  
% 3.75/1.61  Ordering : KBO
% 3.75/1.61  
% 3.75/1.61  Simplification rules
% 3.75/1.61  ----------------------
% 3.75/1.61  #Subsume      : 33
% 3.75/1.61  #Demod        : 75
% 3.75/1.61  #Tautology    : 101
% 3.75/1.61  #SimpNegUnit  : 1
% 3.75/1.61  #BackRed      : 1
% 3.75/1.61  
% 3.75/1.61  #Partial instantiations: 0
% 3.75/1.61  #Strategies tried      : 1
% 3.75/1.61  
% 3.75/1.62  Timing (in seconds)
% 3.75/1.62  ----------------------
% 3.75/1.62  Preprocessing        : 0.32
% 3.75/1.62  Parsing              : 0.17
% 3.75/1.62  CNF conversion       : 0.02
% 3.75/1.62  Main loop            : 0.51
% 3.75/1.62  Inferencing          : 0.18
% 3.75/1.62  Reduction            : 0.17
% 3.75/1.62  Demodulation         : 0.13
% 3.75/1.62  BG Simplification    : 0.02
% 3.75/1.62  Subsumption          : 0.09
% 3.75/1.62  Abstraction          : 0.02
% 3.75/1.62  MUC search           : 0.00
% 3.75/1.62  Cooper               : 0.00
% 3.75/1.62  Total                : 0.87
% 3.75/1.62  Index Insertion      : 0.00
% 3.75/1.62  Index Deletion       : 0.00
% 3.75/1.62  Index Matching       : 0.00
% 3.75/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
