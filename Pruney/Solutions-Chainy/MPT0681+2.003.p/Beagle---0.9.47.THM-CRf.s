%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:25 EST 2020

% Result     : Theorem 31.77s
% Output     : CNFRefutation 31.86s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 165 expanded)
%              Number of leaves         :   46 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  141 ( 296 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    v2_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [B_73,A_74] :
      ( r1_xboole_0(B_73,A_74)
      | ~ r1_xboole_0(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden(A_77,B_78)
      | ~ r1_xboole_0(k1_tarski(A_77),B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_105,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_110,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_62,plain,(
    ! [A_71] :
      ( k7_relat_1(A_71,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    k7_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_62])).

tff(c_980,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(k4_tarski('#skF_4'(A_156,B_157),'#skF_5'(A_156,B_157)),A_156)
      | r1_tarski(A_156,B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_988,plain,(
    ! [B_157] :
      ( r1_tarski(k1_xboole_0,B_157)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_980,c_104])).

tff(c_993,plain,(
    ! [B_158] : r1_tarski(k1_xboole_0,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_988])).

tff(c_38,plain,(
    ! [B_62,A_61] :
      ( k1_relat_1(k7_relat_1(B_62,A_61)) = A_61
      | ~ r1_tarski(A_61,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1005,plain,(
    ! [B_160] :
      ( k1_relat_1(k7_relat_1(B_160,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_993,c_38])).

tff(c_1043,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1005])).

tff(c_1058,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1043])).

tff(c_30,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_6'(A_50,B_51),k1_relat_1(B_51))
      | ~ r2_hidden(A_50,k2_relat_1(B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1062,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_6'(A_50,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_50,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_30])).

tff(c_1069,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_6'(A_50,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_50,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1062])).

tff(c_1078,plain,(
    ! [A_161] : ~ r2_hidden(A_161,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1069])).

tff(c_1093,plain,(
    v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_14,c_1078])).

tff(c_36,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | r2_hidden(k4_tarski('#skF_7'(A_58),'#skF_8'(A_58)),A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1092,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_1078])).

tff(c_1147,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1092])).

tff(c_427,plain,(
    ! [C_108,A_109,B_110] :
      ( k7_relat_1(k7_relat_1(C_108,A_109),B_110) = k7_relat_1(C_108,k3_xboole_0(A_109,B_110))
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [C_55,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_55,A_53),B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1547,plain,(
    ! [C_180,A_181,B_182] :
      ( k7_relat_1(C_180,k3_xboole_0(A_181,B_182)) = k1_xboole_0
      | ~ r1_xboole_0(A_181,B_182)
      | ~ v1_relat_1(C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_32])).

tff(c_28,plain,(
    ! [B_49,A_48] :
      ( k2_relat_1(k7_relat_1(B_49,A_48)) = k9_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1603,plain,(
    ! [C_180,A_181,B_182] :
      ( k9_relat_1(C_180,k3_xboole_0(A_181,B_182)) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_180)
      | ~ r1_xboole_0(A_181,B_182)
      | ~ v1_relat_1(C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_28])).

tff(c_68813,plain,(
    ! [C_983,A_984,B_985] :
      ( k9_relat_1(C_983,k3_xboole_0(A_984,B_985)) = k1_xboole_0
      | ~ v1_relat_1(C_983)
      | ~ r1_xboole_0(A_984,B_985)
      | ~ v1_relat_1(C_983)
      | ~ v1_relat_1(C_983) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1603])).

tff(c_1210,plain,(
    ! [C_170,A_171,B_172] :
      ( k3_xboole_0(k9_relat_1(C_170,A_171),k9_relat_1(C_170,B_172)) = k9_relat_1(C_170,k3_xboole_0(A_171,B_172))
      | ~ v2_funct_1(C_170)
      | ~ v1_funct_1(C_170)
      | ~ v1_relat_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( ~ r1_xboole_0(k3_xboole_0(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1228,plain,(
    ! [C_170,A_171,B_172] :
      ( ~ r1_xboole_0(k9_relat_1(C_170,k3_xboole_0(A_171,B_172)),k9_relat_1(C_170,B_172))
      | r1_xboole_0(k9_relat_1(C_170,A_171),k9_relat_1(C_170,B_172))
      | ~ v2_funct_1(C_170)
      | ~ v1_funct_1(C_170)
      | ~ v1_relat_1(C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_6])).

tff(c_69013,plain,(
    ! [C_983,B_985,A_984] :
      ( ~ r1_xboole_0(k1_xboole_0,k9_relat_1(C_983,B_985))
      | r1_xboole_0(k9_relat_1(C_983,A_984),k9_relat_1(C_983,B_985))
      | ~ v2_funct_1(C_983)
      | ~ v1_funct_1(C_983)
      | ~ v1_relat_1(C_983)
      | ~ v1_relat_1(C_983)
      | ~ r1_xboole_0(A_984,B_985)
      | ~ v1_relat_1(C_983)
      | ~ v1_relat_1(C_983) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68813,c_1228])).

tff(c_151803,plain,(
    ! [C_1646,A_1647,B_1648] :
      ( r1_xboole_0(k9_relat_1(C_1646,A_1647),k9_relat_1(C_1646,B_1648))
      | ~ v2_funct_1(C_1646)
      | ~ v1_funct_1(C_1646)
      | ~ r1_xboole_0(A_1647,B_1648)
      | ~ v1_relat_1(C_1646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_69013])).

tff(c_48,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_11','#skF_9'),k9_relat_1('#skF_11','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_151834,plain,
    ( ~ v2_funct_1('#skF_11')
    | ~ v1_funct_1('#skF_11')
    | ~ r1_xboole_0('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_151803,c_48])).

tff(c_152675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_50,c_151834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.77/23.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.77/23.48  
% 31.77/23.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.86/23.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_5 > #skF_4
% 31.86/23.48  
% 31.86/23.48  %Foreground sorts:
% 31.86/23.48  
% 31.86/23.48  
% 31.86/23.48  %Background operators:
% 31.86/23.48  
% 31.86/23.48  
% 31.86/23.48  %Foreground operators:
% 31.86/23.48  tff('#skF_7', type, '#skF_7': $i > $i).
% 31.86/23.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 31.86/23.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 31.86/23.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 31.86/23.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.86/23.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.86/23.48  tff('#skF_11', type, '#skF_11': $i).
% 31.86/23.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.86/23.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 31.86/23.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 31.86/23.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 31.86/23.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.86/23.48  tff('#skF_8', type, '#skF_8': $i > $i).
% 31.86/23.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 31.86/23.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.86/23.48  tff('#skF_10', type, '#skF_10': $i).
% 31.86/23.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 31.86/23.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 31.86/23.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 31.86/23.48  tff('#skF_9', type, '#skF_9': $i).
% 31.86/23.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 31.86/23.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.86/23.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.86/23.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 31.86/23.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.86/23.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 31.86/23.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 31.86/23.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.86/23.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 31.86/23.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 31.86/23.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 31.86/23.48  
% 31.86/23.50  tff(f_136, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 31.86/23.50  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 31.86/23.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 31.86/23.50  tff(f_52, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 31.86/23.50  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 31.86/23.50  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 31.86/23.50  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 31.86/23.50  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 31.86/23.50  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 31.86/23.50  tff(f_105, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 31.86/23.50  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 31.86/23.50  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 31.86/23.50  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 31.86/23.50  tff(f_125, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 31.86/23.50  tff(f_37, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 31.86/23.50  tff(c_56, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.86/23.50  tff(c_52, plain, (r1_xboole_0('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.86/23.50  tff(c_54, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.86/23.50  tff(c_50, plain, (v2_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.86/23.50  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.86/23.50  tff(c_82, plain, (![B_73, A_74]: (r1_xboole_0(B_73, A_74) | ~r1_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.86/23.50  tff(c_87, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_4, c_82])).
% 31.86/23.50  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 31.86/23.50  tff(c_99, plain, (![A_77, B_78]: (~r2_hidden(A_77, B_78) | ~r1_xboole_0(k1_tarski(A_77), B_78))), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.86/23.50  tff(c_104, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_99])).
% 31.86/23.50  tff(c_105, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_99])).
% 31.86/23.50  tff(c_110, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_105])).
% 31.86/23.50  tff(c_62, plain, (![A_71]: (k7_relat_1(A_71, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.86/23.50  tff(c_70, plain, (k7_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_62])).
% 31.86/23.50  tff(c_980, plain, (![A_156, B_157]: (r2_hidden(k4_tarski('#skF_4'(A_156, B_157), '#skF_5'(A_156, B_157)), A_156) | r1_tarski(A_156, B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_62])).
% 31.86/23.50  tff(c_988, plain, (![B_157]: (r1_tarski(k1_xboole_0, B_157) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_980, c_104])).
% 31.86/23.50  tff(c_993, plain, (![B_158]: (r1_tarski(k1_xboole_0, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_988])).
% 31.86/23.50  tff(c_38, plain, (![B_62, A_61]: (k1_relat_1(k7_relat_1(B_62, A_61))=A_61 | ~r1_tarski(A_61, k1_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_111])).
% 31.86/23.50  tff(c_1005, plain, (![B_160]: (k1_relat_1(k7_relat_1(B_160, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_993, c_38])).
% 31.86/23.50  tff(c_1043, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_70, c_1005])).
% 31.86/23.50  tff(c_1058, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1043])).
% 31.86/23.50  tff(c_30, plain, (![A_50, B_51]: (r2_hidden('#skF_6'(A_50, B_51), k1_relat_1(B_51)) | ~r2_hidden(A_50, k2_relat_1(B_51)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 31.86/23.50  tff(c_1062, plain, (![A_50]: (r2_hidden('#skF_6'(A_50, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_50, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1058, c_30])).
% 31.86/23.50  tff(c_1069, plain, (![A_50]: (r2_hidden('#skF_6'(A_50, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_50, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1062])).
% 31.86/23.50  tff(c_1078, plain, (![A_161]: (~r2_hidden(A_161, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_104, c_1069])).
% 31.86/23.50  tff(c_1093, plain, (v1_relat_1(k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1078])).
% 31.86/23.50  tff(c_36, plain, (![A_58]: (k1_xboole_0=A_58 | r2_hidden(k4_tarski('#skF_7'(A_58), '#skF_8'(A_58)), A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_105])).
% 31.86/23.50  tff(c_1092, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_1078])).
% 31.86/23.50  tff(c_1147, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1092])).
% 31.86/23.50  tff(c_427, plain, (![C_108, A_109, B_110]: (k7_relat_1(k7_relat_1(C_108, A_109), B_110)=k7_relat_1(C_108, k3_xboole_0(A_109, B_110)) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_68])).
% 31.86/23.50  tff(c_32, plain, (![C_55, A_53, B_54]: (k7_relat_1(k7_relat_1(C_55, A_53), B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 31.86/23.50  tff(c_1547, plain, (![C_180, A_181, B_182]: (k7_relat_1(C_180, k3_xboole_0(A_181, B_182))=k1_xboole_0 | ~r1_xboole_0(A_181, B_182) | ~v1_relat_1(C_180) | ~v1_relat_1(C_180))), inference(superposition, [status(thm), theory('equality')], [c_427, c_32])).
% 31.86/23.50  tff(c_28, plain, (![B_49, A_48]: (k2_relat_1(k7_relat_1(B_49, A_48))=k9_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 31.86/23.50  tff(c_1603, plain, (![C_180, A_181, B_182]: (k9_relat_1(C_180, k3_xboole_0(A_181, B_182))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(C_180) | ~r1_xboole_0(A_181, B_182) | ~v1_relat_1(C_180) | ~v1_relat_1(C_180))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_28])).
% 31.86/23.50  tff(c_68813, plain, (![C_983, A_984, B_985]: (k9_relat_1(C_983, k3_xboole_0(A_984, B_985))=k1_xboole_0 | ~v1_relat_1(C_983) | ~r1_xboole_0(A_984, B_985) | ~v1_relat_1(C_983) | ~v1_relat_1(C_983))), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1603])).
% 31.86/23.50  tff(c_1210, plain, (![C_170, A_171, B_172]: (k3_xboole_0(k9_relat_1(C_170, A_171), k9_relat_1(C_170, B_172))=k9_relat_1(C_170, k3_xboole_0(A_171, B_172)) | ~v2_funct_1(C_170) | ~v1_funct_1(C_170) | ~v1_relat_1(C_170))), inference(cnfTransformation, [status(thm)], [f_125])).
% 31.86/23.50  tff(c_6, plain, (![A_4, B_5]: (~r1_xboole_0(k3_xboole_0(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.86/23.50  tff(c_1228, plain, (![C_170, A_171, B_172]: (~r1_xboole_0(k9_relat_1(C_170, k3_xboole_0(A_171, B_172)), k9_relat_1(C_170, B_172)) | r1_xboole_0(k9_relat_1(C_170, A_171), k9_relat_1(C_170, B_172)) | ~v2_funct_1(C_170) | ~v1_funct_1(C_170) | ~v1_relat_1(C_170))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_6])).
% 31.86/23.50  tff(c_69013, plain, (![C_983, B_985, A_984]: (~r1_xboole_0(k1_xboole_0, k9_relat_1(C_983, B_985)) | r1_xboole_0(k9_relat_1(C_983, A_984), k9_relat_1(C_983, B_985)) | ~v2_funct_1(C_983) | ~v1_funct_1(C_983) | ~v1_relat_1(C_983) | ~v1_relat_1(C_983) | ~r1_xboole_0(A_984, B_985) | ~v1_relat_1(C_983) | ~v1_relat_1(C_983))), inference(superposition, [status(thm), theory('equality')], [c_68813, c_1228])).
% 31.86/23.50  tff(c_151803, plain, (![C_1646, A_1647, B_1648]: (r1_xboole_0(k9_relat_1(C_1646, A_1647), k9_relat_1(C_1646, B_1648)) | ~v2_funct_1(C_1646) | ~v1_funct_1(C_1646) | ~r1_xboole_0(A_1647, B_1648) | ~v1_relat_1(C_1646))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_69013])).
% 31.86/23.50  tff(c_48, plain, (~r1_xboole_0(k9_relat_1('#skF_11', '#skF_9'), k9_relat_1('#skF_11', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.86/23.50  tff(c_151834, plain, (~v2_funct_1('#skF_11') | ~v1_funct_1('#skF_11') | ~r1_xboole_0('#skF_9', '#skF_10') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_151803, c_48])).
% 31.86/23.50  tff(c_152675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_50, c_151834])).
% 31.86/23.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.86/23.50  
% 31.86/23.50  Inference rules
% 31.86/23.50  ----------------------
% 31.86/23.50  #Ref     : 1
% 31.86/23.50  #Sup     : 32966
% 31.86/23.50  #Fact    : 0
% 31.86/23.50  #Define  : 0
% 31.86/23.50  #Split   : 0
% 31.86/23.50  #Chain   : 0
% 31.86/23.50  #Close   : 0
% 31.86/23.50  
% 31.86/23.50  Ordering : KBO
% 31.86/23.50  
% 31.86/23.50  Simplification rules
% 31.86/23.50  ----------------------
% 31.86/23.50  #Subsume      : 4270
% 31.86/23.50  #Demod        : 56008
% 31.86/23.50  #Tautology    : 20902
% 31.86/23.50  #SimpNegUnit  : 6
% 31.86/23.50  #BackRed      : 43
% 31.86/23.50  
% 31.86/23.50  #Partial instantiations: 0
% 31.86/23.50  #Strategies tried      : 1
% 31.86/23.50  
% 31.86/23.50  Timing (in seconds)
% 31.86/23.50  ----------------------
% 31.86/23.50  Preprocessing        : 0.31
% 31.86/23.50  Parsing              : 0.18
% 31.86/23.50  CNF conversion       : 0.02
% 31.86/23.50  Main loop            : 22.38
% 31.86/23.50  Inferencing          : 3.37
% 31.86/23.50  Reduction            : 11.95
% 31.86/23.50  Demodulation         : 10.78
% 31.86/23.50  BG Simplification    : 0.39
% 31.86/23.50  Subsumption          : 6.05
% 31.86/23.50  Abstraction          : 0.69
% 31.86/23.50  MUC search           : 0.00
% 31.86/23.50  Cooper               : 0.00
% 31.86/23.50  Total                : 22.73
% 31.86/23.50  Index Insertion      : 0.00
% 31.86/23.50  Index Deletion       : 0.00
% 31.86/23.50  Index Matching       : 0.00
% 31.86/23.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
