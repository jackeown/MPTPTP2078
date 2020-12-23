%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 215 expanded)
%              Number of leaves         :   42 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 427 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_131,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_144,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_131])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_153,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_144,c_34])).

tff(c_180,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k2_relat_1(B_25)
      | k1_tarski(A_24) != k1_relat_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_352,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_362,plain,(
    ! [D_98] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_98) = k9_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_52,c_352])).

tff(c_48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_473,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_48])).

tff(c_485,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_473])).

tff(c_487,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_56,c_485])).

tff(c_517,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_154,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_167,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_225,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_228,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_225])).

tff(c_234,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_228])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_264,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_36])).

tff(c_268,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_264])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_518,plain,(
    ! [B_121,C_122,A_123] :
      ( k2_tarski(B_121,C_122) = A_123
      | k1_tarski(C_122) = A_123
      | k1_tarski(B_121) = A_123
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,k2_tarski(B_121,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_550,plain,(
    ! [A_1,A_123] :
      ( k2_tarski(A_1,A_1) = A_123
      | k1_tarski(A_1) = A_123
      | k1_tarski(A_1) = A_123
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_518])).

tff(c_782,plain,(
    ! [A_147,A_148] :
      ( k1_tarski(A_147) = A_148
      | k1_tarski(A_147) = A_148
      | k1_tarski(A_147) = A_148
      | k1_xboole_0 = A_148
      | ~ r1_tarski(A_148,k1_tarski(A_147)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_550])).

tff(c_800,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_782])).

tff(c_828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_517,c_517,c_517,c_800])).

tff(c_829,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_943,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_829])).

tff(c_947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_943])).

tff(c_948,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_954,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_96])).

tff(c_28,plain,(
    ! [A_18] : k9_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_955,plain,(
    ! [A_18] : k9_relat_1('#skF_4',A_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_948,c_28])).

tff(c_956,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_18])).

tff(c_1163,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k7_relset_1(A_196,B_197,C_198,D_199) = k9_relat_1(C_198,D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1166,plain,(
    ! [A_196,B_197,D_199] : k7_relset_1(A_196,B_197,'#skF_4',D_199) = k9_relat_1('#skF_4',D_199) ),
    inference(resolution,[status(thm)],[c_956,c_1163])).

tff(c_1171,plain,(
    ! [A_196,B_197,D_199] : k7_relset_1(A_196,B_197,'#skF_4',D_199) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_1166])).

tff(c_1173,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_48])).

tff(c_1176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_1173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.46  
% 3.30/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.30/1.46  
% 3.30/1.46  %Foreground sorts:
% 3.30/1.46  
% 3.30/1.46  
% 3.30/1.46  %Background operators:
% 3.30/1.46  
% 3.30/1.46  
% 3.30/1.46  %Foreground operators:
% 3.30/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.30/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.30/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.30/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.30/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.46  
% 3.33/1.48  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.33/1.48  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.33/1.48  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.33/1.48  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.33/1.48  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.33/1.48  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.48  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.33/1.48  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.33/1.48  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.33/1.48  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.33/1.48  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.33/1.48  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.33/1.48  tff(f_64, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.33/1.48  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.33/1.48  tff(c_131, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.33/1.48  tff(c_144, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_131])).
% 3.33/1.48  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.33/1.48  tff(c_34, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.48  tff(c_153, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_144, c_34])).
% 3.33/1.48  tff(c_180, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_153])).
% 3.33/1.48  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.33/1.48  tff(c_38, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k2_relat_1(B_25) | k1_tarski(A_24)!=k1_relat_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.48  tff(c_352, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.33/1.48  tff(c_362, plain, (![D_98]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_98)=k9_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_52, c_352])).
% 3.33/1.48  tff(c_48, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.33/1.48  tff(c_473, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_48])).
% 3.33/1.48  tff(c_485, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_473])).
% 3.33/1.48  tff(c_487, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_56, c_485])).
% 3.33/1.48  tff(c_517, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_487])).
% 3.33/1.48  tff(c_154, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.33/1.48  tff(c_167, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_154])).
% 3.33/1.48  tff(c_225, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.33/1.48  tff(c_228, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_167, c_225])).
% 3.33/1.48  tff(c_234, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_228])).
% 3.33/1.48  tff(c_36, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.33/1.48  tff(c_264, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_234, c_36])).
% 3.33/1.48  tff(c_268, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_264])).
% 3.33/1.48  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.48  tff(c_518, plain, (![B_121, C_122, A_123]: (k2_tarski(B_121, C_122)=A_123 | k1_tarski(C_122)=A_123 | k1_tarski(B_121)=A_123 | k1_xboole_0=A_123 | ~r1_tarski(A_123, k2_tarski(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.48  tff(c_550, plain, (![A_1, A_123]: (k2_tarski(A_1, A_1)=A_123 | k1_tarski(A_1)=A_123 | k1_tarski(A_1)=A_123 | k1_xboole_0=A_123 | ~r1_tarski(A_123, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_518])).
% 3.33/1.48  tff(c_782, plain, (![A_147, A_148]: (k1_tarski(A_147)=A_148 | k1_tarski(A_147)=A_148 | k1_tarski(A_147)=A_148 | k1_xboole_0=A_148 | ~r1_tarski(A_148, k1_tarski(A_147)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_550])).
% 3.33/1.48  tff(c_800, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_782])).
% 3.33/1.48  tff(c_828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_517, c_517, c_517, c_800])).
% 3.33/1.48  tff(c_829, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_487])).
% 3.33/1.48  tff(c_943, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_829])).
% 3.33/1.48  tff(c_947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_943])).
% 3.33/1.48  tff(c_948, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_153])).
% 3.33/1.48  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.48  tff(c_88, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.33/1.48  tff(c_96, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_18, c_88])).
% 3.33/1.48  tff(c_954, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_948, c_96])).
% 3.33/1.48  tff(c_28, plain, (![A_18]: (k9_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.33/1.48  tff(c_955, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_948, c_948, c_28])).
% 3.33/1.48  tff(c_956, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_948, c_18])).
% 3.33/1.48  tff(c_1163, plain, (![A_196, B_197, C_198, D_199]: (k7_relset_1(A_196, B_197, C_198, D_199)=k9_relat_1(C_198, D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.33/1.48  tff(c_1166, plain, (![A_196, B_197, D_199]: (k7_relset_1(A_196, B_197, '#skF_4', D_199)=k9_relat_1('#skF_4', D_199))), inference(resolution, [status(thm)], [c_956, c_1163])).
% 3.33/1.48  tff(c_1171, plain, (![A_196, B_197, D_199]: (k7_relset_1(A_196, B_197, '#skF_4', D_199)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_955, c_1166])).
% 3.33/1.48  tff(c_1173, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_48])).
% 3.33/1.48  tff(c_1176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_954, c_1173])).
% 3.33/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  
% 3.33/1.48  Inference rules
% 3.33/1.48  ----------------------
% 3.33/1.48  #Ref     : 0
% 3.33/1.48  #Sup     : 218
% 3.33/1.48  #Fact    : 0
% 3.33/1.48  #Define  : 0
% 3.33/1.48  #Split   : 6
% 3.33/1.48  #Chain   : 0
% 3.33/1.48  #Close   : 0
% 3.33/1.48  
% 3.33/1.48  Ordering : KBO
% 3.33/1.48  
% 3.33/1.48  Simplification rules
% 3.33/1.48  ----------------------
% 3.33/1.48  #Subsume      : 1
% 3.33/1.48  #Demod        : 132
% 3.33/1.48  #Tautology    : 108
% 3.33/1.48  #SimpNegUnit  : 15
% 3.33/1.48  #BackRed      : 18
% 3.33/1.48  
% 3.33/1.48  #Partial instantiations: 0
% 3.33/1.48  #Strategies tried      : 1
% 3.33/1.48  
% 3.33/1.48  Timing (in seconds)
% 3.33/1.48  ----------------------
% 3.33/1.48  Preprocessing        : 0.31
% 3.33/1.48  Parsing              : 0.16
% 3.33/1.48  CNF conversion       : 0.02
% 3.33/1.48  Main loop            : 0.40
% 3.33/1.48  Inferencing          : 0.15
% 3.33/1.48  Reduction            : 0.13
% 3.33/1.48  Demodulation         : 0.09
% 3.33/1.48  BG Simplification    : 0.02
% 3.33/1.48  Subsumption          : 0.06
% 3.33/1.48  Abstraction          : 0.02
% 3.33/1.48  MUC search           : 0.00
% 3.33/1.48  Cooper               : 0.00
% 3.33/1.48  Total                : 0.75
% 3.33/1.48  Index Insertion      : 0.00
% 3.33/1.48  Index Deletion       : 0.00
% 3.33/1.48  Index Matching       : 0.00
% 3.33/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
