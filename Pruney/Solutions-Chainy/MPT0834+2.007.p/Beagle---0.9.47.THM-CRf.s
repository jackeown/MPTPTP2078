%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 110 expanded)
%              Number of leaves         :   40 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 166 expanded)
%              Number of equality atoms :   39 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1149,plain,(
    ! [A_294,B_295,C_296,D_297] :
      ( k8_relset_1(A_294,B_295,C_296,D_297) = k10_relat_1(C_296,D_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1156,plain,(
    ! [D_297] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_297) = k10_relat_1('#skF_5',D_297) ),
    inference(resolution,[status(thm)],[c_58,c_1149])).

tff(c_810,plain,(
    ! [A_216,B_217,C_218] :
      ( k1_relset_1(A_216,B_217,C_218) = k1_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_819,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_810])).

tff(c_105,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_174,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_174])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_187,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_40])).

tff(c_190,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_187])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_32])).

tff(c_198,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_194])).

tff(c_593,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k7_relset_1(A_170,B_171,C_172,D_173) = k9_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_600,plain,(
    ! [D_173] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_173) = k9_relat_1('#skF_5',D_173) ),
    inference(resolution,[status(thm)],[c_58,c_593])).

tff(c_384,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_393,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_384])).

tff(c_56,plain,
    ( k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relset_1('#skF_3','#skF_4','#skF_5')
    | k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_394,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_85])).

tff(c_601,plain,(
    k9_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_394])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_601])).

tff(c_605,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_820,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_605])).

tff(c_1157,plain,(
    k10_relat_1('#skF_5','#skF_4') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_820])).

tff(c_626,plain,(
    ! [C_177,A_178,B_179] :
      ( v1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_635,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_626])).

tff(c_676,plain,(
    ! [C_189,B_190,A_191] :
      ( v5_relat_1(C_189,B_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_685,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_676])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_17] :
      ( k10_relat_1(A_17,k2_relat_1(A_17)) = k1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_872,plain,(
    ! [C_231,A_232,B_233] :
      ( r1_tarski(k10_relat_1(C_231,A_232),k10_relat_1(C_231,B_233))
      | ~ r1_tarski(A_232,B_233)
      | ~ v1_relat_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1204,plain,(
    ! [A_313,B_314] :
      ( r1_tarski(k1_relat_1(A_313),k10_relat_1(A_313,B_314))
      | ~ r1_tarski(k2_relat_1(A_313),B_314)
      | ~ v1_relat_1(A_313)
      | ~ v1_relat_1(A_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_872])).

tff(c_797,plain,(
    ! [B_214,A_215] :
      ( r1_tarski(k10_relat_1(B_214,A_215),k10_relat_1(B_214,k2_relat_1(B_214)))
      | ~ v1_relat_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_825,plain,(
    ! [A_219,A_220] :
      ( r1_tarski(k10_relat_1(A_219,A_220),k1_relat_1(A_219))
      | ~ v1_relat_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_797])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_831,plain,(
    ! [A_219,A_220] :
      ( k10_relat_1(A_219,A_220) = k1_relat_1(A_219)
      | ~ r1_tarski(k1_relat_1(A_219),k10_relat_1(A_219,A_220))
      | ~ v1_relat_1(A_219) ) ),
    inference(resolution,[status(thm)],[c_825,c_2])).

tff(c_1217,plain,(
    ! [A_315,B_316] :
      ( k10_relat_1(A_315,B_316) = k1_relat_1(A_315)
      | ~ r1_tarski(k2_relat_1(A_315),B_316)
      | ~ v1_relat_1(A_315) ) ),
    inference(resolution,[status(thm)],[c_1204,c_831])).

tff(c_1230,plain,(
    ! [B_317,A_318] :
      ( k10_relat_1(B_317,A_318) = k1_relat_1(B_317)
      | ~ v5_relat_1(B_317,A_318)
      | ~ v1_relat_1(B_317) ) ),
    inference(resolution,[status(thm)],[c_30,c_1217])).

tff(c_1254,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_685,c_1230])).

tff(c_1274,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_1254])).

tff(c_1276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1157,c_1274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:27:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.52  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.34/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.34/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.52  
% 3.42/1.53  tff(f_114, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.42/1.53  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.42/1.53  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.53  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.53  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.53  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.42/1.53  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.42/1.53  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.42/1.53  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.53  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.42/1.53  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.42/1.54  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.42/1.54  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 3.42/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.54  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.42/1.54  tff(c_1149, plain, (![A_294, B_295, C_296, D_297]: (k8_relset_1(A_294, B_295, C_296, D_297)=k10_relat_1(C_296, D_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.54  tff(c_1156, plain, (![D_297]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_297)=k10_relat_1('#skF_5', D_297))), inference(resolution, [status(thm)], [c_58, c_1149])).
% 3.42/1.54  tff(c_810, plain, (![A_216, B_217, C_218]: (k1_relset_1(A_216, B_217, C_218)=k1_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.42/1.54  tff(c_819, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_810])).
% 3.42/1.54  tff(c_105, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.42/1.54  tff(c_114, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_105])).
% 3.42/1.54  tff(c_174, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.42/1.54  tff(c_183, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_174])).
% 3.42/1.54  tff(c_40, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.54  tff(c_187, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_183, c_40])).
% 3.42/1.54  tff(c_190, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_187])).
% 3.42/1.54  tff(c_32, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.54  tff(c_194, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_190, c_32])).
% 3.42/1.54  tff(c_198, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_194])).
% 3.42/1.54  tff(c_593, plain, (![A_170, B_171, C_172, D_173]: (k7_relset_1(A_170, B_171, C_172, D_173)=k9_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.42/1.54  tff(c_600, plain, (![D_173]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_173)=k9_relat_1('#skF_5', D_173))), inference(resolution, [status(thm)], [c_58, c_593])).
% 3.42/1.54  tff(c_384, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.42/1.54  tff(c_393, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_384])).
% 3.42/1.54  tff(c_56, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relset_1('#skF_3', '#skF_4', '#skF_5') | k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.42/1.54  tff(c_85, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 3.42/1.54  tff(c_394, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_85])).
% 3.42/1.54  tff(c_601, plain, (k9_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_394])).
% 3.42/1.54  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_601])).
% 3.42/1.54  tff(c_605, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.42/1.54  tff(c_820, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_605])).
% 3.42/1.54  tff(c_1157, plain, (k10_relat_1('#skF_5', '#skF_4')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_820])).
% 3.42/1.54  tff(c_626, plain, (![C_177, A_178, B_179]: (v1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.42/1.54  tff(c_635, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_626])).
% 3.42/1.54  tff(c_676, plain, (![C_189, B_190, A_191]: (v5_relat_1(C_189, B_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.42/1.54  tff(c_685, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_676])).
% 3.42/1.54  tff(c_30, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.54  tff(c_34, plain, (![A_17]: (k10_relat_1(A_17, k2_relat_1(A_17))=k1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.54  tff(c_872, plain, (![C_231, A_232, B_233]: (r1_tarski(k10_relat_1(C_231, A_232), k10_relat_1(C_231, B_233)) | ~r1_tarski(A_232, B_233) | ~v1_relat_1(C_231))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.42/1.54  tff(c_1204, plain, (![A_313, B_314]: (r1_tarski(k1_relat_1(A_313), k10_relat_1(A_313, B_314)) | ~r1_tarski(k2_relat_1(A_313), B_314) | ~v1_relat_1(A_313) | ~v1_relat_1(A_313))), inference(superposition, [status(thm), theory('equality')], [c_34, c_872])).
% 3.42/1.54  tff(c_797, plain, (![B_214, A_215]: (r1_tarski(k10_relat_1(B_214, A_215), k10_relat_1(B_214, k2_relat_1(B_214))) | ~v1_relat_1(B_214))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.42/1.54  tff(c_825, plain, (![A_219, A_220]: (r1_tarski(k10_relat_1(A_219, A_220), k1_relat_1(A_219)) | ~v1_relat_1(A_219) | ~v1_relat_1(A_219))), inference(superposition, [status(thm), theory('equality')], [c_34, c_797])).
% 3.42/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.54  tff(c_831, plain, (![A_219, A_220]: (k10_relat_1(A_219, A_220)=k1_relat_1(A_219) | ~r1_tarski(k1_relat_1(A_219), k10_relat_1(A_219, A_220)) | ~v1_relat_1(A_219))), inference(resolution, [status(thm)], [c_825, c_2])).
% 3.42/1.54  tff(c_1217, plain, (![A_315, B_316]: (k10_relat_1(A_315, B_316)=k1_relat_1(A_315) | ~r1_tarski(k2_relat_1(A_315), B_316) | ~v1_relat_1(A_315))), inference(resolution, [status(thm)], [c_1204, c_831])).
% 3.42/1.54  tff(c_1230, plain, (![B_317, A_318]: (k10_relat_1(B_317, A_318)=k1_relat_1(B_317) | ~v5_relat_1(B_317, A_318) | ~v1_relat_1(B_317))), inference(resolution, [status(thm)], [c_30, c_1217])).
% 3.42/1.54  tff(c_1254, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_685, c_1230])).
% 3.42/1.54  tff(c_1274, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_1254])).
% 3.42/1.54  tff(c_1276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1157, c_1274])).
% 3.42/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.54  
% 3.42/1.54  Inference rules
% 3.42/1.54  ----------------------
% 3.42/1.54  #Ref     : 0
% 3.42/1.54  #Sup     : 252
% 3.42/1.54  #Fact    : 0
% 3.42/1.54  #Define  : 0
% 3.42/1.54  #Split   : 3
% 3.42/1.54  #Chain   : 0
% 3.42/1.54  #Close   : 0
% 3.42/1.54  
% 3.42/1.54  Ordering : KBO
% 3.42/1.54  
% 3.42/1.54  Simplification rules
% 3.42/1.54  ----------------------
% 3.42/1.54  #Subsume      : 11
% 3.42/1.54  #Demod        : 102
% 3.42/1.54  #Tautology    : 85
% 3.42/1.54  #SimpNegUnit  : 2
% 3.42/1.54  #BackRed      : 5
% 3.42/1.54  
% 3.42/1.54  #Partial instantiations: 0
% 3.42/1.54  #Strategies tried      : 1
% 3.42/1.54  
% 3.42/1.54  Timing (in seconds)
% 3.42/1.54  ----------------------
% 3.42/1.54  Preprocessing        : 0.34
% 3.42/1.54  Parsing              : 0.18
% 3.42/1.54  CNF conversion       : 0.02
% 3.42/1.54  Main loop            : 0.44
% 3.42/1.54  Inferencing          : 0.18
% 3.42/1.54  Reduction            : 0.13
% 3.42/1.54  Demodulation         : 0.09
% 3.42/1.54  BG Simplification    : 0.02
% 3.42/1.54  Subsumption          : 0.07
% 3.42/1.54  Abstraction          : 0.02
% 3.42/1.54  MUC search           : 0.00
% 3.42/1.54  Cooper               : 0.00
% 3.42/1.54  Total                : 0.81
% 3.42/1.54  Index Insertion      : 0.00
% 3.42/1.54  Index Deletion       : 0.00
% 3.42/1.54  Index Matching       : 0.00
% 3.42/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
