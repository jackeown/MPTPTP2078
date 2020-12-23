%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 736 expanded)
%              Number of leaves         :   40 ( 259 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 (1537 expanded)
%              Number of equality atoms :   64 ( 376 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1739,plain,(
    ! [C_261,A_262,B_263] :
      ( v4_relat_1(C_261,A_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1835,plain,(
    ! [C_269,A_270] :
      ( v4_relat_1(C_269,A_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1739])).

tff(c_1840,plain,(
    ! [A_271,A_272] :
      ( v4_relat_1(A_271,A_272)
      | ~ r1_tarski(A_271,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_1835])).

tff(c_93,plain,(
    ! [A_39,B_40] : v1_relat_1(k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_93])).

tff(c_1235,plain,(
    ! [C_189,A_190,B_191] :
      ( v4_relat_1(C_189,A_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1256,plain,(
    ! [C_192,A_193] :
      ( v4_relat_1(C_192,A_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1235])).

tff(c_1261,plain,(
    ! [A_194,A_195] :
      ( v4_relat_1(A_194,A_195)
      | ~ r1_tarski(A_194,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_1256])).

tff(c_36,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_145,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_151])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) = k1_xboole_0
      | k2_relat_1(A_57) != k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_186,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155,c_176])).

tff(c_189,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_203,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | k1_relat_1(A_60) != k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_206,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155,c_203])).

tff(c_215,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_206])).

tff(c_497,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k7_relset_1(A_109,B_110,C_111,D_112) = k9_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_511,plain,(
    ! [D_112] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_112) = k9_relat_1('#skF_4',D_112) ),
    inference(resolution,[status(thm)],[c_62,c_497])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_538,plain,(
    ! [B_116,A_117] :
      ( k1_tarski(k1_funct_1(B_116,A_117)) = k2_relat_1(B_116)
      | k1_tarski(A_117) != k1_relat_1(B_116)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_547,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_58])).

tff(c_558,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_66,c_547])).

tff(c_576,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_558])).

tff(c_577,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_249,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_264,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_249])).

tff(c_349,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k1_relat_1(B_96),A_97)
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_957,plain,(
    ! [B_175,B_176] :
      ( k1_tarski(B_175) = k1_relat_1(B_176)
      | k1_relat_1(B_176) = k1_xboole_0
      | ~ v4_relat_1(B_176,k1_tarski(B_175))
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_349,c_14])).

tff(c_1003,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_264,c_957])).

tff(c_1029,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1003])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_577,c_1029])).

tff(c_1033,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_44,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(k1_funct_1(B_26,A_25)) = k2_relat_1(B_26)
      | k1_tarski(A_25) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_560,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_58])).

tff(c_572,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_560])).

tff(c_574,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_66,c_572])).

tff(c_575,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_575])).

tff(c_1064,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_1143,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1064])).

tff(c_1147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1143])).

tff(c_1148,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_1221,plain,(
    ! [B_186,A_187] :
      ( r1_tarski(k1_relat_1(B_186),A_187)
      | ~ v4_relat_1(B_186,A_187)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1229,plain,(
    ! [A_187] :
      ( r1_tarski(k1_xboole_0,A_187)
      | ~ v4_relat_1('#skF_4',A_187)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_1221])).

tff(c_1233,plain,(
    ! [A_187] :
      ( r1_tarski(k1_xboole_0,A_187)
      | ~ v4_relat_1('#skF_4',A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1229])).

tff(c_1266,plain,(
    ! [A_195] :
      ( r1_tarski(k1_xboole_0,A_195)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1261,c_1233])).

tff(c_1267,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1149,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_1435,plain,(
    ! [A_227] :
      ( m1_subset_1(A_227,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_227),k2_relat_1(A_227))))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1450,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_1435])).

tff(c_1461,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_66,c_22,c_1450])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1474,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1461,c_26])).

tff(c_1483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1267,c_1474])).

tff(c_1484,plain,(
    ! [A_195] : r1_tarski(k1_xboole_0,A_195) ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1485,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1519,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1485,c_2])).

tff(c_1525,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_1519])).

tff(c_1535,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1149])).

tff(c_187,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_176])).

tff(c_1189,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_1533,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1525,c_1189])).

tff(c_1588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1533])).

tff(c_1589,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1755,plain,(
    ! [B_264,A_265] :
      ( r1_tarski(k1_relat_1(B_264),A_265)
      | ~ v4_relat_1(B_264,A_265)
      | ~ v1_relat_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1770,plain,(
    ! [A_265] :
      ( r1_tarski(k1_xboole_0,A_265)
      | ~ v4_relat_1(k1_xboole_0,A_265)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_1755])).

tff(c_1779,plain,(
    ! [A_265] :
      ( r1_tarski(k1_xboole_0,A_265)
      | ~ v4_relat_1(k1_xboole_0,A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1770])).

tff(c_1848,plain,(
    ! [A_272] :
      ( r1_tarski(k1_xboole_0,A_272)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1840,c_1779])).

tff(c_1852,plain,(
    ! [A_272] : r1_tarski(k1_xboole_0,A_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1848])).

tff(c_2235,plain,(
    ! [A_297] :
      ( m1_subset_1(A_297,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_297),k2_relat_1(A_297))))
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2256,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_2235])).

tff(c_2271,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_66,c_22,c_1148,c_2256])).

tff(c_2310,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2271,c_26])).

tff(c_2324,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2310,c_2])).

tff(c_2334,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_2324])).

tff(c_2348,plain,(
    ! [A_272] : r1_tarski('#skF_4',A_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_1852])).

tff(c_1157,plain,(
    ! [A_22] :
      ( r1_tarski(k9_relat_1('#skF_4',A_22),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_38])).

tff(c_1163,plain,(
    ! [A_178] : r1_tarski(k9_relat_1('#skF_4',A_178),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1157])).

tff(c_1172,plain,(
    ! [A_178] :
      ( k9_relat_1('#skF_4',A_178) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1('#skF_4',A_178)) ) ),
    inference(resolution,[status(thm)],[c_1163,c_2])).

tff(c_1860,plain,(
    ! [A_178] : k9_relat_1('#skF_4',A_178) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_1172])).

tff(c_2345,plain,(
    ! [A_178] : k9_relat_1('#skF_4',A_178) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_1860])).

tff(c_2475,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( k7_relset_1(A_302,B_303,C_304,D_305) = k9_relat_1(C_304,D_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2485,plain,(
    ! [D_305] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_305) = k9_relat_1('#skF_4',D_305) ),
    inference(resolution,[status(thm)],[c_62,c_2475])).

tff(c_2535,plain,(
    ! [D_305] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_305) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_2485])).

tff(c_2536,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_58])).

tff(c_2539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_2536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.78  
% 4.08/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.08/1.78  
% 4.08/1.78  %Foreground sorts:
% 4.08/1.78  
% 4.08/1.78  
% 4.08/1.78  %Background operators:
% 4.08/1.78  
% 4.08/1.78  
% 4.08/1.78  %Foreground operators:
% 4.08/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.08/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.08/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.08/1.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.08/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.08/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.08/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.08/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.08/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.08/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.08/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.08/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.08/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.08/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.08/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.78  
% 4.08/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.80  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.80  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.08/1.80  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.80  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.08/1.80  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.08/1.80  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.08/1.80  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.08/1.80  tff(f_78, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.08/1.80  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.08/1.80  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.08/1.80  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.08/1.80  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.08/1.80  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.08/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.80  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.80  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.08/1.80  tff(c_1739, plain, (![C_261, A_262, B_263]: (v4_relat_1(C_261, A_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/1.80  tff(c_1835, plain, (![C_269, A_270]: (v4_relat_1(C_269, A_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1739])).
% 4.08/1.80  tff(c_1840, plain, (![A_271, A_272]: (v4_relat_1(A_271, A_272) | ~r1_tarski(A_271, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_1835])).
% 4.08/1.80  tff(c_93, plain, (![A_39, B_40]: (v1_relat_1(k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.08/1.80  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_93])).
% 4.08/1.80  tff(c_1235, plain, (![C_189, A_190, B_191]: (v4_relat_1(C_189, A_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/1.80  tff(c_1256, plain, (![C_192, A_193]: (v4_relat_1(C_192, A_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1235])).
% 4.08/1.80  tff(c_1261, plain, (![A_194, A_195]: (v4_relat_1(A_194, A_195) | ~r1_tarski(A_194, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_1256])).
% 4.08/1.80  tff(c_36, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.08/1.80  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.80  tff(c_145, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/1.80  tff(c_151, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_145])).
% 4.08/1.80  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_151])).
% 4.08/1.80  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.80  tff(c_176, plain, (![A_57]: (k1_relat_1(A_57)=k1_xboole_0 | k2_relat_1(A_57)!=k1_xboole_0 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.08/1.80  tff(c_186, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_155, c_176])).
% 4.08/1.80  tff(c_189, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_186])).
% 4.08/1.80  tff(c_203, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | k1_relat_1(A_60)!=k1_xboole_0 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.08/1.80  tff(c_206, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_155, c_203])).
% 4.08/1.80  tff(c_215, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_189, c_206])).
% 4.08/1.80  tff(c_497, plain, (![A_109, B_110, C_111, D_112]: (k7_relset_1(A_109, B_110, C_111, D_112)=k9_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.08/1.80  tff(c_511, plain, (![D_112]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_112)=k9_relat_1('#skF_4', D_112))), inference(resolution, [status(thm)], [c_62, c_497])).
% 4.08/1.80  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.80  tff(c_538, plain, (![B_116, A_117]: (k1_tarski(k1_funct_1(B_116, A_117))=k2_relat_1(B_116) | k1_tarski(A_117)!=k1_relat_1(B_116) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.08/1.80  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.80  tff(c_547, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_538, c_58])).
% 4.08/1.80  tff(c_558, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_66, c_547])).
% 4.08/1.80  tff(c_576, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_558])).
% 4.08/1.80  tff(c_577, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_576])).
% 4.08/1.80  tff(c_249, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/1.80  tff(c_264, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_249])).
% 4.08/1.80  tff(c_349, plain, (![B_96, A_97]: (r1_tarski(k1_relat_1(B_96), A_97) | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.08/1.80  tff(c_14, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_957, plain, (![B_175, B_176]: (k1_tarski(B_175)=k1_relat_1(B_176) | k1_relat_1(B_176)=k1_xboole_0 | ~v4_relat_1(B_176, k1_tarski(B_175)) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_349, c_14])).
% 4.08/1.80  tff(c_1003, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_264, c_957])).
% 4.08/1.80  tff(c_1029, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1003])).
% 4.08/1.80  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_577, c_1029])).
% 4.08/1.80  tff(c_1033, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_576])).
% 4.08/1.80  tff(c_44, plain, (![B_26, A_25]: (k1_tarski(k1_funct_1(B_26, A_25))=k2_relat_1(B_26) | k1_tarski(A_25)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.08/1.80  tff(c_560, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_58])).
% 4.08/1.80  tff(c_572, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_560])).
% 4.08/1.80  tff(c_574, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_66, c_572])).
% 4.08/1.80  tff(c_575, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_574])).
% 4.08/1.80  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1033, c_575])).
% 4.08/1.80  tff(c_1064, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_574])).
% 4.08/1.80  tff(c_1143, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1064])).
% 4.08/1.80  tff(c_1147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_1143])).
% 4.08/1.80  tff(c_1148, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 4.08/1.80  tff(c_1221, plain, (![B_186, A_187]: (r1_tarski(k1_relat_1(B_186), A_187) | ~v4_relat_1(B_186, A_187) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.08/1.80  tff(c_1229, plain, (![A_187]: (r1_tarski(k1_xboole_0, A_187) | ~v4_relat_1('#skF_4', A_187) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1148, c_1221])).
% 4.08/1.80  tff(c_1233, plain, (![A_187]: (r1_tarski(k1_xboole_0, A_187) | ~v4_relat_1('#skF_4', A_187))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1229])).
% 4.08/1.80  tff(c_1266, plain, (![A_195]: (r1_tarski(k1_xboole_0, A_195) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_1261, c_1233])).
% 4.08/1.80  tff(c_1267, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1266])).
% 4.08/1.80  tff(c_1149, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 4.08/1.80  tff(c_1435, plain, (![A_227]: (m1_subset_1(A_227, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_227), k2_relat_1(A_227)))) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.80  tff(c_1450, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1149, c_1435])).
% 4.08/1.80  tff(c_1461, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_66, c_22, c_1450])).
% 4.08/1.80  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.80  tff(c_1474, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1461, c_26])).
% 4.08/1.80  tff(c_1483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1267, c_1474])).
% 4.08/1.80  tff(c_1484, plain, (![A_195]: (r1_tarski(k1_xboole_0, A_195))), inference(splitRight, [status(thm)], [c_1266])).
% 4.08/1.80  tff(c_1485, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1266])).
% 4.08/1.80  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.80  tff(c_1519, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_1485, c_2])).
% 4.08/1.80  tff(c_1525, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_1519])).
% 4.08/1.80  tff(c_1535, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1149])).
% 4.08/1.80  tff(c_187, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_176])).
% 4.08/1.80  tff(c_1189, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_187])).
% 4.08/1.80  tff(c_1533, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1525, c_1189])).
% 4.08/1.80  tff(c_1588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1533])).
% 4.08/1.80  tff(c_1589, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 4.08/1.80  tff(c_1755, plain, (![B_264, A_265]: (r1_tarski(k1_relat_1(B_264), A_265) | ~v4_relat_1(B_264, A_265) | ~v1_relat_1(B_264))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.08/1.80  tff(c_1770, plain, (![A_265]: (r1_tarski(k1_xboole_0, A_265) | ~v4_relat_1(k1_xboole_0, A_265) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1589, c_1755])).
% 4.08/1.80  tff(c_1779, plain, (![A_265]: (r1_tarski(k1_xboole_0, A_265) | ~v4_relat_1(k1_xboole_0, A_265))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1770])).
% 4.08/1.80  tff(c_1848, plain, (![A_272]: (r1_tarski(k1_xboole_0, A_272) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1840, c_1779])).
% 4.08/1.80  tff(c_1852, plain, (![A_272]: (r1_tarski(k1_xboole_0, A_272))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1848])).
% 4.08/1.80  tff(c_2235, plain, (![A_297]: (m1_subset_1(A_297, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_297), k2_relat_1(A_297)))) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.80  tff(c_2256, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1149, c_2235])).
% 4.08/1.80  tff(c_2271, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_66, c_22, c_1148, c_2256])).
% 4.08/1.80  tff(c_2310, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2271, c_26])).
% 4.08/1.80  tff(c_2324, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_2310, c_2])).
% 4.08/1.80  tff(c_2334, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_2324])).
% 4.08/1.80  tff(c_2348, plain, (![A_272]: (r1_tarski('#skF_4', A_272))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_1852])).
% 4.08/1.80  tff(c_1157, plain, (![A_22]: (r1_tarski(k9_relat_1('#skF_4', A_22), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_38])).
% 4.08/1.80  tff(c_1163, plain, (![A_178]: (r1_tarski(k9_relat_1('#skF_4', A_178), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1157])).
% 4.08/1.80  tff(c_1172, plain, (![A_178]: (k9_relat_1('#skF_4', A_178)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1('#skF_4', A_178)))), inference(resolution, [status(thm)], [c_1163, c_2])).
% 4.08/1.80  tff(c_1860, plain, (![A_178]: (k9_relat_1('#skF_4', A_178)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_1172])).
% 4.08/1.80  tff(c_2345, plain, (![A_178]: (k9_relat_1('#skF_4', A_178)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_1860])).
% 4.08/1.80  tff(c_2475, plain, (![A_302, B_303, C_304, D_305]: (k7_relset_1(A_302, B_303, C_304, D_305)=k9_relat_1(C_304, D_305) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.08/1.80  tff(c_2485, plain, (![D_305]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_305)=k9_relat_1('#skF_4', D_305))), inference(resolution, [status(thm)], [c_62, c_2475])).
% 4.08/1.80  tff(c_2535, plain, (![D_305]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_305)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2345, c_2485])).
% 4.08/1.80  tff(c_2536, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2535, c_58])).
% 4.08/1.80  tff(c_2539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2348, c_2536])).
% 4.08/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.80  
% 4.08/1.80  Inference rules
% 4.08/1.80  ----------------------
% 4.08/1.80  #Ref     : 0
% 4.08/1.80  #Sup     : 482
% 4.08/1.80  #Fact    : 0
% 4.08/1.80  #Define  : 0
% 4.08/1.80  #Split   : 20
% 4.08/1.80  #Chain   : 0
% 4.08/1.80  #Close   : 0
% 4.08/1.80  
% 4.08/1.80  Ordering : KBO
% 4.08/1.80  
% 4.08/1.80  Simplification rules
% 4.08/1.80  ----------------------
% 4.08/1.80  #Subsume      : 121
% 4.08/1.80  #Demod        : 485
% 4.08/1.80  #Tautology    : 220
% 4.08/1.80  #SimpNegUnit  : 55
% 4.08/1.80  #BackRed      : 118
% 4.08/1.80  
% 4.08/1.80  #Partial instantiations: 0
% 4.08/1.80  #Strategies tried      : 1
% 4.08/1.80  
% 4.08/1.80  Timing (in seconds)
% 4.08/1.80  ----------------------
% 4.08/1.81  Preprocessing        : 0.35
% 4.08/1.81  Parsing              : 0.19
% 4.08/1.81  CNF conversion       : 0.02
% 4.08/1.81  Main loop            : 0.63
% 4.08/1.81  Inferencing          : 0.22
% 4.08/1.81  Reduction            : 0.22
% 4.08/1.81  Demodulation         : 0.15
% 4.08/1.81  BG Simplification    : 0.03
% 4.08/1.81  Subsumption          : 0.11
% 4.08/1.81  Abstraction          : 0.03
% 4.08/1.81  MUC search           : 0.00
% 4.08/1.81  Cooper               : 0.00
% 4.08/1.81  Total                : 1.01
% 4.08/1.81  Index Insertion      : 0.00
% 4.08/1.81  Index Deletion       : 0.00
% 4.08/1.81  Index Matching       : 0.00
% 4.08/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
