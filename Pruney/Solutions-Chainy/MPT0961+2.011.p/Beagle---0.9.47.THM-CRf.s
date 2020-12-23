%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 533 expanded)
%              Number of leaves         :   29 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 (1219 expanded)
%              Number of equality atoms :   46 ( 358 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1791,plain,(
    ! [A_214] :
      ( r1_tarski(A_214,k2_zfmisc_1(k1_relat_1(A_214),k2_relat_1(A_214)))
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_281,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_618,plain,(
    ! [A_116,B_117,A_118] :
      ( k1_relset_1(A_116,B_117,A_118) = k1_relat_1(A_118)
      | ~ r1_tarski(A_118,k2_zfmisc_1(A_116,B_117)) ) ),
    inference(resolution,[status(thm)],[c_12,c_281])).

tff(c_638,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_618])).

tff(c_530,plain,(
    ! [B_100,C_101,A_102] :
      ( k1_xboole_0 = B_100
      | v1_funct_2(C_101,A_102,B_100)
      | k1_relset_1(A_102,B_100,C_101) != A_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_874,plain,(
    ! [B_141,A_142,A_143] :
      ( k1_xboole_0 = B_141
      | v1_funct_2(A_142,A_143,B_141)
      | k1_relset_1(A_143,B_141,A_142) != A_143
      | ~ r1_tarski(A_142,k2_zfmisc_1(A_143,B_141)) ) ),
    inference(resolution,[status(thm)],[c_12,c_530])).

tff(c_1295,plain,(
    ! [A_166] :
      ( k2_relat_1(A_166) = k1_xboole_0
      | v1_funct_2(A_166,k1_relat_1(A_166),k2_relat_1(A_166))
      | k1_relset_1(k1_relat_1(A_166),k2_relat_1(A_166),A_166) != k1_relat_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(resolution,[status(thm)],[c_16,c_874])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1302,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1295,c_98])).

tff(c_1317,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1302])).

tff(c_1320,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1317])).

tff(c_1323,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_1320])).

tff(c_1327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1323])).

tff(c_1328,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1343,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_16])).

tff(c_1353,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_1343])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1374,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1353,c_2])).

tff(c_80,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_30,A_31)),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [B_32] :
      ( k1_relat_1(k7_relat_1(B_32,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [B_32] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_18])).

tff(c_100,plain,(
    ! [B_33] :
      ( ~ v1_relat_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_102,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_107,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_124,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [C_39] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_140,plain,(
    ! [A_40] :
      ( v1_relat_1(A_40)
      | ~ r1_tarski(A_40,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_148,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_107,c_140])).

tff(c_28,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_49,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_248,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_251,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_251])).

tff(c_257,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_210,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [C_59,A_2] :
      ( v4_relat_1(C_59,A_2)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_274,plain,(
    ! [A_69] : v4_relat_1(k1_xboole_0,A_69) ),
    inference(resolution,[status(thm)],[c_257,c_217])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_277,plain,(
    ! [A_69] :
      ( k7_relat_1(k1_xboole_0,A_69) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_274,c_14])).

tff(c_294,plain,(
    ! [A_74] : k7_relat_1(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_277])).

tff(c_85,plain,(
    ! [B_30] :
      ( k1_relat_1(k7_relat_1(B_30,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_304,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_85])).

tff(c_314,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_304])).

tff(c_307,plain,(
    ! [A_74] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_74)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_18])).

tff(c_316,plain,(
    ! [A_74] : r1_tarski(k1_relat_1(k1_xboole_0),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_307])).

tff(c_329,plain,(
    ! [A_74] : r1_tarski(k1_xboole_0,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_316])).

tff(c_622,plain,(
    ! [A_116,B_117] : k1_relset_1(A_116,B_117,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_329,c_618])).

tff(c_637,plain,(
    ! [A_116,B_117] : k1_relset_1(A_116,B_117,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_622])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_720,plain,(
    ! [C_125,B_126] :
      ( v1_funct_2(C_125,k1_xboole_0,B_126)
      | k1_relset_1(k1_xboole_0,B_126,C_125) != k1_xboole_0
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_722,plain,(
    ! [B_126] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_126)
      | k1_relset_1(k1_xboole_0,B_126,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_257,c_720])).

tff(c_728,plain,(
    ! [B_126] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_722])).

tff(c_1395,plain,(
    ! [B_126] : v1_funct_2('#skF_1','#skF_1',B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1374,c_728])).

tff(c_1414,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1374,c_314])).

tff(c_1330,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_98])).

tff(c_1377,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1330])).

tff(c_1490,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1377])).

tff(c_1646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1490])).

tff(c_1647,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1703,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1647])).

tff(c_1800,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1791,c_1703])).

tff(c_1812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:25:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.57  
% 3.72/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.72/1.57  
% 3.72/1.57  %Foreground sorts:
% 3.72/1.57  
% 3.72/1.57  
% 3.72/1.57  %Background operators:
% 3.72/1.57  
% 3.72/1.57  
% 3.72/1.57  %Foreground operators:
% 3.72/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.72/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.72/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.72/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.57  
% 3.72/1.59  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.72/1.59  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.72/1.59  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.72/1.59  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.72/1.59  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.72/1.59  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.72/1.59  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.72/1.59  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.72/1.59  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.72/1.59  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.72/1.59  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.72/1.59  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.59  tff(c_1791, plain, (![A_214]: (r1_tarski(A_214, k2_zfmisc_1(k1_relat_1(A_214), k2_relat_1(A_214))) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.59  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.59  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.72/1.59  tff(c_16, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.59  tff(c_281, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.72/1.59  tff(c_618, plain, (![A_116, B_117, A_118]: (k1_relset_1(A_116, B_117, A_118)=k1_relat_1(A_118) | ~r1_tarski(A_118, k2_zfmisc_1(A_116, B_117)))), inference(resolution, [status(thm)], [c_12, c_281])).
% 3.72/1.59  tff(c_638, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_618])).
% 3.72/1.59  tff(c_530, plain, (![B_100, C_101, A_102]: (k1_xboole_0=B_100 | v1_funct_2(C_101, A_102, B_100) | k1_relset_1(A_102, B_100, C_101)!=A_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.72/1.59  tff(c_874, plain, (![B_141, A_142, A_143]: (k1_xboole_0=B_141 | v1_funct_2(A_142, A_143, B_141) | k1_relset_1(A_143, B_141, A_142)!=A_143 | ~r1_tarski(A_142, k2_zfmisc_1(A_143, B_141)))), inference(resolution, [status(thm)], [c_12, c_530])).
% 3.72/1.59  tff(c_1295, plain, (![A_166]: (k2_relat_1(A_166)=k1_xboole_0 | v1_funct_2(A_166, k1_relat_1(A_166), k2_relat_1(A_166)) | k1_relset_1(k1_relat_1(A_166), k2_relat_1(A_166), A_166)!=k1_relat_1(A_166) | ~v1_relat_1(A_166))), inference(resolution, [status(thm)], [c_16, c_874])).
% 3.72/1.59  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.59  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.59  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.72/1.59  tff(c_98, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.72/1.59  tff(c_1302, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1295, c_98])).
% 3.72/1.59  tff(c_1317, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1302])).
% 3.72/1.59  tff(c_1320, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1317])).
% 3.72/1.59  tff(c_1323, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_638, c_1320])).
% 3.72/1.59  tff(c_1327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1323])).
% 3.72/1.59  tff(c_1328, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1317])).
% 3.72/1.59  tff(c_1343, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1328, c_16])).
% 3.72/1.59  tff(c_1353, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_1343])).
% 3.72/1.59  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.59  tff(c_1374, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1353, c_2])).
% 3.72/1.59  tff(c_80, plain, (![B_30, A_31]: (r1_tarski(k1_relat_1(k7_relat_1(B_30, A_31)), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.59  tff(c_86, plain, (![B_32]: (k1_relat_1(k7_relat_1(B_32, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.72/1.59  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.59  tff(c_92, plain, (![B_32]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(B_32) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_86, c_18])).
% 3.72/1.59  tff(c_100, plain, (![B_33]: (~v1_relat_1(B_33) | ~v1_relat_1(B_33))), inference(splitLeft, [status(thm)], [c_92])).
% 3.72/1.59  tff(c_102, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_100])).
% 3.72/1.59  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_102])).
% 3.72/1.59  tff(c_107, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_92])).
% 3.72/1.59  tff(c_124, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.72/1.59  tff(c_134, plain, (![C_39]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_124])).
% 3.72/1.59  tff(c_140, plain, (![A_40]: (v1_relat_1(A_40) | ~r1_tarski(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_134])).
% 3.72/1.59  tff(c_148, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_140])).
% 3.72/1.59  tff(c_28, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.72/1.59  tff(c_49, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 3.72/1.59  tff(c_248, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_49])).
% 3.72/1.59  tff(c_251, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_248])).
% 3.72/1.59  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_251])).
% 3.72/1.59  tff(c_257, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_49])).
% 3.72/1.59  tff(c_210, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.72/1.59  tff(c_217, plain, (![C_59, A_2]: (v4_relat_1(C_59, A_2) | ~m1_subset_1(C_59, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_210])).
% 3.72/1.59  tff(c_274, plain, (![A_69]: (v4_relat_1(k1_xboole_0, A_69))), inference(resolution, [status(thm)], [c_257, c_217])).
% 3.72/1.59  tff(c_14, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.72/1.59  tff(c_277, plain, (![A_69]: (k7_relat_1(k1_xboole_0, A_69)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_274, c_14])).
% 3.72/1.59  tff(c_294, plain, (![A_74]: (k7_relat_1(k1_xboole_0, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_277])).
% 3.72/1.59  tff(c_85, plain, (![B_30]: (k1_relat_1(k7_relat_1(B_30, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.72/1.59  tff(c_304, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_85])).
% 3.72/1.59  tff(c_314, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_304])).
% 3.72/1.59  tff(c_307, plain, (![A_74]: (r1_tarski(k1_relat_1(k1_xboole_0), A_74) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_294, c_18])).
% 3.72/1.59  tff(c_316, plain, (![A_74]: (r1_tarski(k1_relat_1(k1_xboole_0), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_307])).
% 3.72/1.59  tff(c_329, plain, (![A_74]: (r1_tarski(k1_xboole_0, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_316])).
% 3.72/1.59  tff(c_622, plain, (![A_116, B_117]: (k1_relset_1(A_116, B_117, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_329, c_618])).
% 3.72/1.59  tff(c_637, plain, (![A_116, B_117]: (k1_relset_1(A_116, B_117, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_622])).
% 3.72/1.59  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.72/1.59  tff(c_32, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.72/1.59  tff(c_720, plain, (![C_125, B_126]: (v1_funct_2(C_125, k1_xboole_0, B_126) | k1_relset_1(k1_xboole_0, B_126, C_125)!=k1_xboole_0 | ~m1_subset_1(C_125, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 3.72/1.59  tff(c_722, plain, (![B_126]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_126) | k1_relset_1(k1_xboole_0, B_126, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_257, c_720])).
% 3.72/1.59  tff(c_728, plain, (![B_126]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_722])).
% 3.72/1.59  tff(c_1395, plain, (![B_126]: (v1_funct_2('#skF_1', '#skF_1', B_126))), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_1374, c_728])).
% 3.72/1.59  tff(c_1414, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_1374, c_314])).
% 3.72/1.59  tff(c_1330, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_98])).
% 3.72/1.59  tff(c_1377, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_1330])).
% 3.72/1.59  tff(c_1490, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1377])).
% 3.72/1.59  tff(c_1646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1490])).
% 3.72/1.59  tff(c_1647, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 3.72/1.59  tff(c_1703, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1647])).
% 3.72/1.59  tff(c_1800, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1791, c_1703])).
% 3.72/1.59  tff(c_1812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1800])).
% 3.72/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.59  
% 3.72/1.59  Inference rules
% 3.72/1.59  ----------------------
% 3.72/1.59  #Ref     : 0
% 3.72/1.59  #Sup     : 368
% 3.72/1.59  #Fact    : 0
% 3.72/1.59  #Define  : 0
% 3.72/1.59  #Split   : 5
% 3.72/1.59  #Chain   : 0
% 3.72/1.59  #Close   : 0
% 3.72/1.59  
% 3.72/1.59  Ordering : KBO
% 3.72/1.59  
% 3.72/1.59  Simplification rules
% 3.72/1.59  ----------------------
% 3.72/1.59  #Subsume      : 59
% 3.72/1.59  #Demod        : 415
% 3.72/1.59  #Tautology    : 169
% 3.72/1.59  #SimpNegUnit  : 0
% 3.72/1.59  #BackRed      : 61
% 3.72/1.59  
% 3.72/1.59  #Partial instantiations: 0
% 3.72/1.59  #Strategies tried      : 1
% 3.72/1.59  
% 3.72/1.59  Timing (in seconds)
% 3.72/1.59  ----------------------
% 3.72/1.60  Preprocessing        : 0.32
% 3.72/1.60  Parsing              : 0.17
% 3.72/1.60  CNF conversion       : 0.02
% 3.72/1.60  Main loop            : 0.51
% 3.72/1.60  Inferencing          : 0.19
% 3.72/1.60  Reduction            : 0.16
% 3.72/1.60  Demodulation         : 0.11
% 3.72/1.60  BG Simplification    : 0.03
% 3.72/1.60  Subsumption          : 0.09
% 3.72/1.60  Abstraction          : 0.03
% 3.72/1.60  MUC search           : 0.00
% 3.72/1.60  Cooper               : 0.00
% 3.72/1.60  Total                : 0.87
% 3.72/1.60  Index Insertion      : 0.00
% 3.72/1.60  Index Deletion       : 0.00
% 3.72/1.60  Index Matching       : 0.00
% 3.72/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
