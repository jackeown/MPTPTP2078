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
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 311 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 759 expanded)
%              Number of equality atoms :   48 ( 239 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_50,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1538,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,k2_zfmisc_1(k1_relat_1(A_138),k2_relat_1(A_138)))
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_213,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_384,plain,(
    ! [A_65,B_66,A_67] :
      ( k1_relset_1(A_65,B_66,A_67) = k1_relat_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_12,c_213])).

tff(c_394,plain,(
    ! [A_9] :
      ( k1_relset_1(k1_relat_1(A_9),k2_relat_1(A_9),A_9) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_384])).

tff(c_321,plain,(
    ! [B_56,C_57,A_58] :
      ( k1_xboole_0 = B_56
      | v1_funct_2(C_57,A_58,B_56)
      | k1_relset_1(A_58,B_56,C_57) != A_58
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1030,plain,(
    ! [B_112,A_113,A_114] :
      ( k1_xboole_0 = B_112
      | v1_funct_2(A_113,A_114,B_112)
      | k1_relset_1(A_114,B_112,A_113) != A_114
      | ~ r1_tarski(A_113,k2_zfmisc_1(A_114,B_112)) ) ),
    inference(resolution,[status(thm)],[c_12,c_321])).

tff(c_1158,plain,(
    ! [A_124] :
      ( k2_relat_1(A_124) = k1_xboole_0
      | v1_funct_2(A_124,k1_relat_1(A_124),k2_relat_1(A_124))
      | k1_relset_1(k1_relat_1(A_124),k2_relat_1(A_124),A_124) != k1_relat_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_16,c_1030])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_75,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1161,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1158,c_75])).

tff(c_1182,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1161])).

tff(c_1187,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1182])).

tff(c_1190,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_1187])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1190])).

tff(c_1195,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1182])).

tff(c_1251,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_16])).

tff(c_1289,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_1251])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1328,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1289,c_2])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35)))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_134,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_6,c_24,c_128])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34])).

tff(c_149,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_152,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_152])).

tff(c_158,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_242,plain,(
    ! [B_46,C_47] :
      ( k1_relset_1(k1_xboole_0,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_213])).

tff(c_244,plain,(
    ! [B_46] : k1_relset_1(k1_xboole_0,B_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_158,c_242])).

tff(c_249,plain,(
    ! [B_46] : k1_relset_1(k1_xboole_0,B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_244])).

tff(c_38,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_630,plain,(
    ! [C_81,B_82] :
      ( v1_funct_2(C_81,k1_xboole_0,B_82)
      | k1_relset_1(k1_xboole_0,B_82,C_81) != k1_xboole_0
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_632,plain,(
    ! [B_82] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_82)
      | k1_relset_1(k1_xboole_0,B_82,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_158,c_630])).

tff(c_638,plain,(
    ! [B_82] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_632])).

tff(c_1353,plain,(
    ! [B_82] : v1_funct_2('#skF_1','#skF_1',B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1328,c_638])).

tff(c_266,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(A_51),k1_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_275,plain,(
    ! [A_51] :
      ( r1_tarski(k1_relat_1(A_51),k1_xboole_0)
      | ~ r1_tarski(A_51,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_292,plain,(
    ! [A_54] :
      ( r1_tarski(k1_relat_1(A_54),k1_xboole_0)
      | ~ r1_tarski(A_54,k1_xboole_0)
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_275])).

tff(c_312,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) = k1_xboole_0
      | ~ r1_tarski(A_54,k1_xboole_0)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_292,c_2])).

tff(c_1299,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1289,c_312])).

tff(c_1320,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1299])).

tff(c_1398,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1320])).

tff(c_1197,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_75])).

tff(c_1330,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1197])).

tff(c_1480,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1330])).

tff(c_1485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1480])).

tff(c_1486,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1520,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1486])).

tff(c_1544,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1538,c_1520])).

tff(c_1555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.63  
% 3.75/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.63  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.75/1.63  
% 3.75/1.63  %Foreground sorts:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Background operators:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Foreground operators:
% 3.75/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.75/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.63  
% 3.75/1.65  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.75/1.65  tff(f_50, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.75/1.65  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.65  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.75/1.65  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.75/1.65  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.75/1.65  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.75/1.65  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.75/1.65  tff(f_65, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.75/1.65  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.75/1.65  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.75/1.65  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.65  tff(c_1538, plain, (![A_138]: (r1_tarski(A_138, k2_zfmisc_1(k1_relat_1(A_138), k2_relat_1(A_138))) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.65  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.75/1.65  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.65  tff(c_16, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.65  tff(c_213, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.75/1.65  tff(c_384, plain, (![A_65, B_66, A_67]: (k1_relset_1(A_65, B_66, A_67)=k1_relat_1(A_67) | ~r1_tarski(A_67, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_12, c_213])).
% 3.75/1.65  tff(c_394, plain, (![A_9]: (k1_relset_1(k1_relat_1(A_9), k2_relat_1(A_9), A_9)=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_384])).
% 3.75/1.65  tff(c_321, plain, (![B_56, C_57, A_58]: (k1_xboole_0=B_56 | v1_funct_2(C_57, A_58, B_56) | k1_relset_1(A_58, B_56, C_57)!=A_58 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_56))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.65  tff(c_1030, plain, (![B_112, A_113, A_114]: (k1_xboole_0=B_112 | v1_funct_2(A_113, A_114, B_112) | k1_relset_1(A_114, B_112, A_113)!=A_114 | ~r1_tarski(A_113, k2_zfmisc_1(A_114, B_112)))), inference(resolution, [status(thm)], [c_12, c_321])).
% 3.75/1.65  tff(c_1158, plain, (![A_124]: (k2_relat_1(A_124)=k1_xboole_0 | v1_funct_2(A_124, k1_relat_1(A_124), k2_relat_1(A_124)) | k1_relset_1(k1_relat_1(A_124), k2_relat_1(A_124), A_124)!=k1_relat_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_16, c_1030])).
% 3.75/1.65  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.65  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.65  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 3.75/1.65  tff(c_75, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.75/1.65  tff(c_1161, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1158, c_75])).
% 3.75/1.65  tff(c_1182, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1161])).
% 3.75/1.65  tff(c_1187, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1182])).
% 3.75/1.65  tff(c_1190, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_394, c_1187])).
% 3.75/1.65  tff(c_1194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1190])).
% 3.75/1.65  tff(c_1195, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1182])).
% 3.75/1.65  tff(c_1251, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1195, c_16])).
% 3.75/1.65  tff(c_1289, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_1251])).
% 3.75/1.65  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.75/1.65  tff(c_1328, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1289, c_2])).
% 3.75/1.65  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.75/1.65  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.65  tff(c_28, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.75/1.65  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_28])).
% 3.75/1.65  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.75/1.65  tff(c_122, plain, (![A_35]: (r1_tarski(A_35, k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35))) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.65  tff(c_128, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_122])).
% 3.75/1.65  tff(c_134, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_6, c_24, c_128])).
% 3.75/1.65  tff(c_34, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.65  tff(c_56, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34])).
% 3.75/1.65  tff(c_149, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_56])).
% 3.75/1.65  tff(c_152, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_149])).
% 3.75/1.65  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_152])).
% 3.75/1.65  tff(c_158, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_56])).
% 3.75/1.65  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.65  tff(c_242, plain, (![B_46, C_47]: (k1_relset_1(k1_xboole_0, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_213])).
% 3.75/1.65  tff(c_244, plain, (![B_46]: (k1_relset_1(k1_xboole_0, B_46, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_158, c_242])).
% 3.75/1.65  tff(c_249, plain, (![B_46]: (k1_relset_1(k1_xboole_0, B_46, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_244])).
% 3.75/1.65  tff(c_38, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.65  tff(c_630, plain, (![C_81, B_82]: (v1_funct_2(C_81, k1_xboole_0, B_82) | k1_relset_1(k1_xboole_0, B_82, C_81)!=k1_xboole_0 | ~m1_subset_1(C_81, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38])).
% 3.75/1.65  tff(c_632, plain, (![B_82]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_82) | k1_relset_1(k1_xboole_0, B_82, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_630])).
% 3.75/1.65  tff(c_638, plain, (![B_82]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_632])).
% 3.75/1.65  tff(c_1353, plain, (![B_82]: (v1_funct_2('#skF_1', '#skF_1', B_82))), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1328, c_638])).
% 3.75/1.65  tff(c_266, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(A_51), k1_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.75/1.65  tff(c_275, plain, (![A_51]: (r1_tarski(k1_relat_1(A_51), k1_xboole_0) | ~r1_tarski(A_51, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_24, c_266])).
% 3.75/1.65  tff(c_292, plain, (![A_54]: (r1_tarski(k1_relat_1(A_54), k1_xboole_0) | ~r1_tarski(A_54, k1_xboole_0) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_275])).
% 3.75/1.65  tff(c_312, plain, (![A_54]: (k1_relat_1(A_54)=k1_xboole_0 | ~r1_tarski(A_54, k1_xboole_0) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_292, c_2])).
% 3.75/1.65  tff(c_1299, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1289, c_312])).
% 3.75/1.65  tff(c_1320, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1299])).
% 3.75/1.65  tff(c_1398, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1320])).
% 3.75/1.65  tff(c_1197, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_75])).
% 3.75/1.65  tff(c_1330, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1197])).
% 3.75/1.65  tff(c_1480, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1330])).
% 3.75/1.65  tff(c_1485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1480])).
% 3.75/1.65  tff(c_1486, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 3.75/1.65  tff(c_1520, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1486])).
% 3.75/1.65  tff(c_1544, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1538, c_1520])).
% 3.75/1.65  tff(c_1555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1544])).
% 3.75/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  Inference rules
% 3.75/1.65  ----------------------
% 3.75/1.65  #Ref     : 0
% 3.75/1.65  #Sup     : 324
% 3.75/1.65  #Fact    : 0
% 3.75/1.65  #Define  : 0
% 3.75/1.65  #Split   : 3
% 3.75/1.65  #Chain   : 0
% 3.75/1.65  #Close   : 0
% 3.75/1.65  
% 3.75/1.65  Ordering : KBO
% 3.75/1.65  
% 3.75/1.65  Simplification rules
% 3.75/1.65  ----------------------
% 3.75/1.65  #Subsume      : 48
% 3.75/1.65  #Demod        : 515
% 3.75/1.65  #Tautology    : 183
% 3.75/1.65  #SimpNegUnit  : 0
% 3.75/1.65  #BackRed      : 62
% 3.75/1.65  
% 3.75/1.65  #Partial instantiations: 0
% 3.75/1.65  #Strategies tried      : 1
% 3.75/1.65  
% 3.75/1.65  Timing (in seconds)
% 3.75/1.65  ----------------------
% 3.75/1.65  Preprocessing        : 0.33
% 3.75/1.65  Parsing              : 0.17
% 3.75/1.65  CNF conversion       : 0.02
% 3.75/1.65  Main loop            : 0.55
% 3.75/1.65  Inferencing          : 0.18
% 3.75/1.65  Reduction            : 0.17
% 3.75/1.65  Demodulation         : 0.13
% 3.75/1.65  BG Simplification    : 0.03
% 3.75/1.65  Subsumption          : 0.12
% 3.75/1.65  Abstraction          : 0.03
% 3.75/1.65  MUC search           : 0.00
% 3.75/1.65  Cooper               : 0.00
% 3.75/1.65  Total                : 0.91
% 3.75/1.65  Index Insertion      : 0.00
% 3.75/1.65  Index Deletion       : 0.00
% 3.75/1.65  Index Matching       : 0.00
% 3.75/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
