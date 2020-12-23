%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 311 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 757 expanded)
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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1414,plain,(
    ! [A_129] :
      ( r1_tarski(A_129,k2_zfmisc_1(k1_relat_1(A_129),k2_relat_1(A_129)))
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_225,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_379,plain,(
    ! [A_64,B_65,A_66] :
      ( k1_relset_1(A_64,B_65,A_66) = k1_relat_1(A_66)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_389,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_379])).

tff(c_340,plain,(
    ! [B_58,C_59,A_60] :
      ( k1_xboole_0 = B_58
      | v1_funct_2(C_59,A_60,B_58)
      | k1_relset_1(A_60,B_58,C_59) != A_60
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1013,plain,(
    ! [B_108,A_109,A_110] :
      ( k1_xboole_0 = B_108
      | v1_funct_2(A_109,A_110,B_108)
      | k1_relset_1(A_110,B_108,A_109) != A_110
      | ~ r1_tarski(A_109,k2_zfmisc_1(A_110,B_108)) ) ),
    inference(resolution,[status(thm)],[c_12,c_340])).

tff(c_1056,plain,(
    ! [A_116] :
      ( k2_relat_1(A_116) = k1_xboole_0
      | v1_funct_2(A_116,k1_relat_1(A_116),k2_relat_1(A_116))
      | k1_relset_1(k1_relat_1(A_116),k2_relat_1(A_116),A_116) != k1_relat_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_18,c_1013])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_92,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1059,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1056,c_92])).

tff(c_1080,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1059])).

tff(c_1085,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_1088,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_1085])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1088])).

tff(c_1093,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_1140,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_18])).

tff(c_1172,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_1140])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1211,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1172,c_2])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34)))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_117])).

tff(c_129,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6,c_26,c_123])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_203,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_206,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_206])).

tff(c_212,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_237,plain,(
    ! [B_45,C_46] :
      ( k1_relset_1(k1_xboole_0,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_225])).

tff(c_239,plain,(
    ! [B_45] : k1_relset_1(k1_xboole_0,B_45,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_212,c_237])).

tff(c_244,plain,(
    ! [B_45] : k1_relset_1(k1_xboole_0,B_45,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_36,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_416,plain,(
    ! [C_70,B_71] :
      ( v1_funct_2(C_70,k1_xboole_0,B_71)
      | k1_relset_1(k1_xboole_0,B_71,C_70) != k1_xboole_0
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_418,plain,(
    ! [B_71] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_71)
      | k1_relset_1(k1_xboole_0,B_71,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_212,c_416])).

tff(c_424,plain,(
    ! [B_71] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_418])).

tff(c_1236,plain,(
    ! [B_71] : v1_funct_2('#skF_1','#skF_1',B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_1211,c_424])).

tff(c_143,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_relat_1(A_35),k1_relat_1(B_36))
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [A_35] :
      ( r1_tarski(k1_relat_1(A_35),k1_xboole_0)
      | ~ r1_tarski(A_35,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_170,plain,(
    ! [A_38] :
      ( r1_tarski(k1_relat_1(A_38),k1_xboole_0)
      | ~ r1_tarski(A_38,k1_xboole_0)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_152])).

tff(c_183,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) = k1_xboole_0
      | ~ r1_tarski(A_38,k1_xboole_0)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_1187,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1172,c_183])).

tff(c_1207,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1187])).

tff(c_1275,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_1207])).

tff(c_1095,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_92])).

tff(c_1213,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_1095])).

tff(c_1354,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_1213])).

tff(c_1383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_1354])).

tff(c_1384,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1396,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1384])).

tff(c_1420,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1414,c_1396])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.16/1.53  
% 3.16/1.53  %Foreground sorts:
% 3.16/1.53  
% 3.16/1.53  
% 3.16/1.53  %Background operators:
% 3.16/1.53  
% 3.16/1.53  
% 3.16/1.53  %Foreground operators:
% 3.16/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.53  
% 3.49/1.54  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.49/1.54  tff(f_52, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.49/1.54  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.49/1.54  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.49/1.54  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.49/1.54  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.49/1.54  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.49/1.54  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.49/1.54  tff(f_67, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.49/1.54  tff(f_48, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.49/1.54  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.49/1.54  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.49/1.54  tff(c_1414, plain, (![A_129]: (r1_tarski(A_129, k2_zfmisc_1(k1_relat_1(A_129), k2_relat_1(A_129))) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.54  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.54  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.54  tff(c_18, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.54  tff(c_225, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.49/1.54  tff(c_379, plain, (![A_64, B_65, A_66]: (k1_relset_1(A_64, B_65, A_66)=k1_relat_1(A_66) | ~r1_tarski(A_66, k2_zfmisc_1(A_64, B_65)))), inference(resolution, [status(thm)], [c_12, c_225])).
% 3.49/1.54  tff(c_389, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_18, c_379])).
% 3.49/1.54  tff(c_340, plain, (![B_58, C_59, A_60]: (k1_xboole_0=B_58 | v1_funct_2(C_59, A_60, B_58) | k1_relset_1(A_60, B_58, C_59)!=A_60 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_58))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.49/1.54  tff(c_1013, plain, (![B_108, A_109, A_110]: (k1_xboole_0=B_108 | v1_funct_2(A_109, A_110, B_108) | k1_relset_1(A_110, B_108, A_109)!=A_110 | ~r1_tarski(A_109, k2_zfmisc_1(A_110, B_108)))), inference(resolution, [status(thm)], [c_12, c_340])).
% 3.49/1.54  tff(c_1056, plain, (![A_116]: (k2_relat_1(A_116)=k1_xboole_0 | v1_funct_2(A_116, k1_relat_1(A_116), k2_relat_1(A_116)) | k1_relset_1(k1_relat_1(A_116), k2_relat_1(A_116), A_116)!=k1_relat_1(A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_18, c_1013])).
% 3.49/1.54  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.49/1.54  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.49/1.54  tff(c_50, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 3.49/1.54  tff(c_92, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.49/1.54  tff(c_1059, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1056, c_92])).
% 3.49/1.54  tff(c_1080, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1059])).
% 3.49/1.54  tff(c_1085, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1080])).
% 3.49/1.54  tff(c_1088, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_389, c_1085])).
% 3.49/1.54  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1088])).
% 3.49/1.54  tff(c_1093, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1080])).
% 3.49/1.54  tff(c_1140, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_18])).
% 3.49/1.54  tff(c_1172, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_1140])).
% 3.49/1.54  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.54  tff(c_1211, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1172, c_2])).
% 3.49/1.54  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.54  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.49/1.54  tff(c_16, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.49/1.54  tff(c_58, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_16])).
% 3.49/1.54  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.54  tff(c_117, plain, (![A_34]: (r1_tarski(A_34, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34))) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.54  tff(c_123, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_117])).
% 3.49/1.54  tff(c_129, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6, c_26, c_123])).
% 3.49/1.54  tff(c_32, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.49/1.54  tff(c_53, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32])).
% 3.49/1.54  tff(c_203, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_53])).
% 3.49/1.54  tff(c_206, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_203])).
% 3.49/1.54  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_206])).
% 3.49/1.54  tff(c_212, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_53])).
% 3.49/1.54  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.54  tff(c_237, plain, (![B_45, C_46]: (k1_relset_1(k1_xboole_0, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_225])).
% 3.49/1.54  tff(c_239, plain, (![B_45]: (k1_relset_1(k1_xboole_0, B_45, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_212, c_237])).
% 3.49/1.54  tff(c_244, plain, (![B_45]: (k1_relset_1(k1_xboole_0, B_45, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_239])).
% 3.49/1.54  tff(c_36, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.49/1.54  tff(c_416, plain, (![C_70, B_71]: (v1_funct_2(C_70, k1_xboole_0, B_71) | k1_relset_1(k1_xboole_0, B_71, C_70)!=k1_xboole_0 | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 3.49/1.54  tff(c_418, plain, (![B_71]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_71) | k1_relset_1(k1_xboole_0, B_71, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_212, c_416])).
% 3.49/1.54  tff(c_424, plain, (![B_71]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_418])).
% 3.49/1.54  tff(c_1236, plain, (![B_71]: (v1_funct_2('#skF_1', '#skF_1', B_71))), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_1211, c_424])).
% 3.49/1.54  tff(c_143, plain, (![A_35, B_36]: (r1_tarski(k1_relat_1(A_35), k1_relat_1(B_36)) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.49/1.54  tff(c_152, plain, (![A_35]: (r1_tarski(k1_relat_1(A_35), k1_xboole_0) | ~r1_tarski(A_35, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_26, c_143])).
% 3.49/1.54  tff(c_170, plain, (![A_38]: (r1_tarski(k1_relat_1(A_38), k1_xboole_0) | ~r1_tarski(A_38, k1_xboole_0) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_152])).
% 3.49/1.54  tff(c_183, plain, (![A_38]: (k1_relat_1(A_38)=k1_xboole_0 | ~r1_tarski(A_38, k1_xboole_0) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_170, c_2])).
% 3.49/1.54  tff(c_1187, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1172, c_183])).
% 3.49/1.54  tff(c_1207, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1187])).
% 3.49/1.54  tff(c_1275, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_1207])).
% 3.49/1.54  tff(c_1095, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_92])).
% 3.49/1.54  tff(c_1213, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_1095])).
% 3.49/1.54  tff(c_1354, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1275, c_1213])).
% 3.49/1.54  tff(c_1383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1236, c_1354])).
% 3.49/1.54  tff(c_1384, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 3.49/1.54  tff(c_1396, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1384])).
% 3.49/1.54  tff(c_1420, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1414, c_1396])).
% 3.49/1.54  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1420])).
% 3.49/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  Inference rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Ref     : 0
% 3.49/1.54  #Sup     : 298
% 3.49/1.54  #Fact    : 0
% 3.49/1.54  #Define  : 0
% 3.49/1.54  #Split   : 3
% 3.49/1.54  #Chain   : 0
% 3.49/1.54  #Close   : 0
% 3.49/1.54  
% 3.49/1.54  Ordering : KBO
% 3.49/1.54  
% 3.49/1.54  Simplification rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Subsume      : 29
% 3.49/1.54  #Demod        : 452
% 3.49/1.54  #Tautology    : 173
% 3.49/1.54  #SimpNegUnit  : 0
% 3.49/1.54  #BackRed      : 57
% 3.49/1.54  
% 3.49/1.54  #Partial instantiations: 0
% 3.49/1.54  #Strategies tried      : 1
% 3.49/1.54  
% 3.49/1.54  Timing (in seconds)
% 3.49/1.54  ----------------------
% 3.49/1.55  Preprocessing        : 0.31
% 3.49/1.55  Parsing              : 0.17
% 3.49/1.55  CNF conversion       : 0.02
% 3.49/1.55  Main loop            : 0.46
% 3.49/1.55  Inferencing          : 0.15
% 3.49/1.55  Reduction            : 0.15
% 3.49/1.55  Demodulation         : 0.11
% 3.49/1.55  BG Simplification    : 0.02
% 3.49/1.55  Subsumption          : 0.10
% 3.49/1.55  Abstraction          : 0.02
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.80
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
