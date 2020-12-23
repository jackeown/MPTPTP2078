%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 403 expanded)
%              Number of leaves         :   26 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 (1065 expanded)
%              Number of equality atoms :   49 ( 325 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1304,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,k2_zfmisc_1(k1_relat_1(A_133),k2_relat_1(A_133)))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_236,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_385,plain,(
    ! [A_65,B_66,A_67] :
      ( k1_relset_1(A_65,B_66,A_67) = k1_relat_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_18,c_236])).

tff(c_403,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_22,c_385])).

tff(c_355,plain,(
    ! [B_60,C_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(C_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,C_61) != A_62
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_754,plain,(
    ! [B_107,A_108,A_109] :
      ( k1_xboole_0 = B_107
      | v1_funct_2(A_108,A_109,B_107)
      | k1_relset_1(A_109,B_107,A_108) != A_109
      | ~ r1_tarski(A_108,k2_zfmisc_1(A_109,B_107)) ) ),
    inference(resolution,[status(thm)],[c_18,c_355])).

tff(c_916,plain,(
    ! [A_120] :
      ( k2_relat_1(A_120) = k1_xboole_0
      | v1_funct_2(A_120,k1_relat_1(A_120),k2_relat_1(A_120))
      | k1_relset_1(k1_relat_1(A_120),k2_relat_1(A_120),A_120) != k1_relat_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_22,c_754])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_95,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_923,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_916,c_95])).

tff(c_935,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_923])).

tff(c_940,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_943,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_940])).

tff(c_947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_943])).

tff(c_948,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_137,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35)))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [A_35] :
      ( k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35)) = A_35
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35)),A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_975,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_146])).

tff(c_1014,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12,c_12,c_948,c_975])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_402,plain,(
    ! [A_65,B_66] : k1_relset_1(A_65,B_66,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_385])).

tff(c_406,plain,(
    ! [A_65,B_66] : k1_relset_1(A_65,B_66,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_402])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_199,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_202,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_208,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_464,plain,(
    ! [C_73,B_74] :
      ( v1_funct_2(C_73,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,C_73) != k1_xboole_0
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_466,plain,(
    ! [B_74] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_208,c_464])).

tff(c_472,plain,(
    ! [B_74] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_466])).

tff(c_1049,plain,(
    ! [B_74] : v1_funct_2('#skF_1','#skF_1',B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_1014,c_472])).

tff(c_20,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_relat_1(A_11),k1_relat_1(B_13))
      | ~ r1_tarski(A_11,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_relat_1(A_43),k1_relat_1(B_44))
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_838,plain,(
    ! [B_114,A_115] :
      ( k1_relat_1(B_114) = k1_relat_1(A_115)
      | ~ r1_tarski(k1_relat_1(B_114),k1_relat_1(A_115))
      | ~ r1_tarski(A_115,B_114)
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_861,plain,(
    ! [B_116,A_117] :
      ( k1_relat_1(B_116) = k1_relat_1(A_117)
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_26,c_838])).

tff(c_871,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10))) = k1_relat_1(A_10)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)),A_10)
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_22,c_861])).

tff(c_886,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10))) = k1_relat_1(A_10)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)),A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_871])).

tff(c_957,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_886])).

tff(c_1002,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12,c_30,c_12,c_948,c_957])).

tff(c_1078,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_1002])).

tff(c_950,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_95])).

tff(c_1129,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1014,c_950])).

tff(c_1256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1129])).

tff(c_1257,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1280,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_1257])).

tff(c_1307,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1304,c_1280])).

tff(c_1319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.16/1.52  
% 3.16/1.52  %Foreground sorts:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Background operators:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Foreground operators:
% 3.16/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.52  
% 3.36/1.54  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.36/1.54  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.36/1.54  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.54  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.54  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.36/1.54  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.36/1.54  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.36/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.54  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.36/1.54  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.54  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.36/1.54  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.54  tff(c_1304, plain, (![A_133]: (r1_tarski(A_133, k2_zfmisc_1(k1_relat_1(A_133), k2_relat_1(A_133))) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.54  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.54  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.54  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.54  tff(c_22, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.54  tff(c_236, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.54  tff(c_385, plain, (![A_65, B_66, A_67]: (k1_relset_1(A_65, B_66, A_67)=k1_relat_1(A_67) | ~r1_tarski(A_67, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_18, c_236])).
% 3.36/1.54  tff(c_403, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_22, c_385])).
% 3.36/1.54  tff(c_355, plain, (![B_60, C_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(C_61, A_62, B_60) | k1_relset_1(A_62, B_60, C_61)!=A_62 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.54  tff(c_754, plain, (![B_107, A_108, A_109]: (k1_xboole_0=B_107 | v1_funct_2(A_108, A_109, B_107) | k1_relset_1(A_109, B_107, A_108)!=A_109 | ~r1_tarski(A_108, k2_zfmisc_1(A_109, B_107)))), inference(resolution, [status(thm)], [c_18, c_355])).
% 3.36/1.54  tff(c_916, plain, (![A_120]: (k2_relat_1(A_120)=k1_xboole_0 | v1_funct_2(A_120, k1_relat_1(A_120), k2_relat_1(A_120)) | k1_relset_1(k1_relat_1(A_120), k2_relat_1(A_120), A_120)!=k1_relat_1(A_120) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_22, c_754])).
% 3.36/1.54  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.54  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.54  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 3.36/1.54  tff(c_95, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.36/1.54  tff(c_923, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_916, c_95])).
% 3.36/1.54  tff(c_935, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_923])).
% 3.36/1.54  tff(c_940, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_935])).
% 3.36/1.54  tff(c_943, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_403, c_940])).
% 3.36/1.54  tff(c_947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_943])).
% 3.36/1.54  tff(c_948, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_935])).
% 3.36/1.54  tff(c_137, plain, (![A_35]: (r1_tarski(A_35, k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35))) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.54  tff(c_146, plain, (![A_35]: (k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35))=A_35 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35)), A_35) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_137, c_2])).
% 3.36/1.54  tff(c_975, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_948, c_146])).
% 3.36/1.54  tff(c_1014, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12, c_12, c_948, c_975])).
% 3.36/1.54  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.54  tff(c_402, plain, (![A_65, B_66]: (k1_relset_1(A_65, B_66, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_385])).
% 3.36/1.54  tff(c_406, plain, (![A_65, B_66]: (k1_relset_1(A_65, B_66, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_402])).
% 3.36/1.54  tff(c_34, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.54  tff(c_55, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 3.36/1.54  tff(c_199, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 3.36/1.54  tff(c_202, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_199])).
% 3.36/1.54  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_202])).
% 3.36/1.54  tff(c_208, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 3.36/1.54  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.54  tff(c_38, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.54  tff(c_464, plain, (![C_73, B_74]: (v1_funct_2(C_73, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, C_73)!=k1_xboole_0 | ~m1_subset_1(C_73, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 3.36/1.54  tff(c_466, plain, (![B_74]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_208, c_464])).
% 3.36/1.54  tff(c_472, plain, (![B_74]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_466])).
% 3.36/1.54  tff(c_1049, plain, (![B_74]: (v1_funct_2('#skF_1', '#skF_1', B_74))), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_1014, c_472])).
% 3.36/1.54  tff(c_20, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.54  tff(c_26, plain, (![A_11, B_13]: (r1_tarski(k1_relat_1(A_11), k1_relat_1(B_13)) | ~r1_tarski(A_11, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.54  tff(c_222, plain, (![A_43, B_44]: (r1_tarski(k1_relat_1(A_43), k1_relat_1(B_44)) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.54  tff(c_838, plain, (![B_114, A_115]: (k1_relat_1(B_114)=k1_relat_1(A_115) | ~r1_tarski(k1_relat_1(B_114), k1_relat_1(A_115)) | ~r1_tarski(A_115, B_114) | ~v1_relat_1(B_114) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_222, c_2])).
% 3.36/1.54  tff(c_861, plain, (![B_116, A_117]: (k1_relat_1(B_116)=k1_relat_1(A_117) | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116) | ~v1_relat_1(B_116) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_26, c_838])).
% 3.36/1.54  tff(c_871, plain, (![A_10]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10)))=k1_relat_1(A_10) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10)), A_10) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_22, c_861])).
% 3.36/1.54  tff(c_886, plain, (![A_10]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10)))=k1_relat_1(A_10) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10)), A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_871])).
% 3.36/1.54  tff(c_957, plain, (k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))=k1_relat_1('#skF_1') | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_948, c_886])).
% 3.36/1.54  tff(c_1002, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12, c_30, c_12, c_948, c_957])).
% 3.36/1.54  tff(c_1078, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_1002])).
% 3.36/1.54  tff(c_950, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_948, c_95])).
% 3.36/1.54  tff(c_1129, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_1014, c_950])).
% 3.36/1.54  tff(c_1256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1129])).
% 3.36/1.54  tff(c_1257, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.54  tff(c_1280, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_1257])).
% 3.36/1.54  tff(c_1307, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1304, c_1280])).
% 3.36/1.54  tff(c_1319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1307])).
% 3.36/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  Inference rules
% 3.36/1.54  ----------------------
% 3.36/1.54  #Ref     : 0
% 3.36/1.54  #Sup     : 251
% 3.36/1.54  #Fact    : 0
% 3.36/1.54  #Define  : 0
% 3.36/1.54  #Split   : 3
% 3.36/1.54  #Chain   : 0
% 3.36/1.54  #Close   : 0
% 3.36/1.54  
% 3.36/1.54  Ordering : KBO
% 3.36/1.54  
% 3.36/1.54  Simplification rules
% 3.36/1.54  ----------------------
% 3.36/1.54  #Subsume      : 22
% 3.36/1.54  #Demod        : 463
% 3.36/1.54  #Tautology    : 149
% 3.36/1.54  #SimpNegUnit  : 0
% 3.36/1.54  #BackRed      : 45
% 3.36/1.54  
% 3.36/1.54  #Partial instantiations: 0
% 3.36/1.54  #Strategies tried      : 1
% 3.36/1.54  
% 3.36/1.54  Timing (in seconds)
% 3.36/1.54  ----------------------
% 3.36/1.54  Preprocessing        : 0.31
% 3.36/1.54  Parsing              : 0.16
% 3.36/1.54  CNF conversion       : 0.02
% 3.36/1.54  Main loop            : 0.42
% 3.36/1.54  Inferencing          : 0.15
% 3.36/1.55  Reduction            : 0.13
% 3.36/1.55  Demodulation         : 0.10
% 3.36/1.55  BG Simplification    : 0.02
% 3.36/1.55  Subsumption          : 0.08
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.55  Cooper               : 0.00
% 3.36/1.55  Total                : 0.76
% 3.36/1.55  Index Insertion      : 0.00
% 3.36/1.55  Index Deletion       : 0.00
% 3.36/1.55  Index Matching       : 0.00
% 3.36/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
