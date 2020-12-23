%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 9.53s
% Output     : CNFRefutation 9.87s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 244 expanded)
%              Number of leaves         :   45 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  208 ( 729 expanded)
%              Number of equality atoms :   42 (  65 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_80,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_172,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_xboole_0(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_188,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_190,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_1518,plain,(
    ! [C_185,D_187,B_186,E_183,A_184,F_182] :
      ( k4_relset_1(A_184,B_186,C_185,D_187,E_183,F_182) = k5_relat_1(E_183,F_182)
      | ~ m1_subset_1(F_182,k1_zfmisc_1(k2_zfmisc_1(C_185,D_187)))
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1765,plain,(
    ! [A_205,B_206,E_207] :
      ( k4_relset_1(A_205,B_206,'#skF_3','#skF_2',E_207,'#skF_5') = k5_relat_1(E_207,'#skF_5')
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(resolution,[status(thm)],[c_54,c_1518])).

tff(c_1797,plain,(
    k4_relset_1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1765])).

tff(c_24,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k4_relset_1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1955,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_24])).

tff(c_1959,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_1955])).

tff(c_1843,plain,(
    ! [A_209,C_210,F_212,D_211,E_208,B_213] :
      ( k1_partfun1(A_209,B_213,C_210,D_211,E_208,F_212) = k5_relat_1(E_208,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_210,D_211)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_213)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1862,plain,(
    ! [A_209,B_213,E_208] :
      ( k1_partfun1(A_209,B_213,'#skF_3','#skF_2',E_208,'#skF_5') = k5_relat_1(E_208,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_213)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_54,c_1843])).

tff(c_3817,plain,(
    ! [A_287,B_288,E_289] :
      ( k1_partfun1(A_287,B_288,'#skF_3','#skF_2',E_289,'#skF_5') = k5_relat_1(E_289,'#skF_5')
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(E_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1862])).

tff(c_3857,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3817])).

tff(c_3872,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3857])).

tff(c_34,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_65,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1421,plain,(
    ! [D_169,C_170,A_171,B_172] :
      ( D_169 = C_170
      | ~ r2_relset_1(A_171,B_172,C_170,D_169)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1429,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_1421])).

tff(c_1444,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1429])).

tff(c_1470,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_9470,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3872,c_1470])).

tff(c_9474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1959,c_9470])).

tff(c_9475,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_10323,plain,(
    ! [D_528,E_525,A_527,C_526,B_529] :
      ( k1_xboole_0 = C_526
      | v2_funct_1(D_528)
      | ~ v2_funct_1(k1_partfun1(A_527,B_529,B_529,C_526,D_528,E_525))
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(B_529,C_526)))
      | ~ v1_funct_2(E_525,B_529,C_526)
      | ~ v1_funct_1(E_525)
      | ~ m1_subset_1(D_528,k1_zfmisc_1(k2_zfmisc_1(A_527,B_529)))
      | ~ v1_funct_2(D_528,A_527,B_529)
      | ~ v1_funct_1(D_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10325,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9475,c_10323])).

tff(c_10327,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_66,c_10325])).

tff(c_10328,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10327])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10352,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10328,c_2])).

tff(c_10354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_10352])).

tff(c_10355,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_10447,plain,(
    ! [A_533] :
      ( v1_xboole_0(k6_partfun1(A_533))
      | ~ v1_xboole_0(A_533) ) ),
    inference(resolution,[status(thm)],[c_65,c_172])).

tff(c_81,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | B_64 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_10362,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10355,c_84])).

tff(c_10356,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_10369,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10356,c_84])).

tff(c_10379,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10362,c_10369])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10370,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_10356,c_4])).

tff(c_10414,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10379,c_10370])).

tff(c_10466,plain,(
    ! [A_537] :
      ( k6_partfun1(A_537) = '#skF_4'
      | ~ v1_xboole_0(A_537) ) ),
    inference(resolution,[status(thm)],[c_10447,c_10414])).

tff(c_10474,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10355,c_10466])).

tff(c_10491,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10474,c_66])).

tff(c_10499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10491])).

tff(c_10500,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10514,plain,(
    ! [C_543,A_544,B_545] :
      ( v1_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10532,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10514])).

tff(c_10571,plain,(
    ! [C_552,B_553,A_554] :
      ( v5_relat_1(C_552,B_553)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_554,B_553))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10588,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_10571])).

tff(c_10788,plain,(
    ! [A_573,B_574,C_575] :
      ( k2_relset_1(A_573,B_574,C_575) = k2_relat_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10809,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10788])).

tff(c_11749,plain,(
    ! [A_632,B_633,C_634,D_635] :
      ( k2_relset_1(A_632,B_633,C_634) = B_633
      | ~ r2_relset_1(B_633,B_633,k1_partfun1(B_633,A_632,A_632,B_633,D_635,C_634),k6_partfun1(B_633))
      | ~ m1_subset_1(D_635,k1_zfmisc_1(k2_zfmisc_1(B_633,A_632)))
      | ~ v1_funct_2(D_635,B_633,A_632)
      | ~ v1_funct_1(D_635)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(A_632,B_633)))
      | ~ v1_funct_2(C_634,A_632,B_633)
      | ~ v1_funct_1(C_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_11764,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_11749])).

tff(c_11767,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_10809,c_11764])).

tff(c_36,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11772,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11767,c_36])).

tff(c_11776,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10532,c_10588,c_11767,c_11772])).

tff(c_11778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10500,c_11776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.53/3.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.55  
% 9.87/3.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.55  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.87/3.55  
% 9.87/3.55  %Foreground sorts:
% 9.87/3.55  
% 9.87/3.55  
% 9.87/3.55  %Background operators:
% 9.87/3.55  
% 9.87/3.55  
% 9.87/3.55  %Foreground operators:
% 9.87/3.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.87/3.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.87/3.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.87/3.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.87/3.55  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.87/3.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.87/3.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.87/3.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.87/3.55  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.87/3.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.87/3.55  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.87/3.55  tff('#skF_5', type, '#skF_5': $i).
% 9.87/3.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.87/3.55  tff('#skF_2', type, '#skF_2': $i).
% 9.87/3.55  tff('#skF_3', type, '#skF_3': $i).
% 9.87/3.55  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.87/3.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.87/3.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.87/3.55  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.87/3.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.87/3.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.87/3.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.87/3.55  tff('#skF_4', type, '#skF_4': $i).
% 9.87/3.55  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.87/3.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.87/3.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.87/3.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.87/3.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.87/3.55  
% 9.87/3.57  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.87/3.57  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.87/3.57  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.87/3.57  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.87/3.57  tff(f_87, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 9.87/3.57  tff(f_77, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 9.87/3.57  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.87/3.57  tff(f_97, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.87/3.57  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.87/3.57  tff(f_156, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.87/3.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.87/3.57  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.87/3.57  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.87/3.57  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.87/3.57  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.87/3.57  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.87/3.57  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.87/3.57  tff(c_50, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_80, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 9.87/3.57  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_172, plain, (![C_86, A_87, B_88]: (v1_xboole_0(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.87/3.57  tff(c_188, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_172])).
% 9.87/3.57  tff(c_190, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_188])).
% 9.87/3.57  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_42, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.87/3.57  tff(c_14, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.87/3.57  tff(c_66, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 9.87/3.57  tff(c_1518, plain, (![C_185, D_187, B_186, E_183, A_184, F_182]: (k4_relset_1(A_184, B_186, C_185, D_187, E_183, F_182)=k5_relat_1(E_183, F_182) | ~m1_subset_1(F_182, k1_zfmisc_1(k2_zfmisc_1(C_185, D_187))) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_184, B_186))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.87/3.57  tff(c_1765, plain, (![A_205, B_206, E_207]: (k4_relset_1(A_205, B_206, '#skF_3', '#skF_2', E_207, '#skF_5')=k5_relat_1(E_207, '#skF_5') | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(resolution, [status(thm)], [c_54, c_1518])).
% 9.87/3.57  tff(c_1797, plain, (k4_relset_1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_1765])).
% 9.87/3.57  tff(c_24, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (m1_subset_1(k4_relset_1(A_19, B_20, C_21, D_22, E_23, F_24), k1_zfmisc_1(k2_zfmisc_1(A_19, D_22))) | ~m1_subset_1(F_24, k1_zfmisc_1(k2_zfmisc_1(C_21, D_22))) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.87/3.57  tff(c_1955, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1797, c_24])).
% 9.87/3.57  tff(c_1959, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_1955])).
% 9.87/3.57  tff(c_1843, plain, (![A_209, C_210, F_212, D_211, E_208, B_213]: (k1_partfun1(A_209, B_213, C_210, D_211, E_208, F_212)=k5_relat_1(E_208, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_210, D_211))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_213))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.87/3.57  tff(c_1862, plain, (![A_209, B_213, E_208]: (k1_partfun1(A_209, B_213, '#skF_3', '#skF_2', E_208, '#skF_5')=k5_relat_1(E_208, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_213))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_54, c_1843])).
% 9.87/3.57  tff(c_3817, plain, (![A_287, B_288, E_289]: (k1_partfun1(A_287, B_288, '#skF_3', '#skF_2', E_289, '#skF_5')=k5_relat_1(E_289, '#skF_5') | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(E_289))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1862])).
% 9.87/3.57  tff(c_3857, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3817])).
% 9.87/3.57  tff(c_3872, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3857])).
% 9.87/3.57  tff(c_34, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.87/3.57  tff(c_65, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 9.87/3.57  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.87/3.57  tff(c_1421, plain, (![D_169, C_170, A_171, B_172]: (D_169=C_170 | ~r2_relset_1(A_171, B_172, C_170, D_169) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.87/3.57  tff(c_1429, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_1421])).
% 9.87/3.57  tff(c_1444, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1429])).
% 9.87/3.57  tff(c_1470, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1444])).
% 9.87/3.57  tff(c_9470, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3872, c_1470])).
% 9.87/3.57  tff(c_9474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1959, c_9470])).
% 9.87/3.57  tff(c_9475, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1444])).
% 9.87/3.57  tff(c_10323, plain, (![D_528, E_525, A_527, C_526, B_529]: (k1_xboole_0=C_526 | v2_funct_1(D_528) | ~v2_funct_1(k1_partfun1(A_527, B_529, B_529, C_526, D_528, E_525)) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(B_529, C_526))) | ~v1_funct_2(E_525, B_529, C_526) | ~v1_funct_1(E_525) | ~m1_subset_1(D_528, k1_zfmisc_1(k2_zfmisc_1(A_527, B_529))) | ~v1_funct_2(D_528, A_527, B_529) | ~v1_funct_1(D_528))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.87/3.57  tff(c_10325, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9475, c_10323])).
% 9.87/3.57  tff(c_10327, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_66, c_10325])).
% 9.87/3.57  tff(c_10328, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_80, c_10327])).
% 9.87/3.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.87/3.57  tff(c_10352, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10328, c_2])).
% 9.87/3.57  tff(c_10354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_10352])).
% 9.87/3.57  tff(c_10355, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_188])).
% 9.87/3.57  tff(c_10447, plain, (![A_533]: (v1_xboole_0(k6_partfun1(A_533)) | ~v1_xboole_0(A_533))), inference(resolution, [status(thm)], [c_65, c_172])).
% 9.87/3.57  tff(c_81, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | B_64=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.87/3.57  tff(c_84, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_2, c_81])).
% 9.87/3.57  tff(c_10362, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10355, c_84])).
% 9.87/3.57  tff(c_10356, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_188])).
% 9.87/3.57  tff(c_10369, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10356, c_84])).
% 9.87/3.57  tff(c_10379, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10362, c_10369])).
% 9.87/3.57  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.87/3.57  tff(c_10370, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_10356, c_4])).
% 9.87/3.57  tff(c_10414, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10379, c_10370])).
% 9.87/3.57  tff(c_10466, plain, (![A_537]: (k6_partfun1(A_537)='#skF_4' | ~v1_xboole_0(A_537))), inference(resolution, [status(thm)], [c_10447, c_10414])).
% 9.87/3.57  tff(c_10474, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10355, c_10466])).
% 9.87/3.57  tff(c_10491, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10474, c_66])).
% 9.87/3.57  tff(c_10499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_10491])).
% 9.87/3.57  tff(c_10500, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 9.87/3.57  tff(c_10514, plain, (![C_543, A_544, B_545]: (v1_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.87/3.57  tff(c_10532, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10514])).
% 9.87/3.57  tff(c_10571, plain, (![C_552, B_553, A_554]: (v5_relat_1(C_552, B_553) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_554, B_553))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.87/3.57  tff(c_10588, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_10571])).
% 9.87/3.57  tff(c_10788, plain, (![A_573, B_574, C_575]: (k2_relset_1(A_573, B_574, C_575)=k2_relat_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.87/3.57  tff(c_10809, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10788])).
% 9.87/3.57  tff(c_11749, plain, (![A_632, B_633, C_634, D_635]: (k2_relset_1(A_632, B_633, C_634)=B_633 | ~r2_relset_1(B_633, B_633, k1_partfun1(B_633, A_632, A_632, B_633, D_635, C_634), k6_partfun1(B_633)) | ~m1_subset_1(D_635, k1_zfmisc_1(k2_zfmisc_1(B_633, A_632))) | ~v1_funct_2(D_635, B_633, A_632) | ~v1_funct_1(D_635) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))) | ~v1_funct_2(C_634, A_632, B_633) | ~v1_funct_1(C_634))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.87/3.57  tff(c_11764, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_11749])).
% 9.87/3.57  tff(c_11767, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_10809, c_11764])).
% 9.87/3.57  tff(c_36, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.87/3.57  tff(c_11772, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11767, c_36])).
% 9.87/3.57  tff(c_11776, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10532, c_10588, c_11767, c_11772])).
% 9.87/3.57  tff(c_11778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10500, c_11776])).
% 9.87/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.57  
% 9.87/3.57  Inference rules
% 9.87/3.57  ----------------------
% 9.87/3.57  #Ref     : 0
% 9.87/3.57  #Sup     : 3086
% 9.87/3.57  #Fact    : 0
% 9.87/3.57  #Define  : 0
% 9.87/3.57  #Split   : 33
% 9.87/3.57  #Chain   : 0
% 9.87/3.57  #Close   : 0
% 9.87/3.57  
% 9.87/3.57  Ordering : KBO
% 9.87/3.57  
% 9.87/3.57  Simplification rules
% 9.87/3.57  ----------------------
% 9.87/3.57  #Subsume      : 237
% 9.87/3.57  #Demod        : 1964
% 9.87/3.57  #Tautology    : 1025
% 9.87/3.57  #SimpNegUnit  : 5
% 9.87/3.57  #BackRed      : 65
% 9.87/3.57  
% 9.87/3.57  #Partial instantiations: 0
% 9.87/3.57  #Strategies tried      : 1
% 9.87/3.57  
% 9.87/3.57  Timing (in seconds)
% 9.87/3.57  ----------------------
% 9.87/3.58  Preprocessing        : 0.36
% 9.87/3.58  Parsing              : 0.19
% 9.87/3.58  CNF conversion       : 0.02
% 9.87/3.58  Main loop            : 2.44
% 9.87/3.58  Inferencing          : 0.64
% 9.87/3.58  Reduction            : 0.94
% 9.87/3.58  Demodulation         : 0.71
% 9.87/3.58  BG Simplification    : 0.08
% 9.87/3.58  Subsumption          : 0.59
% 9.87/3.58  Abstraction          : 0.10
% 9.87/3.58  MUC search           : 0.00
% 9.87/3.58  Cooper               : 0.00
% 9.87/3.58  Total                : 2.85
% 9.87/3.58  Index Insertion      : 0.00
% 9.87/3.58  Index Deletion       : 0.00
% 9.87/3.58  Index Matching       : 0.00
% 9.87/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
