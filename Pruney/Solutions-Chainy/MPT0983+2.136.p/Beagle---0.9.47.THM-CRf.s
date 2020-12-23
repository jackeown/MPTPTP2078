%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:21 EST 2020

% Result     : Theorem 9.15s
% Output     : CNFRefutation 9.47s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 435 expanded)
%              Number of leaves         :   52 ( 177 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (1415 expanded)
%              Number of equality atoms :   52 ( 153 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
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

tff(f_149,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_103,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_188,axiom,(
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

tff(f_75,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_166,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_76,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_161,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_92,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48])).

tff(c_716,plain,(
    ! [C_154,E_155,F_150,B_153,D_152,A_151] :
      ( k4_relset_1(A_151,B_153,C_154,D_152,E_155,F_150) = k5_relat_1(E_155,F_150)
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(C_154,D_152)))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_151,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_971,plain,(
    ! [A_171,B_172,E_173] :
      ( k4_relset_1(A_171,B_172,'#skF_2','#skF_1',E_173,'#skF_4') = k5_relat_1(E_173,'#skF_4')
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(resolution,[status(thm)],[c_80,c_716])).

tff(c_1004,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_971])).

tff(c_50,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k4_relset_1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1219,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_50])).

tff(c_1223,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_1219])).

tff(c_931,plain,(
    ! [E_166,C_165,D_170,B_167,F_168,A_169] :
      ( k1_partfun1(A_169,B_167,C_165,D_170,E_166,F_168) = k5_relat_1(E_166,F_168)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_165,D_170)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_169,B_167)))
      | ~ v1_funct_1(E_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_943,plain,(
    ! [A_169,B_167,E_166] :
      ( k1_partfun1(A_169,B_167,'#skF_2','#skF_1',E_166,'#skF_4') = k5_relat_1(E_166,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_169,B_167)))
      | ~ v1_funct_1(E_166) ) ),
    inference(resolution,[status(thm)],[c_80,c_931])).

tff(c_1721,plain,(
    ! [A_213,B_214,E_215] :
      ( k1_partfun1(A_213,B_214,'#skF_2','#skF_1',E_215,'#skF_4') = k5_relat_1(E_215,'#skF_4')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(E_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_943])).

tff(c_1742,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_1721])).

tff(c_1764,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1742])).

tff(c_60,plain,(
    ! [A_46] : m1_subset_1(k6_relat_1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_91,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_656,plain,(
    ! [D_138,C_139,A_140,B_141] :
      ( D_138 = C_139
      | ~ r2_relset_1(A_140,B_141,C_139,D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_666,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_656])).

tff(c_685,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_666])).

tff(c_710,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_2299,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_710])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_2299])).

tff(c_2304,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_3019,plain,(
    ! [C_296,A_299,B_298,D_297,E_295] :
      ( k1_xboole_0 = C_296
      | v2_funct_1(D_297)
      | ~ v2_funct_1(k1_partfun1(A_299,B_298,B_298,C_296,D_297,E_295))
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(B_298,C_296)))
      | ~ v1_funct_2(E_295,B_298,C_296)
      | ~ v1_funct_1(E_295)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(k2_zfmisc_1(A_299,B_298)))
      | ~ v1_funct_2(D_297,A_299,B_298)
      | ~ v1_funct_1(D_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3021,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2304,c_3019])).

tff(c_3026,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_92,c_3021])).

tff(c_3027,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_3026])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3064,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_2])).

tff(c_34,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3056,plain,(
    ! [A_19] : k9_relat_1('#skF_1',A_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_3027,c_34])).

tff(c_113,plain,(
    ! [A_73] : k6_relat_1(A_73) = k6_partfun1(A_73) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_119,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_36])).

tff(c_3060,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_3027,c_119])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3057,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_3027,c_14])).

tff(c_46,plain,(
    ! [A_24,B_25] :
      ( k9_relat_1(k6_relat_1(A_24),B_25) = B_25
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_358,plain,(
    ! [A_99,B_100] :
      ( k9_relat_1(k6_partfun1(A_99),B_100) = B_100
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_372,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_1','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_86,c_358])).

tff(c_3180,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_372])).

tff(c_3182,plain,(
    k9_relat_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3060,c_3180])).

tff(c_3388,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3056,c_3182])).

tff(c_240,plain,(
    ! [A_87] :
      ( v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_243,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_161])).

tff(c_246,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_243])).

tff(c_247,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_3415,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3388,c_247])).

tff(c_3424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_3415])).

tff(c_3425,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_30,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3434,plain,(
    ! [B_317,A_318] :
      ( v1_relat_1(B_317)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(A_318))
      | ~ v1_relat_1(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3440,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_3434])).

tff(c_3452,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3440])).

tff(c_3454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3425,c_3452])).

tff(c_3455,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3498,plain,(
    ! [B_323,A_324] :
      ( v1_relat_1(B_323)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_324))
      | ~ v1_relat_1(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3504,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_3498])).

tff(c_3516,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3504])).

tff(c_3871,plain,(
    ! [A_367,B_368,C_369] :
      ( k2_relset_1(A_367,B_368,C_369) = k2_relat_1(C_369)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3892,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_3871])).

tff(c_4722,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( k2_relset_1(A_439,B_440,C_441) = B_440
      | ~ r2_relset_1(B_440,B_440,k1_partfun1(B_440,A_439,A_439,B_440,D_442,C_441),k6_partfun1(B_440))
      | ~ m1_subset_1(D_442,k1_zfmisc_1(k2_zfmisc_1(B_440,A_439)))
      | ~ v1_funct_2(D_442,B_440,A_439)
      | ~ v1_funct_1(D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ v1_funct_2(C_441,A_439,B_440)
      | ~ v1_funct_1(C_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4725,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_4722])).

tff(c_4731,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_90,c_88,c_86,c_3892,c_4725])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3631,plain,(
    ! [B_336,A_337] :
      ( v5_relat_1(B_336,A_337)
      | ~ r1_tarski(k2_relat_1(B_336),A_337)
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3636,plain,(
    ! [B_336] :
      ( v5_relat_1(B_336,k2_relat_1(B_336))
      | ~ v1_relat_1(B_336) ) ),
    inference(resolution,[status(thm)],[c_8,c_3631])).

tff(c_3704,plain,(
    ! [B_345] :
      ( v2_funct_2(B_345,k2_relat_1(B_345))
      | ~ v5_relat_1(B_345,k2_relat_1(B_345))
      | ~ v1_relat_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3708,plain,(
    ! [B_336] :
      ( v2_funct_2(B_336,k2_relat_1(B_336))
      | ~ v1_relat_1(B_336) ) ),
    inference(resolution,[status(thm)],[c_3636,c_3704])).

tff(c_4742,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4731,c_3708])).

tff(c_4759,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_4742])).

tff(c_4761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3455,c_4759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.15/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.30  
% 9.15/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.30  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.15/3.30  
% 9.15/3.30  %Foreground sorts:
% 9.15/3.30  
% 9.15/3.30  
% 9.15/3.30  %Background operators:
% 9.15/3.30  
% 9.15/3.30  
% 9.15/3.30  %Foreground operators:
% 9.15/3.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.15/3.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.15/3.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.15/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.15/3.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.15/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.15/3.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.15/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.15/3.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.15/3.30  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.15/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.15/3.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.15/3.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.15/3.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.15/3.30  tff('#skF_2', type, '#skF_2': $i).
% 9.15/3.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.15/3.30  tff('#skF_3', type, '#skF_3': $i).
% 9.15/3.30  tff('#skF_1', type, '#skF_1': $i).
% 9.15/3.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.15/3.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.15/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.15/3.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.15/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.15/3.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.15/3.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.15/3.30  tff('#skF_4', type, '#skF_4': $i).
% 9.15/3.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.15/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.15/3.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.15/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.15/3.30  
% 9.47/3.34  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.47/3.34  tff(f_149, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.47/3.34  tff(f_103, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 9.47/3.34  tff(f_119, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 9.47/3.34  tff(f_109, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 9.47/3.34  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.47/3.34  tff(f_129, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.47/3.34  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.47/3.34  tff(f_188, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.47/3.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.47/3.34  tff(f_75, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 9.47/3.34  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 9.47/3.34  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.47/3.34  tff(f_101, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 9.47/3.34  tff(f_88, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 9.47/3.34  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.47/3.34  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.47/3.34  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.47/3.34  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.47/3.34  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.47/3.34  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.47/3.34  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.47/3.34  tff(c_76, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_161, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 9.47/3.34  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_68, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.47/3.34  tff(c_48, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.47/3.34  tff(c_92, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48])).
% 9.47/3.34  tff(c_716, plain, (![C_154, E_155, F_150, B_153, D_152, A_151]: (k4_relset_1(A_151, B_153, C_154, D_152, E_155, F_150)=k5_relat_1(E_155, F_150) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(C_154, D_152))) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_151, B_153))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.47/3.34  tff(c_971, plain, (![A_171, B_172, E_173]: (k4_relset_1(A_171, B_172, '#skF_2', '#skF_1', E_173, '#skF_4')=k5_relat_1(E_173, '#skF_4') | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(resolution, [status(thm)], [c_80, c_716])).
% 9.47/3.34  tff(c_1004, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_971])).
% 9.47/3.34  tff(c_50, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k4_relset_1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.47/3.34  tff(c_1219, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1004, c_50])).
% 9.47/3.34  tff(c_1223, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_80, c_1219])).
% 9.47/3.34  tff(c_931, plain, (![E_166, C_165, D_170, B_167, F_168, A_169]: (k1_partfun1(A_169, B_167, C_165, D_170, E_166, F_168)=k5_relat_1(E_166, F_168) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_165, D_170))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_169, B_167))) | ~v1_funct_1(E_166))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.47/3.34  tff(c_943, plain, (![A_169, B_167, E_166]: (k1_partfun1(A_169, B_167, '#skF_2', '#skF_1', E_166, '#skF_4')=k5_relat_1(E_166, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_169, B_167))) | ~v1_funct_1(E_166))), inference(resolution, [status(thm)], [c_80, c_931])).
% 9.47/3.34  tff(c_1721, plain, (![A_213, B_214, E_215]: (k1_partfun1(A_213, B_214, '#skF_2', '#skF_1', E_215, '#skF_4')=k5_relat_1(E_215, '#skF_4') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(E_215))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_943])).
% 9.47/3.34  tff(c_1742, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_1721])).
% 9.47/3.34  tff(c_1764, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1742])).
% 9.47/3.34  tff(c_60, plain, (![A_46]: (m1_subset_1(k6_relat_1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.47/3.34  tff(c_91, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_60])).
% 9.47/3.34  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.47/3.34  tff(c_656, plain, (![D_138, C_139, A_140, B_141]: (D_138=C_139 | ~r2_relset_1(A_140, B_141, C_139, D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.47/3.34  tff(c_666, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_656])).
% 9.47/3.34  tff(c_685, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_666])).
% 9.47/3.34  tff(c_710, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_685])).
% 9.47/3.34  tff(c_2299, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_710])).
% 9.47/3.34  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1223, c_2299])).
% 9.47/3.34  tff(c_2304, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_685])).
% 9.47/3.34  tff(c_3019, plain, (![C_296, A_299, B_298, D_297, E_295]: (k1_xboole_0=C_296 | v2_funct_1(D_297) | ~v2_funct_1(k1_partfun1(A_299, B_298, B_298, C_296, D_297, E_295)) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(B_298, C_296))) | ~v1_funct_2(E_295, B_298, C_296) | ~v1_funct_1(E_295) | ~m1_subset_1(D_297, k1_zfmisc_1(k2_zfmisc_1(A_299, B_298))) | ~v1_funct_2(D_297, A_299, B_298) | ~v1_funct_1(D_297))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.47/3.34  tff(c_3021, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2304, c_3019])).
% 9.47/3.34  tff(c_3026, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_92, c_3021])).
% 9.47/3.34  tff(c_3027, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_161, c_3026])).
% 9.47/3.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.47/3.34  tff(c_3064, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_2])).
% 9.47/3.34  tff(c_34, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.47/3.34  tff(c_3056, plain, (![A_19]: (k9_relat_1('#skF_1', A_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_3027, c_34])).
% 9.47/3.34  tff(c_113, plain, (![A_73]: (k6_relat_1(A_73)=k6_partfun1(A_73))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.47/3.34  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.47/3.34  tff(c_119, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_113, c_36])).
% 9.47/3.34  tff(c_3060, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_3027, c_119])).
% 9.47/3.34  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.47/3.34  tff(c_3057, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3027, c_3027, c_14])).
% 9.47/3.34  tff(c_46, plain, (![A_24, B_25]: (k9_relat_1(k6_relat_1(A_24), B_25)=B_25 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.47/3.34  tff(c_358, plain, (![A_99, B_100]: (k9_relat_1(k6_partfun1(A_99), B_100)=B_100 | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 9.47/3.34  tff(c_372, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_1', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_86, c_358])).
% 9.47/3.34  tff(c_3180, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_372])).
% 9.47/3.34  tff(c_3182, plain, (k9_relat_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3060, c_3180])).
% 9.47/3.34  tff(c_3388, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3056, c_3182])).
% 9.47/3.34  tff(c_240, plain, (![A_87]: (v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.47/3.34  tff(c_243, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_240, c_161])).
% 9.47/3.34  tff(c_246, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_243])).
% 9.47/3.34  tff(c_247, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_246])).
% 9.47/3.34  tff(c_3415, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3388, c_247])).
% 9.47/3.34  tff(c_3424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3064, c_3415])).
% 9.47/3.34  tff(c_3425, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_246])).
% 9.47/3.34  tff(c_30, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.47/3.34  tff(c_3434, plain, (![B_317, A_318]: (v1_relat_1(B_317) | ~m1_subset_1(B_317, k1_zfmisc_1(A_318)) | ~v1_relat_1(A_318))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.47/3.34  tff(c_3440, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_3434])).
% 9.47/3.34  tff(c_3452, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3440])).
% 9.47/3.34  tff(c_3454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3425, c_3452])).
% 9.47/3.34  tff(c_3455, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_76])).
% 9.47/3.34  tff(c_3498, plain, (![B_323, A_324]: (v1_relat_1(B_323) | ~m1_subset_1(B_323, k1_zfmisc_1(A_324)) | ~v1_relat_1(A_324))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.47/3.34  tff(c_3504, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_3498])).
% 9.47/3.34  tff(c_3516, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3504])).
% 9.47/3.34  tff(c_3871, plain, (![A_367, B_368, C_369]: (k2_relset_1(A_367, B_368, C_369)=k2_relat_1(C_369) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.47/3.34  tff(c_3892, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_3871])).
% 9.47/3.34  tff(c_4722, plain, (![A_439, B_440, C_441, D_442]: (k2_relset_1(A_439, B_440, C_441)=B_440 | ~r2_relset_1(B_440, B_440, k1_partfun1(B_440, A_439, A_439, B_440, D_442, C_441), k6_partfun1(B_440)) | ~m1_subset_1(D_442, k1_zfmisc_1(k2_zfmisc_1(B_440, A_439))) | ~v1_funct_2(D_442, B_440, A_439) | ~v1_funct_1(D_442) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~v1_funct_2(C_441, A_439, B_440) | ~v1_funct_1(C_441))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.47/3.34  tff(c_4725, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_4722])).
% 9.47/3.34  tff(c_4731, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_90, c_88, c_86, c_3892, c_4725])).
% 9.47/3.34  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.47/3.34  tff(c_3631, plain, (![B_336, A_337]: (v5_relat_1(B_336, A_337) | ~r1_tarski(k2_relat_1(B_336), A_337) | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.47/3.34  tff(c_3636, plain, (![B_336]: (v5_relat_1(B_336, k2_relat_1(B_336)) | ~v1_relat_1(B_336))), inference(resolution, [status(thm)], [c_8, c_3631])).
% 9.47/3.34  tff(c_3704, plain, (![B_345]: (v2_funct_2(B_345, k2_relat_1(B_345)) | ~v5_relat_1(B_345, k2_relat_1(B_345)) | ~v1_relat_1(B_345))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.47/3.34  tff(c_3708, plain, (![B_336]: (v2_funct_2(B_336, k2_relat_1(B_336)) | ~v1_relat_1(B_336))), inference(resolution, [status(thm)], [c_3636, c_3704])).
% 9.47/3.34  tff(c_4742, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4731, c_3708])).
% 9.47/3.34  tff(c_4759, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_4742])).
% 9.47/3.34  tff(c_4761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3455, c_4759])).
% 9.47/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/3.34  
% 9.47/3.34  Inference rules
% 9.47/3.34  ----------------------
% 9.47/3.34  #Ref     : 0
% 9.47/3.34  #Sup     : 1119
% 9.47/3.34  #Fact    : 0
% 9.47/3.34  #Define  : 0
% 9.47/3.34  #Split   : 15
% 9.47/3.34  #Chain   : 0
% 9.47/3.34  #Close   : 0
% 9.47/3.34  
% 9.47/3.34  Ordering : KBO
% 9.47/3.34  
% 9.47/3.34  Simplification rules
% 9.47/3.34  ----------------------
% 9.47/3.34  #Subsume      : 15
% 9.47/3.34  #Demod        : 986
% 9.47/3.34  #Tautology    : 478
% 9.47/3.34  #SimpNegUnit  : 4
% 9.47/3.34  #BackRed      : 106
% 9.47/3.34  
% 9.47/3.34  #Partial instantiations: 0
% 9.47/3.34  #Strategies tried      : 1
% 9.47/3.34  
% 9.47/3.34  Timing (in seconds)
% 9.47/3.34  ----------------------
% 9.47/3.34  Preprocessing        : 0.61
% 9.47/3.34  Parsing              : 0.32
% 9.47/3.34  CNF conversion       : 0.05
% 9.47/3.34  Main loop            : 1.86
% 9.47/3.34  Inferencing          : 0.63
% 9.47/3.34  Reduction            : 0.69
% 9.47/3.34  Demodulation         : 0.52
% 9.47/3.34  BG Simplification    : 0.08
% 9.47/3.34  Subsumption          : 0.29
% 9.47/3.34  Abstraction          : 0.08
% 9.47/3.34  MUC search           : 0.00
% 9.47/3.34  Cooper               : 0.00
% 9.47/3.34  Total                : 2.54
% 9.47/3.34  Index Insertion      : 0.00
% 9.47/3.34  Index Deletion       : 0.00
% 9.47/3.34  Index Matching       : 0.00
% 9.47/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
