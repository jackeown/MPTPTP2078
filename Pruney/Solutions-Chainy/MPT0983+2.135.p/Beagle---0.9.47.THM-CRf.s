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
% DateTime   : Thu Dec  3 10:12:21 EST 2020

% Result     : Theorem 8.79s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  138 (1379 expanded)
%              Number of leaves         :   51 ( 521 expanded)
%              Depth                    :   16
%              Number of atoms          :  238 (5874 expanded)
%              Number of equality atoms :   59 ( 555 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_151,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_105,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_210,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_131,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_190,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_71,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_78,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_168,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_70,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_917,plain,(
    ! [C_160,B_159,D_158,F_156,A_157,E_161] :
      ( k4_relset_1(A_157,B_159,C_160,D_158,E_161,F_156) = k5_relat_1(E_161,F_156)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_160,D_158)))
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_157,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1159,plain,(
    ! [A_191,B_192,E_193] :
      ( k4_relset_1(A_191,B_192,'#skF_2','#skF_1',E_193,'#skF_4') = k5_relat_1(E_193,'#skF_4')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(resolution,[status(thm)],[c_82,c_917])).

tff(c_1188,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1159])).

tff(c_52,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k4_relset_1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1432,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_52])).

tff(c_1436,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_1432])).

tff(c_62,plain,(
    ! [A_46] : m1_subset_1(k6_relat_1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_93,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_62])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1320,plain,(
    ! [E_197,C_196,F_199,A_200,D_201,B_198] :
      ( k1_partfun1(A_200,B_198,C_196,D_201,E_197,F_199) = k5_relat_1(E_197,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_196,D_201)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_200,B_198)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1332,plain,(
    ! [A_200,B_198,E_197] :
      ( k1_partfun1(A_200,B_198,'#skF_2','#skF_1',E_197,'#skF_4') = k5_relat_1(E_197,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_200,B_198)))
      | ~ v1_funct_1(E_197) ) ),
    inference(resolution,[status(thm)],[c_82,c_1320])).

tff(c_8817,plain,(
    ! [A_564,B_565,E_566] :
      ( k1_partfun1(A_564,B_565,'#skF_2','#skF_1',E_566,'#skF_4') = k5_relat_1(E_566,'#skF_4')
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565)))
      | ~ v1_funct_1(E_566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1332])).

tff(c_8850,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_8817])).

tff(c_8882,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8850])).

tff(c_80,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_8985,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8882,c_80])).

tff(c_60,plain,(
    ! [D_45,C_44,A_42,B_43] :
      ( D_45 = C_44
      | ~ r2_relset_1(A_42,B_43,C_44,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9095,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8985,c_60])).

tff(c_9098,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_93,c_9095])).

tff(c_78,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_163,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_90,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_84,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_76,plain,(
    ! [A_61,B_62,E_66,C_63,D_64] :
      ( k1_xboole_0 = C_63
      | v2_funct_1(D_64)
      | ~ v2_funct_1(k1_partfun1(A_61,B_62,B_62,C_63,D_64,E_66))
      | ~ m1_subset_1(E_66,k1_zfmisc_1(k2_zfmisc_1(B_62,C_63)))
      | ~ v1_funct_2(E_66,B_62,C_63)
      | ~ v1_funct_1(E_66)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_64,A_61,B_62)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_8991,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8882,c_76])).

tff(c_8997,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_8991])).

tff(c_8998,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_8997])).

tff(c_9000,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8998])).

tff(c_9101,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9098,c_9000])).

tff(c_9114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9101])).

tff(c_9115,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8998])).

tff(c_32,plain,(
    ! [A_18] : k9_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9175,plain,(
    ! [A_18] : k9_relat_1('#skF_1',A_18) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_9115,c_32])).

tff(c_106,plain,(
    ! [A_72] : k6_relat_1(A_72) = k6_partfun1(A_72) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_112,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_38])).

tff(c_9177,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_9115,c_112])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9171,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_9115,c_12])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( k9_relat_1(k6_relat_1(A_24),B_25) = B_25
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_456,plain,(
    ! [A_103,B_104] :
      ( k9_relat_1(k6_partfun1(A_103),B_104) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_48])).

tff(c_471,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_1')),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_82,c_456])).

tff(c_9550,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_471])).

tff(c_9555,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9175,c_9177,c_9550])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9179,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_2])).

tff(c_9639,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9555,c_9179])).

tff(c_9626,plain,(
    ! [A_18] : k9_relat_1('#skF_4',A_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9555,c_9555,c_9175])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9173,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_9115,c_14])).

tff(c_470,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_1','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_88,c_456])).

tff(c_9462,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_470])).

tff(c_9466,plain,(
    k9_relat_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9177,c_9462])).

tff(c_9900,plain,(
    k9_relat_1('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9555,c_9466])).

tff(c_9927,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9626,c_9900])).

tff(c_30,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_279,plain,(
    ! [B_90,A_91] :
      ( v1_relat_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_285,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_279])).

tff(c_297,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_285])).

tff(c_319,plain,(
    ! [A_92] :
      ( v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92)
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_322,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_319,c_163])).

tff(c_325,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_92,c_322])).

tff(c_9951,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9927,c_325])).

tff(c_9965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9639,c_9951])).

tff(c_9966,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_10083,plain,(
    ! [B_617,A_618] :
      ( v1_relat_1(B_617)
      | ~ m1_subset_1(B_617,k1_zfmisc_1(A_618))
      | ~ v1_relat_1(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10092,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_82,c_10083])).

tff(c_10104,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10092])).

tff(c_10604,plain,(
    ! [A_665,B_666,C_667] :
      ( k2_relset_1(A_665,B_666,C_667) = k2_relat_1(C_667)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10626,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_10604])).

tff(c_11692,plain,(
    ! [A_744,B_745,C_746,D_747] :
      ( k2_relset_1(A_744,B_745,C_746) = B_745
      | ~ r2_relset_1(B_745,B_745,k1_partfun1(B_745,A_744,A_744,B_745,D_747,C_746),k6_partfun1(B_745))
      | ~ m1_subset_1(D_747,k1_zfmisc_1(k2_zfmisc_1(B_745,A_744)))
      | ~ v1_funct_2(D_747,B_745,A_744)
      | ~ v1_funct_1(D_747)
      | ~ m1_subset_1(C_746,k1_zfmisc_1(k2_zfmisc_1(A_744,B_745)))
      | ~ v1_funct_2(C_746,A_744,B_745)
      | ~ v1_funct_1(C_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_11695,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_11692])).

tff(c_11701,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_92,c_90,c_88,c_10626,c_11695])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10239,plain,(
    ! [B_625,A_626] :
      ( v5_relat_1(B_625,A_626)
      | ~ r1_tarski(k2_relat_1(B_625),A_626)
      | ~ v1_relat_1(B_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10244,plain,(
    ! [B_625] :
      ( v5_relat_1(B_625,k2_relat_1(B_625))
      | ~ v1_relat_1(B_625) ) ),
    inference(resolution,[status(thm)],[c_8,c_10239])).

tff(c_10361,plain,(
    ! [B_637] :
      ( v2_funct_2(B_637,k2_relat_1(B_637))
      | ~ v5_relat_1(B_637,k2_relat_1(B_637))
      | ~ v1_relat_1(B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10365,plain,(
    ! [B_625] :
      ( v2_funct_2(B_625,k2_relat_1(B_625))
      | ~ v1_relat_1(B_625) ) ),
    inference(resolution,[status(thm)],[c_10244,c_10361])).

tff(c_11710,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11701,c_10365])).

tff(c_11725,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10104,c_11710])).

tff(c_11727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9966,c_11725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.79/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.08  
% 8.79/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.08  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.79/3.08  
% 8.79/3.08  %Foreground sorts:
% 8.79/3.08  
% 8.79/3.08  
% 8.79/3.08  %Background operators:
% 8.79/3.08  
% 8.79/3.08  
% 8.79/3.08  %Foreground operators:
% 8.79/3.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.79/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.79/3.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.79/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.79/3.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.79/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.79/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.79/3.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.79/3.08  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.79/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.79/3.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.79/3.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.79/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.79/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.79/3.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.79/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.79/3.08  tff('#skF_1', type, '#skF_1': $i).
% 8.79/3.08  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.79/3.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.79/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.79/3.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.79/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.79/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.79/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.79/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.79/3.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.79/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.79/3.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.79/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.79/3.08  
% 8.79/3.10  tff(f_151, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.79/3.10  tff(f_105, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.79/3.10  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.79/3.10  tff(f_121, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 8.79/3.10  tff(f_111, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 8.79/3.10  tff(f_131, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.79/3.10  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.79/3.10  tff(f_129, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.79/3.10  tff(f_190, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.79/3.10  tff(f_71, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 8.79/3.10  tff(f_78, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 8.79/3.10  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.79/3.10  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 8.79/3.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.79/3.10  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.79/3.10  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.79/3.10  tff(f_90, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 8.79/3.10  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.79/3.10  tff(f_168, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.79/3.10  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.79/3.10  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.79/3.10  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.79/3.10  tff(c_70, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.79/3.10  tff(c_50, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.79/3.10  tff(c_94, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50])).
% 8.79/3.10  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_917, plain, (![C_160, B_159, D_158, F_156, A_157, E_161]: (k4_relset_1(A_157, B_159, C_160, D_158, E_161, F_156)=k5_relat_1(E_161, F_156) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_160, D_158))) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_157, B_159))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.79/3.10  tff(c_1159, plain, (![A_191, B_192, E_193]: (k4_relset_1(A_191, B_192, '#skF_2', '#skF_1', E_193, '#skF_4')=k5_relat_1(E_193, '#skF_4') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(resolution, [status(thm)], [c_82, c_917])).
% 8.79/3.10  tff(c_1188, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_1159])).
% 8.79/3.10  tff(c_52, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k4_relset_1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.79/3.10  tff(c_1432, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_52])).
% 8.79/3.10  tff(c_1436, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_1432])).
% 8.79/3.10  tff(c_62, plain, (![A_46]: (m1_subset_1(k6_relat_1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.10  tff(c_93, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_62])).
% 8.79/3.10  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_1320, plain, (![E_197, C_196, F_199, A_200, D_201, B_198]: (k1_partfun1(A_200, B_198, C_196, D_201, E_197, F_199)=k5_relat_1(E_197, F_199) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_196, D_201))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_200, B_198))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.79/3.10  tff(c_1332, plain, (![A_200, B_198, E_197]: (k1_partfun1(A_200, B_198, '#skF_2', '#skF_1', E_197, '#skF_4')=k5_relat_1(E_197, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_200, B_198))) | ~v1_funct_1(E_197))), inference(resolution, [status(thm)], [c_82, c_1320])).
% 8.79/3.10  tff(c_8817, plain, (![A_564, B_565, E_566]: (k1_partfun1(A_564, B_565, '#skF_2', '#skF_1', E_566, '#skF_4')=k5_relat_1(E_566, '#skF_4') | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_564, B_565))) | ~v1_funct_1(E_566))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1332])).
% 8.79/3.10  tff(c_8850, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_8817])).
% 8.79/3.10  tff(c_8882, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8850])).
% 8.79/3.10  tff(c_80, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_8985, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8882, c_80])).
% 8.79/3.10  tff(c_60, plain, (![D_45, C_44, A_42, B_43]: (D_45=C_44 | ~r2_relset_1(A_42, B_43, C_44, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.79/3.10  tff(c_9095, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_8985, c_60])).
% 8.79/3.10  tff(c_9098, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_93, c_9095])).
% 8.79/3.10  tff(c_78, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_163, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 8.79/3.10  tff(c_90, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_84, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.79/3.10  tff(c_76, plain, (![A_61, B_62, E_66, C_63, D_64]: (k1_xboole_0=C_63 | v2_funct_1(D_64) | ~v2_funct_1(k1_partfun1(A_61, B_62, B_62, C_63, D_64, E_66)) | ~m1_subset_1(E_66, k1_zfmisc_1(k2_zfmisc_1(B_62, C_63))) | ~v1_funct_2(E_66, B_62, C_63) | ~v1_funct_1(E_66) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_64, A_61, B_62) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.79/3.10  tff(c_8991, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8882, c_76])).
% 8.79/3.10  tff(c_8997, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_8991])).
% 8.79/3.10  tff(c_8998, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_163, c_8997])).
% 8.79/3.10  tff(c_9000, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_8998])).
% 8.79/3.10  tff(c_9101, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9098, c_9000])).
% 8.79/3.10  tff(c_9114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_9101])).
% 8.79/3.10  tff(c_9115, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8998])).
% 8.79/3.10  tff(c_32, plain, (![A_18]: (k9_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.79/3.10  tff(c_9175, plain, (![A_18]: (k9_relat_1('#skF_1', A_18)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_9115, c_32])).
% 8.79/3.10  tff(c_106, plain, (![A_72]: (k6_relat_1(A_72)=k6_partfun1(A_72))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.79/3.10  tff(c_38, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.79/3.10  tff(c_112, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_106, c_38])).
% 8.79/3.10  tff(c_9177, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_9115, c_112])).
% 8.79/3.10  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.79/3.10  tff(c_9171, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_9115, c_12])).
% 8.79/3.10  tff(c_48, plain, (![A_24, B_25]: (k9_relat_1(k6_relat_1(A_24), B_25)=B_25 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.79/3.10  tff(c_456, plain, (![A_103, B_104]: (k9_relat_1(k6_partfun1(A_103), B_104)=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_48])).
% 8.79/3.10  tff(c_471, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_1')), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_82, c_456])).
% 8.79/3.10  tff(c_9550, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_471])).
% 8.79/3.10  tff(c_9555, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9175, c_9177, c_9550])).
% 8.79/3.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.79/3.10  tff(c_9179, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_2])).
% 8.79/3.10  tff(c_9639, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9555, c_9179])).
% 8.79/3.10  tff(c_9626, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9555, c_9555, c_9175])).
% 8.79/3.10  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.79/3.10  tff(c_9173, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_9115, c_14])).
% 8.79/3.10  tff(c_470, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_1', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_88, c_456])).
% 8.79/3.10  tff(c_9462, plain, (k9_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_470])).
% 8.79/3.10  tff(c_9466, plain, (k9_relat_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9177, c_9462])).
% 8.79/3.10  tff(c_9900, plain, (k9_relat_1('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9555, c_9466])).
% 8.79/3.10  tff(c_9927, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9626, c_9900])).
% 8.79/3.10  tff(c_30, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.79/3.10  tff(c_279, plain, (![B_90, A_91]: (v1_relat_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.79/3.10  tff(c_285, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_279])).
% 8.79/3.10  tff(c_297, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_285])).
% 8.79/3.10  tff(c_319, plain, (![A_92]: (v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92) | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.79/3.10  tff(c_322, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_319, c_163])).
% 8.79/3.10  tff(c_325, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_92, c_322])).
% 8.79/3.10  tff(c_9951, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9927, c_325])).
% 8.79/3.10  tff(c_9965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9639, c_9951])).
% 8.79/3.10  tff(c_9966, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 8.79/3.10  tff(c_10083, plain, (![B_617, A_618]: (v1_relat_1(B_617) | ~m1_subset_1(B_617, k1_zfmisc_1(A_618)) | ~v1_relat_1(A_618))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.79/3.10  tff(c_10092, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_10083])).
% 8.79/3.10  tff(c_10104, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10092])).
% 8.79/3.10  tff(c_10604, plain, (![A_665, B_666, C_667]: (k2_relset_1(A_665, B_666, C_667)=k2_relat_1(C_667) | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.79/3.10  tff(c_10626, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_10604])).
% 8.79/3.10  tff(c_11692, plain, (![A_744, B_745, C_746, D_747]: (k2_relset_1(A_744, B_745, C_746)=B_745 | ~r2_relset_1(B_745, B_745, k1_partfun1(B_745, A_744, A_744, B_745, D_747, C_746), k6_partfun1(B_745)) | ~m1_subset_1(D_747, k1_zfmisc_1(k2_zfmisc_1(B_745, A_744))) | ~v1_funct_2(D_747, B_745, A_744) | ~v1_funct_1(D_747) | ~m1_subset_1(C_746, k1_zfmisc_1(k2_zfmisc_1(A_744, B_745))) | ~v1_funct_2(C_746, A_744, B_745) | ~v1_funct_1(C_746))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.79/3.10  tff(c_11695, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_11692])).
% 8.79/3.10  tff(c_11701, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_92, c_90, c_88, c_10626, c_11695])).
% 8.79/3.10  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.79/3.10  tff(c_10239, plain, (![B_625, A_626]: (v5_relat_1(B_625, A_626) | ~r1_tarski(k2_relat_1(B_625), A_626) | ~v1_relat_1(B_625))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.79/3.10  tff(c_10244, plain, (![B_625]: (v5_relat_1(B_625, k2_relat_1(B_625)) | ~v1_relat_1(B_625))), inference(resolution, [status(thm)], [c_8, c_10239])).
% 8.79/3.10  tff(c_10361, plain, (![B_637]: (v2_funct_2(B_637, k2_relat_1(B_637)) | ~v5_relat_1(B_637, k2_relat_1(B_637)) | ~v1_relat_1(B_637))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.79/3.10  tff(c_10365, plain, (![B_625]: (v2_funct_2(B_625, k2_relat_1(B_625)) | ~v1_relat_1(B_625))), inference(resolution, [status(thm)], [c_10244, c_10361])).
% 8.79/3.10  tff(c_11710, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11701, c_10365])).
% 8.79/3.10  tff(c_11725, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10104, c_11710])).
% 8.79/3.10  tff(c_11727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9966, c_11725])).
% 8.79/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.10  
% 8.79/3.10  Inference rules
% 8.79/3.10  ----------------------
% 8.79/3.10  #Ref     : 0
% 8.79/3.10  #Sup     : 2581
% 8.79/3.10  #Fact    : 0
% 8.79/3.10  #Define  : 0
% 8.79/3.10  #Split   : 29
% 8.79/3.10  #Chain   : 0
% 8.79/3.10  #Close   : 0
% 8.79/3.10  
% 8.79/3.10  Ordering : KBO
% 8.79/3.10  
% 8.79/3.10  Simplification rules
% 8.79/3.10  ----------------------
% 8.79/3.10  #Subsume      : 71
% 8.79/3.10  #Demod        : 3810
% 8.79/3.10  #Tautology    : 1287
% 8.79/3.10  #SimpNegUnit  : 11
% 8.79/3.10  #BackRed      : 650
% 8.79/3.10  
% 8.79/3.10  #Partial instantiations: 0
% 8.79/3.10  #Strategies tried      : 1
% 8.79/3.10  
% 8.79/3.10  Timing (in seconds)
% 8.79/3.10  ----------------------
% 8.79/3.10  Preprocessing        : 0.37
% 8.79/3.10  Parsing              : 0.20
% 8.79/3.10  CNF conversion       : 0.03
% 8.79/3.10  Main loop            : 1.94
% 8.79/3.10  Inferencing          : 0.56
% 8.79/3.10  Reduction            : 0.82
% 8.79/3.10  Demodulation         : 0.63
% 8.79/3.10  BG Simplification    : 0.07
% 8.79/3.10  Subsumption          : 0.34
% 8.79/3.10  Abstraction          : 0.08
% 8.79/3.10  MUC search           : 0.00
% 8.79/3.10  Cooper               : 0.00
% 8.79/3.10  Total                : 2.36
% 8.79/3.10  Index Insertion      : 0.00
% 8.79/3.10  Index Deletion       : 0.00
% 8.79/3.10  Index Matching       : 0.00
% 8.79/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
