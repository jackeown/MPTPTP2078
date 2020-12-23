%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :  178 (9223 expanded)
%              Number of leaves         :   48 (2938 expanded)
%              Depth                    :   18
%              Number of atoms          :  344 (24754 expanded)
%              Number of equality atoms :   65 (2928 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_142,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_186,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_480,plain,(
    ! [A_117,B_118,D_119] :
      ( r2_relset_1(A_117,B_118,D_119,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_497,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_480])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_369,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_xboole_0(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_391,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_369])).

tff(c_396,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_175,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_195,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_175])).

tff(c_336,plain,(
    ! [C_102,B_103,A_104] :
      ( v5_relat_1(C_102,B_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_358,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_336])).

tff(c_561,plain,(
    ! [B_123,A_124] :
      ( k2_relat_1(B_123) = A_124
      | ~ v2_funct_2(B_123,A_124)
      | ~ v5_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_576,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_561])).

tff(c_591,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_576])).

tff(c_597,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_84,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_715,plain,(
    ! [C_139,B_140,A_141] :
      ( v2_funct_2(C_139,B_140)
      | ~ v3_funct_2(C_139,A_141,B_140)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_725,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_715])).

tff(c_739,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_725])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_739])).

tff(c_742,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_914,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_924,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_914])).

tff(c_937,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_924])).

tff(c_62,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_36,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_89,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_494,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_89,c_480])).

tff(c_957,plain,(
    ! [C_163,A_164,B_165] :
      ( v2_funct_1(C_163)
      | ~ v3_funct_2(C_163,A_164,B_165)
      | ~ v1_funct_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_967,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_957])).

tff(c_981,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_967])).

tff(c_2286,plain,(
    ! [D_242,E_241,F_239,B_243,A_238,C_240] :
      ( m1_subset_1(k1_partfun1(A_238,B_243,C_240,D_242,E_241,F_239),k1_zfmisc_1(k2_zfmisc_1(A_238,D_242)))
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_240,D_242)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_238,B_243)))
      | ~ v1_funct_1(E_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1060,plain,(
    ! [D_174,C_175,A_176,B_177] :
      ( D_174 = C_175
      | ~ r2_relset_1(A_176,B_177,C_175,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1070,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_72,c_1060])).

tff(c_1089,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1070])).

tff(c_1114,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1089])).

tff(c_2304,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2286,c_1114])).

tff(c_2355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_80,c_74,c_2304])).

tff(c_2356,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1089])).

tff(c_3955,plain,(
    ! [C_320,D_321,B_322,A_323] :
      ( k2_funct_1(C_320) = D_321
      | k1_xboole_0 = B_322
      | k1_xboole_0 = A_323
      | ~ v2_funct_1(C_320)
      | ~ r2_relset_1(A_323,A_323,k1_partfun1(A_323,B_322,B_322,A_323,C_320,D_321),k6_partfun1(A_323))
      | k2_relset_1(A_323,B_322,C_320) != B_322
      | ~ m1_subset_1(D_321,k1_zfmisc_1(k2_zfmisc_1(B_322,A_323)))
      | ~ v1_funct_2(D_321,B_322,A_323)
      | ~ v1_funct_1(D_321)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322)))
      | ~ v1_funct_2(C_320,A_323,B_322)
      | ~ v1_funct_1(C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_3964,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2356,c_3955])).

tff(c_3972,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_78,c_74,c_937,c_494,c_981,c_3964])).

tff(c_3975,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3972])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4009,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3975,c_8])).

tff(c_4011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_4009])).

tff(c_4012,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3972])).

tff(c_2846,plain,(
    ! [A_268,B_269] :
      ( k2_funct_2(A_268,B_269) = k2_funct_1(B_269)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(k2_zfmisc_1(A_268,A_268)))
      | ~ v3_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2860,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2846])).

tff(c_2876,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_2860])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_2881,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2876,c_70])).

tff(c_4050,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_2881])).

tff(c_4077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_4050])).

tff(c_4078,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_121,plain,(
    ! [B_60,A_61] :
      ( ~ v1_xboole_0(B_60)
      | B_60 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_4085,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4078,c_124])).

tff(c_4079,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_4092,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4079,c_124])).

tff(c_4114,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_4092])).

tff(c_392,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_369])).

tff(c_4137,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_4114,c_392])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4093,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_4079,c_10])).

tff(c_4243,plain,(
    ! [A_333] :
      ( A_333 = '#skF_3'
      | ~ v1_xboole_0(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_4093])).

tff(c_4250,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4137,c_4243])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4106,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_4085,c_16])).

tff(c_4259,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4106])).

tff(c_4125,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_4114,c_74])).

tff(c_4368,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4259,c_4250,c_4250,c_4125])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4105,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_4085,c_14])).

tff(c_4230,plain,(
    ! [A_330,B_331,D_332] :
      ( r2_relset_1(A_330,B_331,D_332,D_332)
      | ~ m1_subset_1(D_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4232,plain,(
    ! [A_8,D_332] :
      ( r2_relset_1(A_8,'#skF_3',D_332,D_332)
      | ~ m1_subset_1(D_332,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4105,c_4230])).

tff(c_8578,plain,(
    ! [A_576,D_577] :
      ( r2_relset_1(A_576,'#skF_4',D_577,D_577)
      | ~ m1_subset_1(D_577,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4232])).

tff(c_8587,plain,(
    ! [A_576] : r2_relset_1(A_576,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_4368,c_8578])).

tff(c_4428,plain,(
    ! [A_344] :
      ( v1_xboole_0(k6_partfun1(A_344))
      | ~ v1_xboole_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_89,c_369])).

tff(c_4086,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_4078,c_10])).

tff(c_4302,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4086])).

tff(c_4496,plain,(
    ! [A_352] :
      ( k6_partfun1(A_352) = '#skF_4'
      | ~ v1_xboole_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_4428,c_4302])).

tff(c_4504,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4137,c_4496])).

tff(c_4127,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_4114,c_78])).

tff(c_4300,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4127])).

tff(c_76,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_4128,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_4114,c_76])).

tff(c_4253,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4128])).

tff(c_6641,plain,(
    ! [A_478,B_479] :
      ( k2_funct_2(A_478,B_479) = k2_funct_1(B_479)
      | ~ m1_subset_1(B_479,k1_zfmisc_1(k2_zfmisc_1(A_478,A_478)))
      | ~ v3_funct_2(B_479,A_478,A_478)
      | ~ v1_funct_2(B_479,A_478,A_478)
      | ~ v1_funct_1(B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_25068,plain,(
    ! [A_838] :
      ( k2_funct_2(A_838,k6_partfun1(A_838)) = k2_funct_1(k6_partfun1(A_838))
      | ~ v3_funct_2(k6_partfun1(A_838),A_838,A_838)
      | ~ v1_funct_2(k6_partfun1(A_838),A_838,A_838)
      | ~ v1_funct_1(k6_partfun1(A_838)) ) ),
    inference(resolution,[status(thm)],[c_89,c_6641])).

tff(c_25122,plain,
    ( k2_funct_2('#skF_4',k6_partfun1('#skF_4')) = k2_funct_1(k6_partfun1('#skF_4'))
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4504,c_25068])).

tff(c_25124,plain,(
    k2_funct_2('#skF_4','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4504,c_4300,c_4504,c_4253,c_4504,c_4504,c_25122])).

tff(c_4585,plain,(
    ! [A_362,B_363] :
      ( v1_funct_1(k2_funct_2(A_362,B_363))
      | ~ m1_subset_1(B_363,k1_zfmisc_1(k2_zfmisc_1(A_362,A_362)))
      | ~ v3_funct_2(B_363,A_362,A_362)
      | ~ v1_funct_2(B_363,A_362,A_362)
      | ~ v1_funct_1(B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18119,plain,(
    ! [A_741] :
      ( v1_funct_1(k2_funct_2(A_741,k6_partfun1(A_741)))
      | ~ v3_funct_2(k6_partfun1(A_741),A_741,A_741)
      | ~ v1_funct_2(k6_partfun1(A_741),A_741,A_741)
      | ~ v1_funct_1(k6_partfun1(A_741)) ) ),
    inference(resolution,[status(thm)],[c_89,c_4585])).

tff(c_18149,plain,
    ( v1_funct_1(k2_funct_2('#skF_4',k6_partfun1('#skF_4')))
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4504,c_18119])).

tff(c_18151,plain,(
    v1_funct_1(k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4504,c_4300,c_4504,c_4253,c_4504,c_18149])).

tff(c_6777,plain,(
    ! [A_487,B_488] :
      ( v3_funct_2(k2_funct_2(A_487,B_488),A_487,A_487)
      | ~ m1_subset_1(B_488,k1_zfmisc_1(k2_zfmisc_1(A_487,A_487)))
      | ~ v3_funct_2(B_488,A_487,A_487)
      | ~ v1_funct_2(B_488,A_487,A_487)
      | ~ v1_funct_1(B_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_19971,plain,(
    ! [A_773] :
      ( v3_funct_2(k2_funct_2(A_773,k6_partfun1(A_773)),A_773,A_773)
      | ~ v3_funct_2(k6_partfun1(A_773),A_773,A_773)
      | ~ v1_funct_2(k6_partfun1(A_773),A_773,A_773)
      | ~ v1_funct_1(k6_partfun1(A_773)) ) ),
    inference(resolution,[status(thm)],[c_89,c_6777])).

tff(c_4257,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4105])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4436,plain,(
    ! [C_345,A_346,B_347] :
      ( v2_funct_1(C_345)
      | ~ v3_funct_2(C_345,A_346,B_347)
      | ~ v1_funct_1(C_345)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_13573,plain,(
    ! [A_700,A_701,B_702] :
      ( v2_funct_1(A_700)
      | ~ v3_funct_2(A_700,A_701,B_702)
      | ~ v1_funct_1(A_700)
      | ~ r1_tarski(A_700,k2_zfmisc_1(A_701,B_702)) ) ),
    inference(resolution,[status(thm)],[c_20,c_4436])).

tff(c_13600,plain,(
    ! [A_700,A_8] :
      ( v2_funct_1(A_700)
      | ~ v3_funct_2(A_700,A_8,'#skF_4')
      | ~ v1_funct_1(A_700)
      | ~ r1_tarski(A_700,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4257,c_13573])).

tff(c_19975,plain,
    ( v2_funct_1(k2_funct_2('#skF_4',k6_partfun1('#skF_4')))
    | ~ v1_funct_1(k2_funct_2('#skF_4',k6_partfun1('#skF_4')))
    | ~ r1_tarski(k2_funct_2('#skF_4',k6_partfun1('#skF_4')),'#skF_4')
    | ~ v3_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19971,c_13600])).

tff(c_20027,plain,
    ( v2_funct_1(k2_funct_2('#skF_4','#skF_4'))
    | ~ r1_tarski(k2_funct_2('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4504,c_4300,c_4504,c_4253,c_4504,c_4504,c_18151,c_4504,c_4504,c_19975])).

tff(c_20045,plain,(
    ~ r1_tarski(k2_funct_2('#skF_4','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20027])).

tff(c_25126,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25124,c_20045])).

tff(c_52,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k2_funct_2(A_41,B_42),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(A_41,A_41)))
      | ~ v3_funct_2(B_42,A_41,A_41)
      | ~ v1_funct_2(B_42,A_41,A_41)
      | ~ v1_funct_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_25133,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25124,c_52])).

tff(c_25137,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4300,c_4253,c_4368,c_4257,c_4257,c_25133])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25171,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_25137,c_18])).

tff(c_25183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25126,c_25171])).

tff(c_25185,plain,(
    r1_tarski(k2_funct_2('#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_20027])).

tff(c_4265,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4085])).

tff(c_388,plain,(
    ! [C_109] :
      ( v1_xboole_0(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_369])).

tff(c_394,plain,(
    ! [C_109] :
      ( v1_xboole_0(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_388])).

tff(c_4541,plain,(
    ! [C_353] :
      ( v1_xboole_0(C_353)
      | ~ m1_subset_1(C_353,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_394])).

tff(c_4551,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_4541])).

tff(c_25198,plain,(
    v1_xboole_0(k2_funct_2('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_25185,c_4551])).

tff(c_25308,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25198,c_4302])).

tff(c_4121,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_4114,c_4114,c_70])).

tff(c_4495,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4250,c_4250,c_4250,c_4121])).

tff(c_25316,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25308,c_4495])).

tff(c_25325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8587,c_25316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/4.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/4.23  
% 11.40/4.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/4.23  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.40/4.23  
% 11.40/4.23  %Foreground sorts:
% 11.40/4.23  
% 11.40/4.23  
% 11.40/4.23  %Background operators:
% 11.40/4.23  
% 11.40/4.23  
% 11.40/4.23  %Foreground operators:
% 11.40/4.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.40/4.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.40/4.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.40/4.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.40/4.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.40/4.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.40/4.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.40/4.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.40/4.23  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 11.40/4.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.40/4.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.40/4.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.40/4.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.40/4.23  tff('#skF_2', type, '#skF_2': $i).
% 11.40/4.23  tff('#skF_3', type, '#skF_3': $i).
% 11.40/4.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.40/4.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.40/4.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.40/4.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.40/4.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.40/4.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.40/4.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.40/4.23  tff('#skF_4', type, '#skF_4': $i).
% 11.40/4.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.40/4.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.40/4.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.40/4.23  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 11.40/4.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.40/4.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.40/4.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.40/4.23  
% 11.40/4.25  tff(f_208, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 11.40/4.25  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.40/4.25  tff(f_68, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 11.40/4.25  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.40/4.25  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.40/4.25  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 11.40/4.25  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 11.40/4.25  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.40/4.25  tff(f_142, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.40/4.25  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.40/4.25  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.40/4.25  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 11.40/4.25  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.40/4.25  tff(f_140, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 11.40/4.25  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 11.40/4.25  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.40/4.25  tff(f_130, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 11.40/4.25  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.40/4.25  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_480, plain, (![A_117, B_118, D_119]: (r2_relset_1(A_117, B_118, D_119, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.40/4.25  tff(c_497, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_480])).
% 11.40/4.25  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_369, plain, (![C_109, A_110, B_111]: (v1_xboole_0(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.40/4.25  tff(c_391, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_369])).
% 11.40/4.25  tff(c_396, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_391])).
% 11.40/4.25  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_175, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.40/4.25  tff(c_195, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_175])).
% 11.40/4.25  tff(c_336, plain, (![C_102, B_103, A_104]: (v5_relat_1(C_102, B_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.40/4.25  tff(c_358, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_336])).
% 11.40/4.25  tff(c_561, plain, (![B_123, A_124]: (k2_relat_1(B_123)=A_124 | ~v2_funct_2(B_123, A_124) | ~v5_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.40/4.25  tff(c_576, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_561])).
% 11.40/4.25  tff(c_591, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_576])).
% 11.40/4.25  tff(c_597, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_591])).
% 11.40/4.25  tff(c_84, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_715, plain, (![C_139, B_140, A_141]: (v2_funct_2(C_139, B_140) | ~v3_funct_2(C_139, A_141, B_140) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.40/4.25  tff(c_725, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_715])).
% 11.40/4.25  tff(c_739, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_725])).
% 11.40/4.25  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_597, c_739])).
% 11.40/4.25  tff(c_742, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_591])).
% 11.40/4.25  tff(c_914, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.40/4.25  tff(c_924, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_914])).
% 11.40/4.25  tff(c_937, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_742, c_924])).
% 11.40/4.25  tff(c_62, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.40/4.25  tff(c_36, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.40/4.25  tff(c_89, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 11.40/4.25  tff(c_494, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_89, c_480])).
% 11.40/4.25  tff(c_957, plain, (![C_163, A_164, B_165]: (v2_funct_1(C_163) | ~v3_funct_2(C_163, A_164, B_165) | ~v1_funct_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.40/4.25  tff(c_967, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_957])).
% 11.40/4.25  tff(c_981, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_967])).
% 11.40/4.25  tff(c_2286, plain, (![D_242, E_241, F_239, B_243, A_238, C_240]: (m1_subset_1(k1_partfun1(A_238, B_243, C_240, D_242, E_241, F_239), k1_zfmisc_1(k2_zfmisc_1(A_238, D_242))) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_240, D_242))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_238, B_243))) | ~v1_funct_1(E_241))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.40/4.25  tff(c_72, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_1060, plain, (![D_174, C_175, A_176, B_177]: (D_174=C_175 | ~r2_relset_1(A_176, B_177, C_175, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.40/4.25  tff(c_1070, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_72, c_1060])).
% 11.40/4.25  tff(c_1089, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1070])).
% 11.40/4.25  tff(c_1114, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1089])).
% 11.40/4.25  tff(c_2304, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2286, c_1114])).
% 11.40/4.25  tff(c_2355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_80, c_74, c_2304])).
% 11.40/4.25  tff(c_2356, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1089])).
% 11.40/4.25  tff(c_3955, plain, (![C_320, D_321, B_322, A_323]: (k2_funct_1(C_320)=D_321 | k1_xboole_0=B_322 | k1_xboole_0=A_323 | ~v2_funct_1(C_320) | ~r2_relset_1(A_323, A_323, k1_partfun1(A_323, B_322, B_322, A_323, C_320, D_321), k6_partfun1(A_323)) | k2_relset_1(A_323, B_322, C_320)!=B_322 | ~m1_subset_1(D_321, k1_zfmisc_1(k2_zfmisc_1(B_322, A_323))) | ~v1_funct_2(D_321, B_322, A_323) | ~v1_funct_1(D_321) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))) | ~v1_funct_2(C_320, A_323, B_322) | ~v1_funct_1(C_320))), inference(cnfTransformation, [status(thm)], [f_186])).
% 11.40/4.25  tff(c_3964, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2356, c_3955])).
% 11.40/4.25  tff(c_3972, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_80, c_78, c_74, c_937, c_494, c_981, c_3964])).
% 11.40/4.25  tff(c_3975, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3972])).
% 11.40/4.25  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.40/4.25  tff(c_4009, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3975, c_8])).
% 11.40/4.25  tff(c_4011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_4009])).
% 11.40/4.25  tff(c_4012, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3972])).
% 11.40/4.25  tff(c_2846, plain, (![A_268, B_269]: (k2_funct_2(A_268, B_269)=k2_funct_1(B_269) | ~m1_subset_1(B_269, k1_zfmisc_1(k2_zfmisc_1(A_268, A_268))) | ~v3_funct_2(B_269, A_268, A_268) | ~v1_funct_2(B_269, A_268, A_268) | ~v1_funct_1(B_269))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.40/4.25  tff(c_2860, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2846])).
% 11.40/4.25  tff(c_2876, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_2860])).
% 11.40/4.25  tff(c_70, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_2881, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2876, c_70])).
% 11.40/4.25  tff(c_4050, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4012, c_2881])).
% 11.40/4.25  tff(c_4077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_4050])).
% 11.40/4.25  tff(c_4078, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_391])).
% 11.40/4.25  tff(c_121, plain, (![B_60, A_61]: (~v1_xboole_0(B_60) | B_60=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.40/4.25  tff(c_124, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_8, c_121])).
% 11.40/4.25  tff(c_4085, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4078, c_124])).
% 11.40/4.25  tff(c_4079, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_391])).
% 11.40/4.25  tff(c_4092, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4079, c_124])).
% 11.40/4.25  tff(c_4114, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4085, c_4092])).
% 11.40/4.25  tff(c_392, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_369])).
% 11.40/4.25  tff(c_4137, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_4114, c_392])).
% 11.40/4.25  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.40/4.25  tff(c_4093, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_4079, c_10])).
% 11.40/4.25  tff(c_4243, plain, (![A_333]: (A_333='#skF_3' | ~v1_xboole_0(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_4093])).
% 11.40/4.25  tff(c_4250, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4137, c_4243])).
% 11.40/4.25  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.40/4.25  tff(c_4106, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4085, c_4085, c_16])).
% 11.40/4.25  tff(c_4259, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4106])).
% 11.40/4.25  tff(c_4125, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_4114, c_74])).
% 11.40/4.25  tff(c_4368, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4259, c_4250, c_4250, c_4125])).
% 11.40/4.25  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.40/4.25  tff(c_4105, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4085, c_4085, c_14])).
% 11.40/4.25  tff(c_4230, plain, (![A_330, B_331, D_332]: (r2_relset_1(A_330, B_331, D_332, D_332) | ~m1_subset_1(D_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.40/4.25  tff(c_4232, plain, (![A_8, D_332]: (r2_relset_1(A_8, '#skF_3', D_332, D_332) | ~m1_subset_1(D_332, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4105, c_4230])).
% 11.40/4.25  tff(c_8578, plain, (![A_576, D_577]: (r2_relset_1(A_576, '#skF_4', D_577, D_577) | ~m1_subset_1(D_577, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4232])).
% 11.40/4.25  tff(c_8587, plain, (![A_576]: (r2_relset_1(A_576, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_4368, c_8578])).
% 11.40/4.25  tff(c_4428, plain, (![A_344]: (v1_xboole_0(k6_partfun1(A_344)) | ~v1_xboole_0(A_344))), inference(resolution, [status(thm)], [c_89, c_369])).
% 11.40/4.25  tff(c_4086, plain, (![A_6]: (A_6='#skF_3' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_4078, c_10])).
% 11.40/4.25  tff(c_4302, plain, (![A_6]: (A_6='#skF_4' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4086])).
% 11.40/4.25  tff(c_4496, plain, (![A_352]: (k6_partfun1(A_352)='#skF_4' | ~v1_xboole_0(A_352))), inference(resolution, [status(thm)], [c_4428, c_4302])).
% 11.40/4.25  tff(c_4504, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4137, c_4496])).
% 11.40/4.25  tff(c_4127, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_4114, c_78])).
% 11.40/4.25  tff(c_4300, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4127])).
% 11.40/4.25  tff(c_76, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.40/4.25  tff(c_4128, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_4114, c_76])).
% 11.40/4.25  tff(c_4253, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4128])).
% 11.40/4.25  tff(c_6641, plain, (![A_478, B_479]: (k2_funct_2(A_478, B_479)=k2_funct_1(B_479) | ~m1_subset_1(B_479, k1_zfmisc_1(k2_zfmisc_1(A_478, A_478))) | ~v3_funct_2(B_479, A_478, A_478) | ~v1_funct_2(B_479, A_478, A_478) | ~v1_funct_1(B_479))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.40/4.25  tff(c_25068, plain, (![A_838]: (k2_funct_2(A_838, k6_partfun1(A_838))=k2_funct_1(k6_partfun1(A_838)) | ~v3_funct_2(k6_partfun1(A_838), A_838, A_838) | ~v1_funct_2(k6_partfun1(A_838), A_838, A_838) | ~v1_funct_1(k6_partfun1(A_838)))), inference(resolution, [status(thm)], [c_89, c_6641])).
% 11.40/4.25  tff(c_25122, plain, (k2_funct_2('#skF_4', k6_partfun1('#skF_4'))=k2_funct_1(k6_partfun1('#skF_4')) | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4504, c_25068])).
% 11.40/4.25  tff(c_25124, plain, (k2_funct_2('#skF_4', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4504, c_4300, c_4504, c_4253, c_4504, c_4504, c_25122])).
% 11.40/4.25  tff(c_4585, plain, (![A_362, B_363]: (v1_funct_1(k2_funct_2(A_362, B_363)) | ~m1_subset_1(B_363, k1_zfmisc_1(k2_zfmisc_1(A_362, A_362))) | ~v3_funct_2(B_363, A_362, A_362) | ~v1_funct_2(B_363, A_362, A_362) | ~v1_funct_1(B_363))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.40/4.25  tff(c_18119, plain, (![A_741]: (v1_funct_1(k2_funct_2(A_741, k6_partfun1(A_741))) | ~v3_funct_2(k6_partfun1(A_741), A_741, A_741) | ~v1_funct_2(k6_partfun1(A_741), A_741, A_741) | ~v1_funct_1(k6_partfun1(A_741)))), inference(resolution, [status(thm)], [c_89, c_4585])).
% 11.40/4.25  tff(c_18149, plain, (v1_funct_1(k2_funct_2('#skF_4', k6_partfun1('#skF_4'))) | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4504, c_18119])).
% 11.40/4.25  tff(c_18151, plain, (v1_funct_1(k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4504, c_4300, c_4504, c_4253, c_4504, c_18149])).
% 11.40/4.25  tff(c_6777, plain, (![A_487, B_488]: (v3_funct_2(k2_funct_2(A_487, B_488), A_487, A_487) | ~m1_subset_1(B_488, k1_zfmisc_1(k2_zfmisc_1(A_487, A_487))) | ~v3_funct_2(B_488, A_487, A_487) | ~v1_funct_2(B_488, A_487, A_487) | ~v1_funct_1(B_488))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.40/4.25  tff(c_19971, plain, (![A_773]: (v3_funct_2(k2_funct_2(A_773, k6_partfun1(A_773)), A_773, A_773) | ~v3_funct_2(k6_partfun1(A_773), A_773, A_773) | ~v1_funct_2(k6_partfun1(A_773), A_773, A_773) | ~v1_funct_1(k6_partfun1(A_773)))), inference(resolution, [status(thm)], [c_89, c_6777])).
% 11.40/4.25  tff(c_4257, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4105])).
% 11.40/4.25  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.40/4.25  tff(c_4436, plain, (![C_345, A_346, B_347]: (v2_funct_1(C_345) | ~v3_funct_2(C_345, A_346, B_347) | ~v1_funct_1(C_345) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.40/4.25  tff(c_13573, plain, (![A_700, A_701, B_702]: (v2_funct_1(A_700) | ~v3_funct_2(A_700, A_701, B_702) | ~v1_funct_1(A_700) | ~r1_tarski(A_700, k2_zfmisc_1(A_701, B_702)))), inference(resolution, [status(thm)], [c_20, c_4436])).
% 11.40/4.25  tff(c_13600, plain, (![A_700, A_8]: (v2_funct_1(A_700) | ~v3_funct_2(A_700, A_8, '#skF_4') | ~v1_funct_1(A_700) | ~r1_tarski(A_700, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4257, c_13573])).
% 11.40/4.25  tff(c_19975, plain, (v2_funct_1(k2_funct_2('#skF_4', k6_partfun1('#skF_4'))) | ~v1_funct_1(k2_funct_2('#skF_4', k6_partfun1('#skF_4'))) | ~r1_tarski(k2_funct_2('#skF_4', k6_partfun1('#skF_4')), '#skF_4') | ~v3_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(resolution, [status(thm)], [c_19971, c_13600])).
% 11.40/4.25  tff(c_20027, plain, (v2_funct_1(k2_funct_2('#skF_4', '#skF_4')) | ~r1_tarski(k2_funct_2('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4504, c_4300, c_4504, c_4253, c_4504, c_4504, c_18151, c_4504, c_4504, c_19975])).
% 11.40/4.25  tff(c_20045, plain, (~r1_tarski(k2_funct_2('#skF_4', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_20027])).
% 11.40/4.25  tff(c_25126, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25124, c_20045])).
% 11.40/4.25  tff(c_52, plain, (![A_41, B_42]: (m1_subset_1(k2_funct_2(A_41, B_42), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))) | ~v3_funct_2(B_42, A_41, A_41) | ~v1_funct_2(B_42, A_41, A_41) | ~v1_funct_1(B_42))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.40/4.25  tff(c_25133, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25124, c_52])).
% 11.40/4.25  tff(c_25137, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4300, c_4253, c_4368, c_4257, c_4257, c_25133])).
% 11.40/4.25  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.40/4.25  tff(c_25171, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_25137, c_18])).
% 11.40/4.25  tff(c_25183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25126, c_25171])).
% 11.40/4.25  tff(c_25185, plain, (r1_tarski(k2_funct_2('#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_20027])).
% 11.40/4.25  tff(c_4265, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4085])).
% 11.40/4.25  tff(c_388, plain, (![C_109]: (v1_xboole_0(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_369])).
% 11.40/4.25  tff(c_394, plain, (![C_109]: (v1_xboole_0(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_388])).
% 11.40/4.25  tff(c_4541, plain, (![C_353]: (v1_xboole_0(C_353) | ~m1_subset_1(C_353, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_394])).
% 11.40/4.25  tff(c_4551, plain, (![A_10]: (v1_xboole_0(A_10) | ~r1_tarski(A_10, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_4541])).
% 11.40/4.25  tff(c_25198, plain, (v1_xboole_0(k2_funct_2('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_25185, c_4551])).
% 11.40/4.25  tff(c_25308, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_25198, c_4302])).
% 11.40/4.25  tff(c_4121, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_4114, c_4114, c_70])).
% 11.40/4.25  tff(c_4495, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4250, c_4250, c_4250, c_4121])).
% 11.40/4.25  tff(c_25316, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25308, c_4495])).
% 11.40/4.25  tff(c_25325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8587, c_25316])).
% 11.40/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/4.25  
% 11.40/4.25  Inference rules
% 11.40/4.25  ----------------------
% 11.40/4.25  #Ref     : 0
% 11.40/4.25  #Sup     : 6763
% 11.40/4.25  #Fact    : 0
% 11.40/4.25  #Define  : 0
% 11.40/4.25  #Split   : 20
% 11.40/4.25  #Chain   : 0
% 11.40/4.25  #Close   : 0
% 11.40/4.25  
% 11.40/4.25  Ordering : KBO
% 11.40/4.25  
% 11.40/4.25  Simplification rules
% 11.40/4.25  ----------------------
% 11.40/4.25  #Subsume      : 1396
% 11.40/4.25  #Demod        : 5851
% 11.40/4.25  #Tautology    : 2731
% 11.40/4.25  #SimpNegUnit  : 19
% 11.40/4.25  #BackRed      : 136
% 11.40/4.25  
% 11.40/4.25  #Partial instantiations: 0
% 11.40/4.25  #Strategies tried      : 1
% 11.40/4.25  
% 11.40/4.25  Timing (in seconds)
% 11.40/4.25  ----------------------
% 11.40/4.26  Preprocessing        : 0.38
% 11.40/4.26  Parsing              : 0.20
% 11.40/4.26  CNF conversion       : 0.03
% 11.40/4.26  Main loop            : 3.02
% 11.40/4.26  Inferencing          : 0.76
% 11.40/4.26  Reduction            : 1.03
% 11.40/4.26  Demodulation         : 0.77
% 11.40/4.26  BG Simplification    : 0.10
% 11.40/4.26  Subsumption          : 0.94
% 11.40/4.26  Abstraction          : 0.11
% 11.40/4.26  MUC search           : 0.00
% 11.40/4.26  Cooper               : 0.00
% 11.40/4.26  Total                : 3.45
% 11.40/4.26  Index Insertion      : 0.00
% 11.40/4.26  Index Deletion       : 0.00
% 11.40/4.26  Index Matching       : 0.00
% 11.40/4.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
