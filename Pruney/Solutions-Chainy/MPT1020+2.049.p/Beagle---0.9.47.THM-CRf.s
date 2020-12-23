%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :  196 (2291 expanded)
%              Number of leaves         :   48 ( 781 expanded)
%              Depth                    :   17
%              Number of atoms          :  342 (5609 expanded)
%              Number of equality atoms :   88 ( 804 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_194,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_172,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_64,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_733,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_relset_1(A_139,B_140,D_141,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_745,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_733])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_164])).

tff(c_188,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_176])).

tff(c_284,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_302,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_284])).

tff(c_333,plain,(
    ! [B_92,A_93] :
      ( k2_relat_1(B_92) = A_93
      | ~ v2_funct_2(B_92,A_93)
      | ~ v5_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_342,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_333])).

tff(c_354,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_342])).

tff(c_360,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_574,plain,(
    ! [C_121,B_122,A_123] :
      ( v2_funct_2(C_121,B_122)
      | ~ v3_funct_2(C_121,A_123,B_122)
      | ~ v1_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_583,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_574])).

tff(c_596,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_583])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_596])).

tff(c_599,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_756,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_765,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_756])).

tff(c_776,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_765])).

tff(c_52,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_79,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_744,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_79,c_733])).

tff(c_799,plain,(
    ! [C_147,A_148,B_149] :
      ( v2_funct_1(C_147)
      | ~ v3_funct_2(C_147,A_148,B_149)
      | ~ v1_funct_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_808,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_799])).

tff(c_821,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_808])).

tff(c_1072,plain,(
    ! [B_204,A_200,F_202,D_201,C_205,E_203] :
      ( m1_subset_1(k1_partfun1(A_200,B_204,C_205,D_201,E_203,F_202),k1_zfmisc_1(k2_zfmisc_1(A_200,D_201)))
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_205,D_201)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_200,B_204)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_875,plain,(
    ! [D_161,C_162,A_163,B_164] :
      ( D_161 = C_162
      | ~ r2_relset_1(A_163,B_164,C_162,D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_885,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_875])).

tff(c_904,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_885])).

tff(c_924,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_1083,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1072,c_924])).

tff(c_1122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_64,c_1083])).

tff(c_1123,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_1999,plain,(
    ! [C_386,D_387,B_388,A_389] :
      ( k2_funct_1(C_386) = D_387
      | k1_xboole_0 = B_388
      | k1_xboole_0 = A_389
      | ~ v2_funct_1(C_386)
      | ~ r2_relset_1(A_389,A_389,k1_partfun1(A_389,B_388,B_388,A_389,C_386,D_387),k6_partfun1(A_389))
      | k2_relset_1(A_389,B_388,C_386) != B_388
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(B_388,A_389)))
      | ~ v1_funct_2(D_387,B_388,A_389)
      | ~ v1_funct_1(D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388)))
      | ~ v1_funct_2(C_386,A_389,B_388)
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2002,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_1999])).

tff(c_2007,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_64,c_776,c_744,c_821,c_2002])).

tff(c_2010,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2007])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2053,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2052,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2010,c_12])).

tff(c_211,plain,(
    ! [C_76,B_77,A_78] :
      ( ~ v1_xboole_0(C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_224,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
      | ~ r2_hidden(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_211])).

tff(c_261,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_2200,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_261])).

tff(c_2205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2200])).

tff(c_2206,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2007])).

tff(c_1661,plain,(
    ! [A_315,B_316] :
      ( k2_funct_2(A_315,B_316) = k2_funct_1(B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k2_zfmisc_1(A_315,A_315)))
      | ~ v3_funct_2(B_316,A_315,A_315)
      | ~ v1_funct_2(B_316,A_315,A_315)
      | ~ v1_funct_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1670,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1661])).

tff(c_1686,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1670])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1691,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1686,c_60])).

tff(c_2208,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2206,c_1691])).

tff(c_2212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_2208])).

tff(c_2234,plain,(
    ! [A_404] : ~ r2_hidden(A_404,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_2239,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2234])).

tff(c_133,plain,(
    ! [B_63,A_64] :
      ( ~ v1_xboole_0(B_63)
      | B_63 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_2245,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2239,c_136])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_66] : m1_subset_1(k6_partfun1(A_66),k1_zfmisc_1(k2_zfmisc_1(A_66,A_66))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_147,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_213,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_78,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_147,c_211])).

tff(c_226,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_213])).

tff(c_231,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_226])).

tff(c_237,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_136])).

tff(c_241,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_147])).

tff(c_3310,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_241])).

tff(c_3162,plain,(
    ! [A_501] : k2_zfmisc_1(A_501,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_12])).

tff(c_30,plain,(
    ! [A_24,B_25,D_27] :
      ( r2_relset_1(A_24,B_25,D_27,D_27)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3796,plain,(
    ! [A_572,D_573] :
      ( r2_relset_1(A_572,'#skF_4',D_573,D_573)
      | ~ m1_subset_1(D_573,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_30])).

tff(c_3799,plain,(
    ! [A_572] : r2_relset_1(A_572,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3310,c_3796])).

tff(c_2247,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_237])).

tff(c_173,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_185,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_173])).

tff(c_2215,plain,(
    ! [C_401,B_402,A_403] :
      ( v5_relat_1(C_401,B_402)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_403,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2286,plain,(
    ! [A_406] : v5_relat_1(k6_partfun1(A_406),A_406) ),
    inference(resolution,[status(thm)],[c_79,c_2215])).

tff(c_2289,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_2286])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( k2_relat_1(B_33) = A_32
      | ~ v2_funct_2(B_33,A_32)
      | ~ v5_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2328,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2289,c_44])).

tff(c_2331,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_2328])).

tff(c_2557,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2331])).

tff(c_2214,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_2337,plain,(
    ! [A_410] :
      ( A_410 = '#skF_4'
      | ~ v1_xboole_0(A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_136])).

tff(c_2347,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2214,c_2337])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2723,plain,(
    ! [B_445,A_446] :
      ( B_445 = '#skF_4'
      | A_446 = '#skF_4'
      | k2_zfmisc_1(A_446,B_445) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_2245,c_10])).

tff(c_2733,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_2723])).

tff(c_66,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2746,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2733,c_2733,c_66])).

tff(c_2598,plain,(
    ! [C_427,B_428,A_429] :
      ( v2_funct_2(C_427,B_428)
      | ~ v3_funct_2(C_427,A_429,B_428)
      | ~ v1_funct_1(C_427)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(A_429,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2879,plain,(
    ! [A_472] :
      ( v2_funct_2(k6_partfun1(A_472),A_472)
      | ~ v3_funct_2(k6_partfun1(A_472),A_472,A_472)
      | ~ v1_funct_1(k6_partfun1(A_472)) ) ),
    inference(resolution,[status(thm)],[c_79,c_2598])).

tff(c_2882,plain,
    ( v2_funct_2(k6_partfun1('#skF_4'),'#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_2879])).

tff(c_2884,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2247,c_2746,c_2247,c_2882])).

tff(c_2886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2557,c_2884])).

tff(c_2888,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2331])).

tff(c_3065,plain,(
    ! [B_495,A_496] :
      ( B_495 = '#skF_4'
      | A_496 = '#skF_4'
      | k2_zfmisc_1(A_496,B_495) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_2245,c_10])).

tff(c_3075,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_3065])).

tff(c_2232,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2215])).

tff(c_2307,plain,(
    ! [B_408,A_409] :
      ( k2_relat_1(B_408) = A_409
      | ~ v2_funct_2(B_408,A_409)
      | ~ v5_relat_1(B_408,A_409)
      | ~ v1_relat_1(B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2316,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2232,c_2307])).

tff(c_2325,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_2316])).

tff(c_2336,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2325])).

tff(c_3087,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_2336])).

tff(c_3096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2888,c_3087])).

tff(c_3097,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2325])).

tff(c_3416,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_2331])).

tff(c_3417,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3416])).

tff(c_225,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
      | ~ r2_hidden(A_78,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_211])).

tff(c_2290,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_2295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_2290])).

tff(c_2298,plain,(
    ! [A_407] : ~ r2_hidden(A_407,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_2303,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_2298])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3185,plain,(
    ! [A_502] :
      ( A_502 = '#skF_3'
      | ~ v1_xboole_0(A_502) ) ),
    inference(resolution,[status(thm)],[c_2303,c_8])).

tff(c_3198,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2239,c_3185])).

tff(c_3195,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2214,c_3185])).

tff(c_3285,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3198,c_3195])).

tff(c_3583,plain,(
    ! [B_541,A_542] :
      ( B_541 = '#skF_4'
      | A_542 = '#skF_4'
      | k2_zfmisc_1(A_542,B_541) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_2245,c_2245,c_10])).

tff(c_3593,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3285,c_3583])).

tff(c_3098,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2325])).

tff(c_3606,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_3098])).

tff(c_3614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3417,c_3606])).

tff(c_3615,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3416])).

tff(c_3635,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3615,c_68])).

tff(c_3634,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3615,c_66])).

tff(c_22,plain,(
    ! [A_17] : k2_funct_1(k6_relat_1(A_17)) = k6_relat_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    ! [A_17] : k2_funct_1(k6_partfun1(A_17)) = k6_partfun1(A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_22])).

tff(c_3695,plain,(
    ! [A_553,B_554] :
      ( k2_funct_2(A_553,B_554) = k2_funct_1(B_554)
      | ~ m1_subset_1(B_554,k1_zfmisc_1(k2_zfmisc_1(A_553,A_553)))
      | ~ v3_funct_2(B_554,A_553,A_553)
      | ~ v1_funct_2(B_554,A_553,A_553)
      | ~ v1_funct_1(B_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3706,plain,(
    ! [A_28] :
      ( k2_funct_2(A_28,k6_partfun1(A_28)) = k2_funct_1(k6_partfun1(A_28))
      | ~ v3_funct_2(k6_partfun1(A_28),A_28,A_28)
      | ~ v1_funct_2(k6_partfun1(A_28),A_28,A_28)
      | ~ v1_funct_1(k6_partfun1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_79,c_3695])).

tff(c_3953,plain,(
    ! [A_605] :
      ( k2_funct_2(A_605,k6_partfun1(A_605)) = k6_partfun1(A_605)
      | ~ v3_funct_2(k6_partfun1(A_605),A_605,A_605)
      | ~ v1_funct_2(k6_partfun1(A_605),A_605,A_605)
      | ~ v1_funct_1(k6_partfun1(A_605)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3706])).

tff(c_3956,plain,
    ( k2_funct_2('#skF_4',k6_partfun1('#skF_4')) = k6_partfun1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_3953])).

tff(c_3958,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2247,c_3635,c_2247,c_3634,c_2247,c_2247,c_3956])).

tff(c_3208,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3198,c_60])).

tff(c_3627,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3615,c_3615,c_3208])).

tff(c_3964,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3958,c_3627])).

tff(c_3967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_3964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.09  
% 5.93/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.09  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.93/2.09  
% 5.93/2.09  %Foreground sorts:
% 5.93/2.09  
% 5.93/2.09  
% 5.93/2.09  %Background operators:
% 5.93/2.09  
% 5.93/2.09  
% 5.93/2.09  %Foreground operators:
% 5.93/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.93/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.93/2.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.93/2.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.93/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.93/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.93/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.09  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.93/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.93/2.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.93/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.93/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.09  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.93/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.93/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.09  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.93/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.93/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.93/2.09  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.93/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.93/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.09  
% 6.19/2.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.19/2.12  tff(f_194, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 6.19/2.12  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.19/2.12  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.19/2.12  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.19/2.12  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.19/2.12  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.19/2.12  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.19/2.12  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.19/2.12  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.19/2.12  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.19/2.12  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.19/2.12  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.19/2.12  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.19/2.12  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.19/2.12  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.19/2.12  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.19/2.12  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.19/2.12  tff(f_64, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 6.19/2.12  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.19/2.12  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_733, plain, (![A_139, B_140, D_141]: (r2_relset_1(A_139, B_140, D_141, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.19/2.12  tff(c_745, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_733])).
% 6.19/2.12  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.19/2.12  tff(c_164, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.19/2.12  tff(c_176, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_164])).
% 6.19/2.12  tff(c_188, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_176])).
% 6.19/2.12  tff(c_284, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.19/2.12  tff(c_302, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_284])).
% 6.19/2.12  tff(c_333, plain, (![B_92, A_93]: (k2_relat_1(B_92)=A_93 | ~v2_funct_2(B_92, A_93) | ~v5_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.19/2.12  tff(c_342, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_302, c_333])).
% 6.19/2.12  tff(c_354, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_342])).
% 6.19/2.12  tff(c_360, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_354])).
% 6.19/2.12  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_574, plain, (![C_121, B_122, A_123]: (v2_funct_2(C_121, B_122) | ~v3_funct_2(C_121, A_123, B_122) | ~v1_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.19/2.12  tff(c_583, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_574])).
% 6.19/2.12  tff(c_596, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_583])).
% 6.19/2.12  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_596])).
% 6.19/2.12  tff(c_599, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_354])).
% 6.19/2.12  tff(c_756, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.19/2.12  tff(c_765, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_756])).
% 6.19/2.12  tff(c_776, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_599, c_765])).
% 6.19/2.12  tff(c_52, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.19/2.12  tff(c_34, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.19/2.12  tff(c_79, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34])).
% 6.19/2.12  tff(c_744, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_79, c_733])).
% 6.19/2.12  tff(c_799, plain, (![C_147, A_148, B_149]: (v2_funct_1(C_147) | ~v3_funct_2(C_147, A_148, B_149) | ~v1_funct_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.19/2.12  tff(c_808, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_799])).
% 6.19/2.12  tff(c_821, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_808])).
% 6.19/2.12  tff(c_1072, plain, (![B_204, A_200, F_202, D_201, C_205, E_203]: (m1_subset_1(k1_partfun1(A_200, B_204, C_205, D_201, E_203, F_202), k1_zfmisc_1(k2_zfmisc_1(A_200, D_201))) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_205, D_201))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_200, B_204))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.19/2.12  tff(c_62, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_875, plain, (![D_161, C_162, A_163, B_164]: (D_161=C_162 | ~r2_relset_1(A_163, B_164, C_162, D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.19/2.12  tff(c_885, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_875])).
% 6.19/2.12  tff(c_904, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_885])).
% 6.19/2.12  tff(c_924, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_904])).
% 6.19/2.12  tff(c_1083, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1072, c_924])).
% 6.19/2.12  tff(c_1122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_64, c_1083])).
% 6.19/2.12  tff(c_1123, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_904])).
% 6.19/2.12  tff(c_1999, plain, (![C_386, D_387, B_388, A_389]: (k2_funct_1(C_386)=D_387 | k1_xboole_0=B_388 | k1_xboole_0=A_389 | ~v2_funct_1(C_386) | ~r2_relset_1(A_389, A_389, k1_partfun1(A_389, B_388, B_388, A_389, C_386, D_387), k6_partfun1(A_389)) | k2_relset_1(A_389, B_388, C_386)!=B_388 | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(B_388, A_389))) | ~v1_funct_2(D_387, B_388, A_389) | ~v1_funct_1(D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))) | ~v1_funct_2(C_386, A_389, B_388) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.19/2.12  tff(c_2002, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_1999])).
% 6.19/2.12  tff(c_2007, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_64, c_776, c_744, c_821, c_2002])).
% 6.19/2.12  tff(c_2010, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2007])).
% 6.19/2.12  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.19/2.12  tff(c_2053, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_6])).
% 6.19/2.12  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.19/2.12  tff(c_2052, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2010, c_12])).
% 6.19/2.12  tff(c_211, plain, (![C_76, B_77, A_78]: (~v1_xboole_0(C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.19/2.12  tff(c_224, plain, (![A_78]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | ~r2_hidden(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_211])).
% 6.19/2.12  tff(c_261, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_224])).
% 6.19/2.12  tff(c_2200, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_261])).
% 6.19/2.12  tff(c_2205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2200])).
% 6.19/2.12  tff(c_2206, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2007])).
% 6.19/2.12  tff(c_1661, plain, (![A_315, B_316]: (k2_funct_2(A_315, B_316)=k2_funct_1(B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(k2_zfmisc_1(A_315, A_315))) | ~v3_funct_2(B_316, A_315, A_315) | ~v1_funct_2(B_316, A_315, A_315) | ~v1_funct_1(B_316))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.19/2.12  tff(c_1670, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1661])).
% 6.19/2.12  tff(c_1686, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1670])).
% 6.19/2.12  tff(c_60, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_1691, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1686, c_60])).
% 6.19/2.12  tff(c_2208, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2206, c_1691])).
% 6.19/2.12  tff(c_2212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_745, c_2208])).
% 6.19/2.12  tff(c_2234, plain, (![A_404]: (~r2_hidden(A_404, '#skF_4'))), inference(splitRight, [status(thm)], [c_224])).
% 6.19/2.12  tff(c_2239, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2234])).
% 6.19/2.12  tff(c_133, plain, (![B_63, A_64]: (~v1_xboole_0(B_63) | B_63=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.19/2.12  tff(c_136, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_6, c_133])).
% 6.19/2.12  tff(c_2245, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2239, c_136])).
% 6.19/2.12  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.19/2.12  tff(c_143, plain, (![A_66]: (m1_subset_1(k6_partfun1(A_66), k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34])).
% 6.19/2.12  tff(c_147, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_143])).
% 6.19/2.12  tff(c_213, plain, (![A_78]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_78, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_211])).
% 6.19/2.12  tff(c_226, plain, (![A_79]: (~r2_hidden(A_79, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_213])).
% 6.19/2.12  tff(c_231, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_226])).
% 6.19/2.12  tff(c_237, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_231, c_136])).
% 6.19/2.12  tff(c_241, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_147])).
% 6.19/2.12  tff(c_3310, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_241])).
% 6.19/2.12  tff(c_3162, plain, (![A_501]: (k2_zfmisc_1(A_501, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_12])).
% 6.19/2.12  tff(c_30, plain, (![A_24, B_25, D_27]: (r2_relset_1(A_24, B_25, D_27, D_27) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.19/2.12  tff(c_3796, plain, (![A_572, D_573]: (r2_relset_1(A_572, '#skF_4', D_573, D_573) | ~m1_subset_1(D_573, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3162, c_30])).
% 6.19/2.12  tff(c_3799, plain, (![A_572]: (r2_relset_1(A_572, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3310, c_3796])).
% 6.19/2.12  tff(c_2247, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_237])).
% 6.19/2.12  tff(c_173, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_164])).
% 6.19/2.12  tff(c_185, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_173])).
% 6.19/2.12  tff(c_2215, plain, (![C_401, B_402, A_403]: (v5_relat_1(C_401, B_402) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_403, B_402))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.19/2.12  tff(c_2286, plain, (![A_406]: (v5_relat_1(k6_partfun1(A_406), A_406))), inference(resolution, [status(thm)], [c_79, c_2215])).
% 6.19/2.12  tff(c_2289, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2247, c_2286])).
% 6.19/2.12  tff(c_44, plain, (![B_33, A_32]: (k2_relat_1(B_33)=A_32 | ~v2_funct_2(B_33, A_32) | ~v5_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.19/2.12  tff(c_2328, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2289, c_44])).
% 6.19/2.12  tff(c_2331, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_2328])).
% 6.19/2.12  tff(c_2557, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_2331])).
% 6.19/2.12  tff(c_2214, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_224])).
% 6.19/2.12  tff(c_2337, plain, (![A_410]: (A_410='#skF_4' | ~v1_xboole_0(A_410))), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_136])).
% 6.19/2.12  tff(c_2347, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_2214, c_2337])).
% 6.19/2.12  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.19/2.12  tff(c_2723, plain, (![B_445, A_446]: (B_445='#skF_4' | A_446='#skF_4' | k2_zfmisc_1(A_446, B_445)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_2245, c_10])).
% 6.19/2.12  tff(c_2733, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2347, c_2723])).
% 6.19/2.12  tff(c_66, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.19/2.12  tff(c_2746, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2733, c_2733, c_66])).
% 6.19/2.12  tff(c_2598, plain, (![C_427, B_428, A_429]: (v2_funct_2(C_427, B_428) | ~v3_funct_2(C_427, A_429, B_428) | ~v1_funct_1(C_427) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(A_429, B_428))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.19/2.12  tff(c_2879, plain, (![A_472]: (v2_funct_2(k6_partfun1(A_472), A_472) | ~v3_funct_2(k6_partfun1(A_472), A_472, A_472) | ~v1_funct_1(k6_partfun1(A_472)))), inference(resolution, [status(thm)], [c_79, c_2598])).
% 6.19/2.12  tff(c_2882, plain, (v2_funct_2(k6_partfun1('#skF_4'), '#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2247, c_2879])).
% 6.19/2.12  tff(c_2884, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2247, c_2746, c_2247, c_2882])).
% 6.19/2.12  tff(c_2886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2557, c_2884])).
% 6.19/2.12  tff(c_2888, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_2331])).
% 6.19/2.12  tff(c_3065, plain, (![B_495, A_496]: (B_495='#skF_4' | A_496='#skF_4' | k2_zfmisc_1(A_496, B_495)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_2245, c_10])).
% 6.19/2.12  tff(c_3075, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2347, c_3065])).
% 6.19/2.12  tff(c_2232, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_2215])).
% 6.19/2.12  tff(c_2307, plain, (![B_408, A_409]: (k2_relat_1(B_408)=A_409 | ~v2_funct_2(B_408, A_409) | ~v5_relat_1(B_408, A_409) | ~v1_relat_1(B_408))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.19/2.12  tff(c_2316, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2232, c_2307])).
% 6.19/2.12  tff(c_2325, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_2316])).
% 6.19/2.12  tff(c_2336, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_2325])).
% 6.19/2.12  tff(c_3087, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_2336])).
% 6.19/2.12  tff(c_3096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2888, c_3087])).
% 6.19/2.12  tff(c_3097, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_2325])).
% 6.19/2.12  tff(c_3416, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_2331])).
% 6.19/2.12  tff(c_3417, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_3416])).
% 6.19/2.12  tff(c_225, plain, (![A_78]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | ~r2_hidden(A_78, '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_211])).
% 6.19/2.12  tff(c_2290, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_225])).
% 6.19/2.12  tff(c_2295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2214, c_2290])).
% 6.19/2.12  tff(c_2298, plain, (![A_407]: (~r2_hidden(A_407, '#skF_3'))), inference(splitRight, [status(thm)], [c_225])).
% 6.19/2.12  tff(c_2303, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_2298])).
% 6.19/2.12  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.19/2.12  tff(c_3185, plain, (![A_502]: (A_502='#skF_3' | ~v1_xboole_0(A_502))), inference(resolution, [status(thm)], [c_2303, c_8])).
% 6.19/2.12  tff(c_3198, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2239, c_3185])).
% 6.19/2.12  tff(c_3195, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_2214, c_3185])).
% 6.19/2.12  tff(c_3285, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3198, c_3195])).
% 6.19/2.12  tff(c_3583, plain, (![B_541, A_542]: (B_541='#skF_4' | A_542='#skF_4' | k2_zfmisc_1(A_542, B_541)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_2245, c_2245, c_10])).
% 6.19/2.12  tff(c_3593, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3285, c_3583])).
% 6.19/2.12  tff(c_3098, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2325])).
% 6.19/2.12  tff(c_3606, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_3098])).
% 6.19/2.12  tff(c_3614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3417, c_3606])).
% 6.19/2.12  tff(c_3615, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_3416])).
% 6.19/2.12  tff(c_3635, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3615, c_68])).
% 6.19/2.12  tff(c_3634, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3615, c_66])).
% 6.19/2.12  tff(c_22, plain, (![A_17]: (k2_funct_1(k6_relat_1(A_17))=k6_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.19/2.12  tff(c_80, plain, (![A_17]: (k2_funct_1(k6_partfun1(A_17))=k6_partfun1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_22])).
% 6.19/2.12  tff(c_3695, plain, (![A_553, B_554]: (k2_funct_2(A_553, B_554)=k2_funct_1(B_554) | ~m1_subset_1(B_554, k1_zfmisc_1(k2_zfmisc_1(A_553, A_553))) | ~v3_funct_2(B_554, A_553, A_553) | ~v1_funct_2(B_554, A_553, A_553) | ~v1_funct_1(B_554))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.19/2.12  tff(c_3706, plain, (![A_28]: (k2_funct_2(A_28, k6_partfun1(A_28))=k2_funct_1(k6_partfun1(A_28)) | ~v3_funct_2(k6_partfun1(A_28), A_28, A_28) | ~v1_funct_2(k6_partfun1(A_28), A_28, A_28) | ~v1_funct_1(k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_79, c_3695])).
% 6.19/2.12  tff(c_3953, plain, (![A_605]: (k2_funct_2(A_605, k6_partfun1(A_605))=k6_partfun1(A_605) | ~v3_funct_2(k6_partfun1(A_605), A_605, A_605) | ~v1_funct_2(k6_partfun1(A_605), A_605, A_605) | ~v1_funct_1(k6_partfun1(A_605)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3706])).
% 6.19/2.12  tff(c_3956, plain, (k2_funct_2('#skF_4', k6_partfun1('#skF_4'))=k6_partfun1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2247, c_3953])).
% 6.19/2.12  tff(c_3958, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2247, c_3635, c_2247, c_3634, c_2247, c_2247, c_3956])).
% 6.19/2.12  tff(c_3208, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3198, c_60])).
% 6.19/2.12  tff(c_3627, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3615, c_3615, c_3208])).
% 6.19/2.12  tff(c_3964, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3958, c_3627])).
% 6.19/2.12  tff(c_3967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3799, c_3964])).
% 6.19/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.19/2.12  
% 6.19/2.12  Inference rules
% 6.19/2.12  ----------------------
% 6.19/2.12  #Ref     : 0
% 6.19/2.12  #Sup     : 846
% 6.19/2.12  #Fact    : 0
% 6.19/2.12  #Define  : 0
% 6.19/2.12  #Split   : 17
% 6.19/2.12  #Chain   : 0
% 6.19/2.12  #Close   : 0
% 6.19/2.12  
% 6.19/2.12  Ordering : KBO
% 6.19/2.12  
% 6.19/2.12  Simplification rules
% 6.19/2.12  ----------------------
% 6.19/2.12  #Subsume      : 109
% 6.19/2.12  #Demod        : 1111
% 6.19/2.12  #Tautology    : 372
% 6.19/2.12  #SimpNegUnit  : 6
% 6.19/2.12  #BackRed      : 202
% 6.19/2.12  
% 6.19/2.12  #Partial instantiations: 0
% 6.19/2.12  #Strategies tried      : 1
% 6.19/2.12  
% 6.19/2.12  Timing (in seconds)
% 6.19/2.12  ----------------------
% 6.19/2.12  Preprocessing        : 0.34
% 6.19/2.12  Parsing              : 0.18
% 6.19/2.12  CNF conversion       : 0.02
% 6.19/2.12  Main loop            : 0.99
% 6.19/2.12  Inferencing          : 0.35
% 6.19/2.12  Reduction            : 0.34
% 6.19/2.12  Demodulation         : 0.25
% 6.19/2.12  BG Simplification    : 0.04
% 6.19/2.12  Subsumption          : 0.17
% 6.19/2.12  Abstraction          : 0.04
% 6.19/2.12  MUC search           : 0.00
% 6.19/2.12  Cooper               : 0.00
% 6.19/2.12  Total                : 1.39
% 6.19/2.12  Index Insertion      : 0.00
% 6.19/2.12  Index Deletion       : 0.00
% 6.19/2.12  Index Matching       : 0.00
% 6.19/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
