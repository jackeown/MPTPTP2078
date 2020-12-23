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
% DateTime   : Thu Dec  3 10:13:20 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 278 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 (1175 expanded)
%              Number of equality atoms :   94 ( 409 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_46,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_135,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_147,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_189,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_189])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_147,c_198])).

tff(c_208,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_207])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_86])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_92,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_146,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_135])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_189])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_146,c_195])).

tff(c_204,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_203])).

tff(c_38,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_654,plain,(
    ! [A_139,B_140] :
      ( k2_funct_1(A_139) = B_140
      | k6_partfun1(k1_relat_1(A_139)) != k5_relat_1(A_139,B_140)
      | k2_relat_1(A_139) != k1_relat_1(B_140)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_658,plain,(
    ! [B_140] :
      ( k2_funct_1('#skF_3') = B_140
      | k5_relat_1('#skF_3',B_140) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_140)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_654])).

tff(c_665,plain,(
    ! [B_141] :
      ( k2_funct_1('#skF_3') = B_141
      | k5_relat_1('#skF_3',B_141) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_141)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_68,c_52,c_658])).

tff(c_671,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_665])).

tff(c_681,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_208,c_671])).

tff(c_682,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_681])).

tff(c_687,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_636,plain,(
    ! [C_135,B_136,A_137] :
      ( v1_funct_2(k2_funct_1(C_135),B_136,A_137)
      | k2_relset_1(A_137,B_136,C_135) != B_136
      | ~ v2_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_2(C_135,A_137,B_136)
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_642,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_636])).

tff(c_649,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_52,c_56,c_642])).

tff(c_738,plain,(
    ! [C_155,B_156,A_157] :
      ( m1_subset_1(k2_funct_1(C_155),k1_zfmisc_1(k2_zfmisc_1(B_156,A_157)))
      | k2_relset_1(A_157,B_156,C_155) != B_156
      | ~ v2_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_2(C_155,A_157,B_156)
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1709,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_relset_1(B_205,A_206,k2_funct_1(C_207)) = k1_relat_1(k2_funct_1(C_207))
      | k2_relset_1(A_206,B_205,C_207) != B_205
      | ~ v2_funct_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ v1_funct_1(C_207) ) ),
    inference(resolution,[status(thm)],[c_738,c_12])).

tff(c_1739,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1709])).

tff(c_1766,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_52,c_56,c_1739])).

tff(c_30,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2149,plain,(
    ! [A_213,B_214,C_215] :
      ( k1_xboole_0 = A_213
      | k1_relset_1(B_214,A_213,k2_funct_1(C_215)) = B_214
      | ~ v1_funct_2(k2_funct_1(C_215),B_214,A_213)
      | k2_relset_1(A_213,B_214,C_215) != B_214
      | ~ v2_funct_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_2(C_215,A_213,B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_738,c_30])).

tff(c_2188,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2149])).

tff(c_2233,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_52,c_56,c_649,c_1766,c_2188])).

tff(c_2234,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2233])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2245,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_8])).

tff(c_2254,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_68,c_52,c_2245])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_2254])).

tff(c_2257,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_557,plain,(
    ! [E_133,B_132,F_131,C_130,A_128,D_129] :
      ( m1_subset_1(k1_partfun1(A_128,B_132,C_130,D_129,E_133,F_131),k1_zfmisc_1(k2_zfmisc_1(A_128,D_129)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_130,D_129)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_128,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_69,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_257,plain,(
    ! [D_70,C_71,A_72,B_73] :
      ( D_70 = C_71
      | ~ r2_relset_1(A_72,B_73,C_71,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_265,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_257])).

tff(c_280,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_265])).

tff(c_299,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_581,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_557,c_299])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_581])).

tff(c_623,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_2346,plain,(
    ! [A_239,B_238,F_234,C_235,E_237,D_236] :
      ( k1_partfun1(A_239,B_238,C_235,D_236,E_237,F_234) = k5_relat_1(E_237,F_234)
      | ~ m1_subset_1(F_234,k1_zfmisc_1(k2_zfmisc_1(C_235,D_236)))
      | ~ v1_funct_1(F_234)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2352,plain,(
    ! [A_239,B_238,E_237] :
      ( k1_partfun1(A_239,B_238,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_58,c_2346])).

tff(c_2463,plain,(
    ! [A_247,B_248,E_249] :
      ( k1_partfun1(A_247,B_248,'#skF_2','#skF_1',E_249,'#skF_4') = k5_relat_1(E_249,'#skF_4')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_1(E_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2352])).

tff(c_2472,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2463])).

tff(c_2480,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_623,c_2472])).

tff(c_2482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2257,c_2480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.89  
% 4.91/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.89  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.91/1.89  
% 4.91/1.89  %Foreground sorts:
% 4.91/1.89  
% 4.91/1.89  
% 4.91/1.89  %Background operators:
% 4.91/1.89  
% 4.91/1.89  
% 4.91/1.89  %Foreground operators:
% 4.91/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.91/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.91/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.91/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.91/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.91/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.91/1.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.91/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.91/1.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.91/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.91/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.91/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.91/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.91/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.91/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.91/1.89  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.91/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.91/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.91/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.91/1.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.91/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.91/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.91/1.89  
% 5.25/1.91  tff(f_159, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.25/1.91  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.25/1.91  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.25/1.91  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.25/1.91  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.25/1.91  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.25/1.91  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.25/1.91  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.25/1.91  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.25/1.91  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.25/1.91  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.25/1.91  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.25/1.91  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.25/1.91  tff(c_46, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_50, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_135, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.25/1.91  tff(c_147, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_135])).
% 5.25/1.91  tff(c_189, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.25/1.91  tff(c_198, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_189])).
% 5.25/1.91  tff(c_207, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_147, c_198])).
% 5.25/1.91  tff(c_208, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_207])).
% 5.25/1.91  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.25/1.91  tff(c_86, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.25/1.91  tff(c_95, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_86])).
% 5.25/1.91  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_95])).
% 5.25/1.91  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_92, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_86])).
% 5.25/1.91  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_92])).
% 5.25/1.91  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_146, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_135])).
% 5.25/1.91  tff(c_195, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_189])).
% 5.25/1.91  tff(c_203, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_146, c_195])).
% 5.25/1.91  tff(c_204, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_48, c_203])).
% 5.25/1.91  tff(c_38, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.25/1.91  tff(c_10, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.25/1.91  tff(c_654, plain, (![A_139, B_140]: (k2_funct_1(A_139)=B_140 | k6_partfun1(k1_relat_1(A_139))!=k5_relat_1(A_139, B_140) | k2_relat_1(A_139)!=k1_relat_1(B_140) | ~v2_funct_1(A_139) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 5.25/1.91  tff(c_658, plain, (![B_140]: (k2_funct_1('#skF_3')=B_140 | k5_relat_1('#skF_3', B_140)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_140) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_654])).
% 5.25/1.91  tff(c_665, plain, (![B_141]: (k2_funct_1('#skF_3')=B_141 | k5_relat_1('#skF_3', B_141)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_141) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_68, c_52, c_658])).
% 5.25/1.91  tff(c_671, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_665])).
% 5.25/1.91  tff(c_681, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_208, c_671])).
% 5.25/1.91  tff(c_682, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_681])).
% 5.25/1.91  tff(c_687, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_682])).
% 5.25/1.91  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_636, plain, (![C_135, B_136, A_137]: (v1_funct_2(k2_funct_1(C_135), B_136, A_137) | k2_relset_1(A_137, B_136, C_135)!=B_136 | ~v2_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_2(C_135, A_137, B_136) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.25/1.91  tff(c_642, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_636])).
% 5.25/1.91  tff(c_649, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_52, c_56, c_642])).
% 5.25/1.91  tff(c_738, plain, (![C_155, B_156, A_157]: (m1_subset_1(k2_funct_1(C_155), k1_zfmisc_1(k2_zfmisc_1(B_156, A_157))) | k2_relset_1(A_157, B_156, C_155)!=B_156 | ~v2_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_2(C_155, A_157, B_156) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.25/1.91  tff(c_12, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.25/1.91  tff(c_1709, plain, (![B_205, A_206, C_207]: (k1_relset_1(B_205, A_206, k2_funct_1(C_207))=k1_relat_1(k2_funct_1(C_207)) | k2_relset_1(A_206, B_205, C_207)!=B_205 | ~v2_funct_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_2(C_207, A_206, B_205) | ~v1_funct_1(C_207))), inference(resolution, [status(thm)], [c_738, c_12])).
% 5.25/1.91  tff(c_1739, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1709])).
% 5.25/1.91  tff(c_1766, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_52, c_56, c_1739])).
% 5.25/1.91  tff(c_30, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.25/1.91  tff(c_2149, plain, (![A_213, B_214, C_215]: (k1_xboole_0=A_213 | k1_relset_1(B_214, A_213, k2_funct_1(C_215))=B_214 | ~v1_funct_2(k2_funct_1(C_215), B_214, A_213) | k2_relset_1(A_213, B_214, C_215)!=B_214 | ~v2_funct_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_2(C_215, A_213, B_214) | ~v1_funct_1(C_215))), inference(resolution, [status(thm)], [c_738, c_30])).
% 5.25/1.91  tff(c_2188, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2149])).
% 5.25/1.91  tff(c_2233, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_52, c_56, c_649, c_1766, c_2188])).
% 5.25/1.91  tff(c_2234, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_2233])).
% 5.25/1.91  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.25/1.91  tff(c_2245, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2234, c_8])).
% 5.25/1.91  tff(c_2254, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_68, c_52, c_2245])).
% 5.25/1.91  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_687, c_2254])).
% 5.25/1.91  tff(c_2257, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_682])).
% 5.25/1.91  tff(c_557, plain, (![E_133, B_132, F_131, C_130, A_128, D_129]: (m1_subset_1(k1_partfun1(A_128, B_132, C_130, D_129, E_133, F_131), k1_zfmisc_1(k2_zfmisc_1(A_128, D_129))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_130, D_129))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_128, B_132))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.25/1.91  tff(c_18, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.25/1.91  tff(c_69, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18])).
% 5.25/1.91  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.25/1.91  tff(c_257, plain, (![D_70, C_71, A_72, B_73]: (D_70=C_71 | ~r2_relset_1(A_72, B_73, C_71, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.25/1.91  tff(c_265, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_257])).
% 5.25/1.91  tff(c_280, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_265])).
% 5.25/1.91  tff(c_299, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_280])).
% 5.25/1.91  tff(c_581, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_557, c_299])).
% 5.25/1.91  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_581])).
% 5.25/1.91  tff(c_623, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_280])).
% 5.25/1.91  tff(c_2346, plain, (![A_239, B_238, F_234, C_235, E_237, D_236]: (k1_partfun1(A_239, B_238, C_235, D_236, E_237, F_234)=k5_relat_1(E_237, F_234) | ~m1_subset_1(F_234, k1_zfmisc_1(k2_zfmisc_1(C_235, D_236))) | ~v1_funct_1(F_234) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.25/1.91  tff(c_2352, plain, (![A_239, B_238, E_237]: (k1_partfun1(A_239, B_238, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_58, c_2346])).
% 5.25/1.91  tff(c_2463, plain, (![A_247, B_248, E_249]: (k1_partfun1(A_247, B_248, '#skF_2', '#skF_1', E_249, '#skF_4')=k5_relat_1(E_249, '#skF_4') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_1(E_249))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2352])).
% 5.25/1.91  tff(c_2472, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2463])).
% 5.25/1.91  tff(c_2480, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_623, c_2472])).
% 5.25/1.91  tff(c_2482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2257, c_2480])).
% 5.25/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/1.91  
% 5.25/1.91  Inference rules
% 5.25/1.91  ----------------------
% 5.25/1.91  #Ref     : 0
% 5.25/1.91  #Sup     : 490
% 5.25/1.91  #Fact    : 0
% 5.25/1.91  #Define  : 0
% 5.25/1.91  #Split   : 17
% 5.25/1.91  #Chain   : 0
% 5.25/1.91  #Close   : 0
% 5.25/1.91  
% 5.25/1.91  Ordering : KBO
% 5.25/1.91  
% 5.25/1.91  Simplification rules
% 5.25/1.91  ----------------------
% 5.25/1.91  #Subsume      : 32
% 5.25/1.91  #Demod        : 362
% 5.25/1.91  #Tautology    : 84
% 5.25/1.91  #SimpNegUnit  : 43
% 5.25/1.91  #BackRed      : 16
% 5.25/1.91  
% 5.25/1.91  #Partial instantiations: 0
% 5.25/1.91  #Strategies tried      : 1
% 5.25/1.91  
% 5.25/1.91  Timing (in seconds)
% 5.25/1.91  ----------------------
% 5.25/1.92  Preprocessing        : 0.35
% 5.25/1.92  Parsing              : 0.18
% 5.25/1.92  CNF conversion       : 0.02
% 5.25/1.92  Main loop            : 0.79
% 5.25/1.92  Inferencing          : 0.26
% 5.25/1.92  Reduction            : 0.29
% 5.25/1.92  Demodulation         : 0.21
% 5.25/1.92  BG Simplification    : 0.03
% 5.25/1.92  Subsumption          : 0.14
% 5.25/1.92  Abstraction          : 0.04
% 5.25/1.92  MUC search           : 0.00
% 5.25/1.92  Cooper               : 0.00
% 5.25/1.92  Total                : 1.18
% 5.25/1.92  Index Insertion      : 0.00
% 5.25/1.92  Index Deletion       : 0.00
% 5.25/1.92  Index Matching       : 0.00
% 5.25/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
