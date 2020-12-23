%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 9.07s
% Output     : CNFRefutation 9.50s
% Verified   : 
% Statistics : Number of formulae       :  295 (3376 expanded)
%              Number of leaves         :   46 (1134 expanded)
%              Depth                    :   23
%              Number of atoms          :  564 (8715 expanded)
%              Number of equality atoms :  149 (2303 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
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

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_99,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_153,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_149,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1021,plain,(
    ! [C_162,D_160,F_159,A_157,B_158,E_161] :
      ( k1_partfun1(A_157,B_158,C_162,D_160,E_161,F_159) = k5_relat_1(E_161,F_159)
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(C_162,D_160)))
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1029,plain,(
    ! [A_157,B_158,E_161] :
      ( k1_partfun1(A_157,B_158,'#skF_2','#skF_1',E_161,'#skF_4') = k5_relat_1(E_161,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_1(E_161) ) ),
    inference(resolution,[status(thm)],[c_68,c_1021])).

tff(c_1258,plain,(
    ! [A_190,B_191,E_192] :
      ( k1_partfun1(A_190,B_191,'#skF_2','#skF_1',E_192,'#skF_4') = k5_relat_1(E_192,'#skF_4')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1029])).

tff(c_1270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1258])).

tff(c_1279,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1270])).

tff(c_52,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1288,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_52])).

tff(c_1292,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1288])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_79,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_802,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r2_relset_1(A_131,B_132,C_130,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_816,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_802])).

tff(c_839,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_816])).

tff(c_1919,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1279,c_1279,c_839])).

tff(c_28,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_34,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_154,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_163,plain,(
    ! [A_20] :
      ( k1_relat_1(k6_partfun1(A_20)) != k1_xboole_0
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_81,c_154])).

tff(c_170,plain,(
    ! [A_20] :
      ( k1_xboole_0 != A_20
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_163])).

tff(c_225,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_66])).

tff(c_284,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1437,plain,(
    ! [B_199,E_200,C_198,A_201,D_197] :
      ( k1_xboole_0 = C_198
      | v2_funct_1(D_197)
      | ~ v2_funct_1(k1_partfun1(A_201,B_199,B_199,C_198,D_197,E_200))
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(B_199,C_198)))
      | ~ v1_funct_2(E_200,B_199,C_198)
      | ~ v1_funct_1(E_200)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_2(D_197,A_201,B_199)
      | ~ v1_funct_1(D_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1439,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_1437])).

tff(c_1441,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_1439])).

tff(c_1442,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_284,c_1441])).

tff(c_1922,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1442])).

tff(c_1935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1922])).

tff(c_1937,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_226,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_238,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_226])).

tff(c_250,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_238])).

tff(c_24,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_250,c_24])).

tff(c_283,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_1953,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_283])).

tff(c_2173,plain,(
    ! [C_237,B_238,A_239] :
      ( v5_relat_1(C_237,B_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2191,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2173])).

tff(c_235,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_226])).

tff(c_247,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_235])).

tff(c_93,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_32])).

tff(c_30,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_129,plain,(
    ! [A_58] : k2_relat_1(k6_partfun1(A_58)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30])).

tff(c_138,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_129])).

tff(c_1944,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1937,c_138])).

tff(c_1940,plain,(
    ! [A_20] :
      ( A_20 != '#skF_1'
      | k6_partfun1(A_20) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1937,c_170])).

tff(c_82,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2015,plain,(
    ! [B_220,A_221] :
      ( v5_relat_1(B_220,A_221)
      | ~ r1_tarski(k2_relat_1(B_220),A_221)
      | ~ v1_relat_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2075,plain,(
    ! [B_225] :
      ( v5_relat_1(B_225,k2_relat_1(B_225))
      | ~ v1_relat_1(B_225) ) ),
    inference(resolution,[status(thm)],[c_6,c_2015])).

tff(c_2081,plain,(
    ! [A_19] :
      ( v5_relat_1(k6_partfun1(A_19),A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2075])).

tff(c_2085,plain,(
    ! [A_19] : v5_relat_1(k6_partfun1(A_19),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2081])).

tff(c_2208,plain,(
    ! [B_241] :
      ( v2_funct_2(B_241,k2_relat_1(B_241))
      | ~ v5_relat_1(B_241,k2_relat_1(B_241))
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2225,plain,(
    ! [A_19] :
      ( v2_funct_2(k6_partfun1(A_19),k2_relat_1(k6_partfun1(A_19)))
      | ~ v5_relat_1(k6_partfun1(A_19),A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2208])).

tff(c_2239,plain,(
    ! [A_242] : v2_funct_2(k6_partfun1(A_242),A_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2085,c_82,c_2225])).

tff(c_2243,plain,(
    v2_funct_2('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_2239])).

tff(c_2739,plain,(
    ! [D_301,E_302,C_303,A_298,B_299,F_300] :
      ( k1_partfun1(A_298,B_299,C_303,D_301,E_302,F_300) = k5_relat_1(E_302,F_300)
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(C_303,D_301)))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299)))
      | ~ v1_funct_1(E_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2747,plain,(
    ! [A_298,B_299,E_302] :
      ( k1_partfun1(A_298,B_299,'#skF_2','#skF_1',E_302,'#skF_4') = k5_relat_1(E_302,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299)))
      | ~ v1_funct_1(E_302) ) ),
    inference(resolution,[status(thm)],[c_68,c_2739])).

tff(c_2911,plain,(
    ! [A_325,B_326,E_327] :
      ( k1_partfun1(A_325,B_326,'#skF_2','#skF_1',E_327,'#skF_4') = k5_relat_1(E_327,'#skF_4')
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ v1_funct_1(E_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2747])).

tff(c_2923,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2911])).

tff(c_2932,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2923])).

tff(c_2997,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2932,c_52])).

tff(c_3001,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_2997])).

tff(c_190,plain,(
    ! [A_62] :
      ( k1_xboole_0 != A_62
      | k6_partfun1(A_62) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_163])).

tff(c_196,plain,(
    ! [A_62] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_62,A_62)))
      | k1_xboole_0 != A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_79])).

tff(c_2439,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1937,c_196])).

tff(c_1936,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_1980,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1936])).

tff(c_2993,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2932,c_1980])).

tff(c_44,plain,(
    ! [D_27,C_26,A_24,B_25] :
      ( D_27 = C_26
      | ~ r2_relset_1(A_24,B_25,C_26,D_27)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3004,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2993,c_44])).

tff(c_3007,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_1'
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2439,c_3004])).

tff(c_4303,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3001,c_3007])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3033,plain,
    ( v1_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3001,c_8])).

tff(c_3054,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3033])).

tff(c_1941,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != '#skF_1'
      | A_18 = '#skF_1'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1937,c_24])).

tff(c_3061,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'
    | k5_relat_1('#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3054,c_1941])).

tff(c_3196,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3061])).

tff(c_38,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3050,plain,(
    v5_relat_1(k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3001,c_38])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(B_30) = A_29
      | ~ v2_funct_2(B_30,A_29)
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3065,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_1'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3050,c_50])).

tff(c_3068,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_1'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_3065])).

tff(c_3822,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3196,c_3068])).

tff(c_4304,plain,(
    ~ v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4303,c_3822])).

tff(c_4319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2243,c_4304])).

tff(c_4320,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3061])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,B_17)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4342,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4320,c_22])).

tff(c_4348,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_250,c_1944,c_4342])).

tff(c_268,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4419,plain,(
    ! [B_412,A_413] :
      ( k2_relat_1(B_412) = A_413
      | ~ r1_tarski(A_413,k2_relat_1(B_412))
      | ~ v5_relat_1(B_412,A_413)
      | ~ v1_relat_1(B_412) ) ),
    inference(resolution,[status(thm)],[c_268,c_2])).

tff(c_4422,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4348,c_4419])).

tff(c_4462,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2191,c_4422])).

tff(c_4464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1953,c_4462])).

tff(c_4465,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_26,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_258,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_247,c_26])).

tff(c_282,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_4467,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_282])).

tff(c_4493,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_4')
    | '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_225])).

tff(c_4494,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4493])).

tff(c_4873,plain,(
    ! [C_449,B_450,A_451] :
      ( v5_relat_1(C_449,B_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4890,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4873])).

tff(c_4466,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_4483,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4466])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4487,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_4',A_8)
      | ~ v5_relat_1('#skF_4',A_8)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4483,c_16])).

tff(c_4491,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_4',A_8)
      | ~ v5_relat_1('#skF_4',A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_4487])).

tff(c_4897,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4890,c_4491])).

tff(c_4899,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_4897,c_2])).

tff(c_4902,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4494,c_4899])).

tff(c_5803,plain,(
    ! [D_519,C_520,A_521,B_522] :
      ( D_519 = C_520
      | ~ r2_relset_1(A_521,B_522,C_520,D_519)
      | ~ m1_subset_1(D_519,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522)))
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5817,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_5803])).

tff(c_5840,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_5817])).

tff(c_5905,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5840])).

tff(c_6673,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_5905])).

tff(c_6677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_6673])).

tff(c_6678,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5840])).

tff(c_7155,plain,(
    ! [E_616,F_614,B_613,D_615,C_617,A_612] :
      ( k1_partfun1(A_612,B_613,C_617,D_615,E_616,F_614) = k5_relat_1(E_616,F_614)
      | ~ m1_subset_1(F_614,k1_zfmisc_1(k2_zfmisc_1(C_617,D_615)))
      | ~ v1_funct_1(F_614)
      | ~ m1_subset_1(E_616,k1_zfmisc_1(k2_zfmisc_1(A_612,B_613)))
      | ~ v1_funct_1(E_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_7163,plain,(
    ! [A_612,B_613,E_616] :
      ( k1_partfun1(A_612,B_613,'#skF_2','#skF_1',E_616,'#skF_4') = k5_relat_1(E_616,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_616,k1_zfmisc_1(k2_zfmisc_1(A_612,B_613)))
      | ~ v1_funct_1(E_616) ) ),
    inference(resolution,[status(thm)],[c_68,c_7155])).

tff(c_7494,plain,(
    ! [A_641,B_642,E_643] :
      ( k1_partfun1(A_641,B_642,'#skF_2','#skF_1',E_643,'#skF_4') = k5_relat_1(E_643,'#skF_4')
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ v1_funct_1(E_643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7163])).

tff(c_7506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_7494])).

tff(c_7517,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6678,c_7506])).

tff(c_5632,plain,(
    ! [A_501,B_502] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_501,B_502)),k2_relat_1(B_502))
      | ~ v1_relat_1(B_502)
      | ~ v1_relat_1(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5647,plain,(
    ! [A_501] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_501,'#skF_4')),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4483,c_5632])).

tff(c_5657,plain,(
    ! [A_501] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_501,'#skF_4')),'#skF_4')
      | ~ v1_relat_1(A_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_5647])).

tff(c_7530,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),'#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7517,c_5657])).

tff(c_7544,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_82,c_7530])).

tff(c_7546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4902,c_7544])).

tff(c_7548,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4493])).

tff(c_7550,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_74])).

tff(c_40,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7672,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7550,c_40])).

tff(c_117,plain,(
    ! [A_57] : k1_relat_1(k6_partfun1(A_57)) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_126,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_117])).

tff(c_4474,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_126])).

tff(c_4469,plain,(
    ! [A_20] :
      ( A_20 != '#skF_4'
      | k6_partfun1(A_20) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_170])).

tff(c_7699,plain,(
    ! [B_654,A_655] :
      ( v5_relat_1(B_654,A_655)
      | ~ r1_tarski(k2_relat_1(B_654),A_655)
      | ~ v1_relat_1(B_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7708,plain,(
    ! [A_19,A_655] :
      ( v5_relat_1(k6_partfun1(A_19),A_655)
      | ~ r1_tarski(A_19,A_655)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_7699])).

tff(c_7717,plain,(
    ! [A_19,A_655] :
      ( v5_relat_1(k6_partfun1(A_19),A_655)
      | ~ r1_tarski(A_19,A_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_7708])).

tff(c_7898,plain,(
    ! [B_677] :
      ( v2_funct_2(B_677,k2_relat_1(B_677))
      | ~ v5_relat_1(B_677,k2_relat_1(B_677))
      | ~ v1_relat_1(B_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7902,plain,(
    ! [A_19] :
      ( v2_funct_2(k6_partfun1(A_19),k2_relat_1(k6_partfun1(A_19)))
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ r1_tarski(A_19,k2_relat_1(k6_partfun1(A_19))) ) ),
    inference(resolution,[status(thm)],[c_7717,c_7898])).

tff(c_7936,plain,(
    ! [A_678] : v2_funct_2(k6_partfun1(A_678),A_678) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82,c_81,c_82,c_7902])).

tff(c_7959,plain,(
    v2_funct_2('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4469,c_7936])).

tff(c_7551,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_68])).

tff(c_8595,plain,(
    ! [A_741,C_746,E_745,D_744,F_743,B_742] :
      ( k1_partfun1(A_741,B_742,C_746,D_744,E_745,F_743) = k5_relat_1(E_745,F_743)
      | ~ m1_subset_1(F_743,k1_zfmisc_1(k2_zfmisc_1(C_746,D_744)))
      | ~ v1_funct_1(F_743)
      | ~ m1_subset_1(E_745,k1_zfmisc_1(k2_zfmisc_1(A_741,B_742)))
      | ~ v1_funct_1(E_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8599,plain,(
    ! [A_741,B_742,E_745] :
      ( k1_partfun1(A_741,B_742,'#skF_2','#skF_4',E_745,'#skF_4') = k5_relat_1(E_745,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_745,k1_zfmisc_1(k2_zfmisc_1(A_741,B_742)))
      | ~ v1_funct_1(E_745) ) ),
    inference(resolution,[status(thm)],[c_7551,c_8595])).

tff(c_8800,plain,(
    ! [A_770,B_771,E_772] :
      ( k1_partfun1(A_770,B_771,'#skF_2','#skF_4',E_772,'#skF_4') = k5_relat_1(E_772,'#skF_4')
      | ~ m1_subset_1(E_772,k1_zfmisc_1(k2_zfmisc_1(A_770,B_771)))
      | ~ v1_funct_1(E_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8599])).

tff(c_8812,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7550,c_8800])).

tff(c_8825,plain,(
    k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8812])).

tff(c_8910,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8825,c_52])).

tff(c_8914,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7550,c_72,c_7551,c_8910])).

tff(c_8032,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_196])).

tff(c_4551,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_170])).

tff(c_7549,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_7548,c_7548,c_7548,c_7548,c_66])).

tff(c_7746,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4551,c_7549])).

tff(c_8906,plain,(
    r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8825,c_7746])).

tff(c_8917,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8906,c_44])).

tff(c_8920,plain,
    ( k5_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8032,c_8917])).

tff(c_10181,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8914,c_8920])).

tff(c_8944,plain,
    ( v1_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8914,c_8])).

tff(c_8965,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8944])).

tff(c_4470,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != '#skF_4'
      | A_18 = '#skF_4'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_24])).

tff(c_8972,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8965,c_4470])).

tff(c_9035,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8972])).

tff(c_8961,plain,(
    v5_relat_1(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8914,c_38])).

tff(c_8984,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8961,c_50])).

tff(c_8987,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8965,c_8984])).

tff(c_9721,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_9035,c_8987])).

tff(c_10182,plain,(
    ~ v2_funct_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_9721])).

tff(c_10197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7959,c_10182])).

tff(c_10198,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8972])).

tff(c_4471,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != '#skF_4'
      | A_18 = '#skF_4'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_4465,c_26])).

tff(c_8973,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8965,c_4471])).

tff(c_9033,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8973])).

tff(c_10219,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10198,c_9033])).

tff(c_10230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_10219])).

tff(c_10231,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8973])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_12,B_14)),k1_relat_1(A_12))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10260,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10231,c_20])).

tff(c_10270,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_250,c_4474,c_10260])).

tff(c_7765,plain,(
    ! [B_662,A_663] :
      ( r1_tarski(k1_relat_1(B_662),A_663)
      | ~ v4_relat_1(B_662,A_663)
      | ~ v1_relat_1(B_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10301,plain,(
    ! [B_844,A_845] :
      ( k1_relat_1(B_844) = A_845
      | ~ r1_tarski(A_845,k1_relat_1(B_844))
      | ~ v4_relat_1(B_844,A_845)
      | ~ v1_relat_1(B_844) ) ),
    inference(resolution,[status(thm)],[c_7765,c_2])).

tff(c_10304,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10270,c_10301])).

tff(c_10352,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_7672,c_10304])).

tff(c_10354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4467,c_10352])).

tff(c_10355,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_112,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_80])).

tff(c_10364,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10355,c_112])).

tff(c_10368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_10364])).

tff(c_10369,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10444,plain,(
    ! [B_852,A_853] :
      ( v1_relat_1(B_852)
      | ~ m1_subset_1(B_852,k1_zfmisc_1(A_853))
      | ~ v1_relat_1(A_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10456,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_10444])).

tff(c_10468,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10456])).

tff(c_10701,plain,(
    ! [C_884,B_885,A_886] :
      ( v5_relat_1(C_884,B_885)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_886,B_885))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10719,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_10701])).

tff(c_10453,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_10444])).

tff(c_10465,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10453])).

tff(c_11259,plain,(
    ! [E_950,C_951,D_949,F_948,B_947,A_946] :
      ( k1_partfun1(A_946,B_947,C_951,D_949,E_950,F_948) = k5_relat_1(E_950,F_948)
      | ~ m1_subset_1(F_948,k1_zfmisc_1(k2_zfmisc_1(C_951,D_949)))
      | ~ v1_funct_1(F_948)
      | ~ m1_subset_1(E_950,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947)))
      | ~ v1_funct_1(E_950) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_11267,plain,(
    ! [A_946,B_947,E_950] :
      ( k1_partfun1(A_946,B_947,'#skF_2','#skF_1',E_950,'#skF_4') = k5_relat_1(E_950,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_950,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947)))
      | ~ v1_funct_1(E_950) ) ),
    inference(resolution,[status(thm)],[c_68,c_11259])).

tff(c_11655,plain,(
    ! [A_989,B_990,E_991] :
      ( k1_partfun1(A_989,B_990,'#skF_2','#skF_1',E_991,'#skF_4') = k5_relat_1(E_991,'#skF_4')
      | ~ m1_subset_1(E_991,k1_zfmisc_1(k2_zfmisc_1(A_989,B_990)))
      | ~ v1_funct_1(E_991) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11267])).

tff(c_11673,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_11655])).

tff(c_11688,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11673])).

tff(c_12039,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11688,c_52])).

tff(c_12046,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_12039])).

tff(c_10994,plain,(
    ! [D_914,C_915,A_916,B_917] :
      ( D_914 = C_915
      | ~ r2_relset_1(A_916,B_917,C_915,D_914)
      | ~ m1_subset_1(D_914,k1_zfmisc_1(k2_zfmisc_1(A_916,B_917)))
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1(A_916,B_917))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11008,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_10994])).

tff(c_11031,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_11008])).

tff(c_11091,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11031])).

tff(c_12122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12046,c_11688,c_11091])).

tff(c_12123,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11031])).

tff(c_12355,plain,(
    ! [E_1034,C_1035,D_1033,B_1031,F_1032,A_1030] :
      ( k1_partfun1(A_1030,B_1031,C_1035,D_1033,E_1034,F_1032) = k5_relat_1(E_1034,F_1032)
      | ~ m1_subset_1(F_1032,k1_zfmisc_1(k2_zfmisc_1(C_1035,D_1033)))
      | ~ v1_funct_1(F_1032)
      | ~ m1_subset_1(E_1034,k1_zfmisc_1(k2_zfmisc_1(A_1030,B_1031)))
      | ~ v1_funct_1(E_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12363,plain,(
    ! [A_1030,B_1031,E_1034] :
      ( k1_partfun1(A_1030,B_1031,'#skF_2','#skF_1',E_1034,'#skF_4') = k5_relat_1(E_1034,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1034,k1_zfmisc_1(k2_zfmisc_1(A_1030,B_1031)))
      | ~ v1_funct_1(E_1034) ) ),
    inference(resolution,[status(thm)],[c_68,c_12355])).

tff(c_12757,plain,(
    ! [A_1075,B_1076,E_1077] :
      ( k1_partfun1(A_1075,B_1076,'#skF_2','#skF_1',E_1077,'#skF_4') = k5_relat_1(E_1077,'#skF_4')
      | ~ m1_subset_1(E_1077,k1_zfmisc_1(k2_zfmisc_1(A_1075,B_1076)))
      | ~ v1_funct_1(E_1077) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12363])).

tff(c_12775,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_12757])).

tff(c_12790,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12123,c_12775])).

tff(c_12800,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12790,c_22])).

tff(c_12806,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10465,c_10468,c_82,c_12800])).

tff(c_12825,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12806,c_2])).

tff(c_12916,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12825])).

tff(c_12922,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_12916])).

tff(c_12927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10468,c_10719,c_12922])).

tff(c_12928,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12825])).

tff(c_10490,plain,(
    ! [B_854,A_855] :
      ( v5_relat_1(B_854,A_855)
      | ~ r1_tarski(k2_relat_1(B_854),A_855)
      | ~ v1_relat_1(B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10505,plain,(
    ! [B_854] :
      ( v5_relat_1(B_854,k2_relat_1(B_854))
      | ~ v1_relat_1(B_854) ) ),
    inference(resolution,[status(thm)],[c_6,c_10490])).

tff(c_10734,plain,(
    ! [B_889] :
      ( v2_funct_2(B_889,k2_relat_1(B_889))
      | ~ v5_relat_1(B_889,k2_relat_1(B_889))
      | ~ v1_relat_1(B_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10765,plain,(
    ! [B_854] :
      ( v2_funct_2(B_854,k2_relat_1(B_854))
      | ~ v1_relat_1(B_854) ) ),
    inference(resolution,[status(thm)],[c_10505,c_10734])).

tff(c_13002,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12928,c_10765])).

tff(c_13018,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10468,c_13002])).

tff(c_13020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10369,c_13018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.07/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.32  
% 9.30/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.32  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.30/3.32  
% 9.30/3.32  %Foreground sorts:
% 9.30/3.32  
% 9.30/3.32  
% 9.30/3.32  %Background operators:
% 9.30/3.32  
% 9.30/3.32  
% 9.30/3.32  %Foreground operators:
% 9.30/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.30/3.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.30/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.30/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.30/3.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.30/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.30/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.30/3.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.30/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.30/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.30/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.30/3.32  tff('#skF_1', type, '#skF_1': $i).
% 9.30/3.32  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.30/3.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.30/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.30/3.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.30/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.30/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.30/3.32  tff('#skF_4', type, '#skF_4': $i).
% 9.30/3.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.30/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.30/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.30/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.30/3.32  
% 9.50/3.35  tff(f_173, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 9.50/3.35  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.50/3.35  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.50/3.35  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.50/3.35  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.50/3.35  tff(f_99, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.50/3.35  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.50/3.35  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.50/3.35  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.50/3.35  tff(f_153, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 9.50/3.35  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.50/3.35  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.50/3.35  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.50/3.35  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 9.50/3.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.50/3.35  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.50/3.35  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.50/3.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.50/3.35  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.50/3.35  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.50/3.35  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_149, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 9.50/3.35  tff(c_58, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.50/3.35  tff(c_36, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.50/3.35  tff(c_80, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 9.50/3.35  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_1021, plain, (![C_162, D_160, F_159, A_157, B_158, E_161]: (k1_partfun1(A_157, B_158, C_162, D_160, E_161, F_159)=k5_relat_1(E_161, F_159) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(C_162, D_160))) | ~v1_funct_1(F_159) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_1(E_161))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.35  tff(c_1029, plain, (![A_157, B_158, E_161]: (k1_partfun1(A_157, B_158, '#skF_2', '#skF_1', E_161, '#skF_4')=k5_relat_1(E_161, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_1(E_161))), inference(resolution, [status(thm)], [c_68, c_1021])).
% 9.50/3.35  tff(c_1258, plain, (![A_190, B_191, E_192]: (k1_partfun1(A_190, B_191, '#skF_2', '#skF_1', E_192, '#skF_4')=k5_relat_1(E_192, '#skF_4') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_192))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1029])).
% 9.50/3.35  tff(c_1270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1258])).
% 9.50/3.35  tff(c_1279, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1270])).
% 9.50/3.35  tff(c_52, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.50/3.35  tff(c_1288, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1279, c_52])).
% 9.50/3.35  tff(c_1292, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1288])).
% 9.50/3.35  tff(c_46, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.50/3.35  tff(c_79, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46])).
% 9.50/3.35  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_802, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r2_relset_1(A_131, B_132, C_130, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.50/3.35  tff(c_816, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_802])).
% 9.50/3.35  tff(c_839, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_816])).
% 9.50/3.35  tff(c_1919, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1279, c_1279, c_839])).
% 9.50/3.35  tff(c_28, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.50/3.35  tff(c_83, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 9.50/3.35  tff(c_34, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.50/3.35  tff(c_81, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 9.50/3.35  tff(c_154, plain, (![A_60]: (k1_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.50/3.35  tff(c_163, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))!=k1_xboole_0 | k6_partfun1(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_154])).
% 9.50/3.35  tff(c_170, plain, (![A_20]: (k1_xboole_0!=A_20 | k6_partfun1(A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_163])).
% 9.50/3.35  tff(c_225, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_170, c_66])).
% 9.50/3.35  tff(c_284, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_225])).
% 9.50/3.35  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.50/3.35  tff(c_1437, plain, (![B_199, E_200, C_198, A_201, D_197]: (k1_xboole_0=C_198 | v2_funct_1(D_197) | ~v2_funct_1(k1_partfun1(A_201, B_199, B_199, C_198, D_197, E_200)) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(B_199, C_198))) | ~v1_funct_2(E_200, B_199, C_198) | ~v1_funct_1(E_200) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_2(D_197, A_201, B_199) | ~v1_funct_1(D_197))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.50/3.35  tff(c_1439, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1279, c_1437])).
% 9.50/3.35  tff(c_1441, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_1439])).
% 9.50/3.35  tff(c_1442, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_149, c_284, c_1441])).
% 9.50/3.35  tff(c_1922, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1442])).
% 9.50/3.35  tff(c_1935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1922])).
% 9.50/3.35  tff(c_1937, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_225])).
% 9.50/3.35  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.50/3.35  tff(c_226, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.50/3.35  tff(c_238, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_226])).
% 9.50/3.35  tff(c_250, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_238])).
% 9.50/3.35  tff(c_24, plain, (![A_18]: (k2_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.50/3.35  tff(c_265, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_250, c_24])).
% 9.50/3.35  tff(c_283, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_265])).
% 9.50/3.35  tff(c_1953, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_283])).
% 9.50/3.35  tff(c_2173, plain, (![C_237, B_238, A_239]: (v5_relat_1(C_237, B_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.50/3.35  tff(c_2191, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_2173])).
% 9.50/3.35  tff(c_235, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_226])).
% 9.50/3.35  tff(c_247, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_235])).
% 9.50/3.35  tff(c_93, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.50/3.35  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.50/3.35  tff(c_99, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_32])).
% 9.50/3.35  tff(c_30, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.50/3.35  tff(c_129, plain, (![A_58]: (k2_relat_1(k6_partfun1(A_58))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30])).
% 9.50/3.35  tff(c_138, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_129])).
% 9.50/3.35  tff(c_1944, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1937, c_138])).
% 9.50/3.35  tff(c_1940, plain, (![A_20]: (A_20!='#skF_1' | k6_partfun1(A_20)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1937, c_170])).
% 9.50/3.35  tff(c_82, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30])).
% 9.50/3.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.50/3.35  tff(c_2015, plain, (![B_220, A_221]: (v5_relat_1(B_220, A_221) | ~r1_tarski(k2_relat_1(B_220), A_221) | ~v1_relat_1(B_220))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.50/3.35  tff(c_2075, plain, (![B_225]: (v5_relat_1(B_225, k2_relat_1(B_225)) | ~v1_relat_1(B_225))), inference(resolution, [status(thm)], [c_6, c_2015])).
% 9.50/3.35  tff(c_2081, plain, (![A_19]: (v5_relat_1(k6_partfun1(A_19), A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2075])).
% 9.50/3.35  tff(c_2085, plain, (![A_19]: (v5_relat_1(k6_partfun1(A_19), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2081])).
% 9.50/3.35  tff(c_2208, plain, (![B_241]: (v2_funct_2(B_241, k2_relat_1(B_241)) | ~v5_relat_1(B_241, k2_relat_1(B_241)) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.50/3.35  tff(c_2225, plain, (![A_19]: (v2_funct_2(k6_partfun1(A_19), k2_relat_1(k6_partfun1(A_19))) | ~v5_relat_1(k6_partfun1(A_19), A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2208])).
% 9.50/3.35  tff(c_2239, plain, (![A_242]: (v2_funct_2(k6_partfun1(A_242), A_242))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2085, c_82, c_2225])).
% 9.50/3.35  tff(c_2243, plain, (v2_funct_2('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1940, c_2239])).
% 9.50/3.35  tff(c_2739, plain, (![D_301, E_302, C_303, A_298, B_299, F_300]: (k1_partfun1(A_298, B_299, C_303, D_301, E_302, F_300)=k5_relat_1(E_302, F_300) | ~m1_subset_1(F_300, k1_zfmisc_1(k2_zfmisc_1(C_303, D_301))) | ~v1_funct_1(F_300) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))) | ~v1_funct_1(E_302))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.35  tff(c_2747, plain, (![A_298, B_299, E_302]: (k1_partfun1(A_298, B_299, '#skF_2', '#skF_1', E_302, '#skF_4')=k5_relat_1(E_302, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))) | ~v1_funct_1(E_302))), inference(resolution, [status(thm)], [c_68, c_2739])).
% 9.50/3.35  tff(c_2911, plain, (![A_325, B_326, E_327]: (k1_partfun1(A_325, B_326, '#skF_2', '#skF_1', E_327, '#skF_4')=k5_relat_1(E_327, '#skF_4') | ~m1_subset_1(E_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~v1_funct_1(E_327))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2747])).
% 9.50/3.35  tff(c_2923, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2911])).
% 9.50/3.35  tff(c_2932, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2923])).
% 9.50/3.35  tff(c_2997, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2932, c_52])).
% 9.50/3.35  tff(c_3001, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_2997])).
% 9.50/3.35  tff(c_190, plain, (![A_62]: (k1_xboole_0!=A_62 | k6_partfun1(A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_163])).
% 9.50/3.35  tff(c_196, plain, (![A_62]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))) | k1_xboole_0!=A_62)), inference(superposition, [status(thm), theory('equality')], [c_190, c_79])).
% 9.50/3.35  tff(c_2439, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1937, c_196])).
% 9.50/3.35  tff(c_1936, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_225])).
% 9.50/3.35  tff(c_1980, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1936])).
% 9.50/3.35  tff(c_2993, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2932, c_1980])).
% 9.50/3.35  tff(c_44, plain, (![D_27, C_26, A_24, B_25]: (D_27=C_26 | ~r2_relset_1(A_24, B_25, C_26, D_27) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.50/3.35  tff(c_3004, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_2993, c_44])).
% 9.50/3.35  tff(c_3007, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_1' | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2439, c_3004])).
% 9.50/3.35  tff(c_4303, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3001, c_3007])).
% 9.50/3.35  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.50/3.35  tff(c_3033, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3001, c_8])).
% 9.50/3.35  tff(c_3054, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3033])).
% 9.50/3.35  tff(c_1941, plain, (![A_18]: (k2_relat_1(A_18)!='#skF_1' | A_18='#skF_1' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1937, c_24])).
% 9.50/3.35  tff(c_3061, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1' | k5_relat_1('#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_3054, c_1941])).
% 9.50/3.35  tff(c_3196, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_3061])).
% 9.50/3.35  tff(c_38, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.50/3.35  tff(c_3050, plain, (v5_relat_1(k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_3001, c_38])).
% 9.50/3.35  tff(c_50, plain, (![B_30, A_29]: (k2_relat_1(B_30)=A_29 | ~v2_funct_2(B_30, A_29) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.50/3.35  tff(c_3065, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_1' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_1') | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_3050, c_50])).
% 9.50/3.35  tff(c_3068, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_1' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_3065])).
% 9.50/3.35  tff(c_3822, plain, (~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3196, c_3068])).
% 9.50/3.35  tff(c_4304, plain, (~v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4303, c_3822])).
% 9.50/3.35  tff(c_4319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2243, c_4304])).
% 9.50/3.35  tff(c_4320, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_3061])).
% 9.50/3.35  tff(c_22, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, B_17)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.50/3.35  tff(c_4342, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4320, c_22])).
% 9.50/3.35  tff(c_4348, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_250, c_1944, c_4342])).
% 9.50/3.35  tff(c_268, plain, (![B_67, A_68]: (r1_tarski(k2_relat_1(B_67), A_68) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.50/3.35  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.50/3.35  tff(c_4419, plain, (![B_412, A_413]: (k2_relat_1(B_412)=A_413 | ~r1_tarski(A_413, k2_relat_1(B_412)) | ~v5_relat_1(B_412, A_413) | ~v1_relat_1(B_412))), inference(resolution, [status(thm)], [c_268, c_2])).
% 9.50/3.35  tff(c_4422, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4348, c_4419])).
% 9.50/3.35  tff(c_4462, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_2191, c_4422])).
% 9.50/3.35  tff(c_4464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1953, c_4462])).
% 9.50/3.35  tff(c_4465, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_265])).
% 9.50/3.35  tff(c_26, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.50/3.35  tff(c_258, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_247, c_26])).
% 9.50/3.35  tff(c_282, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_258])).
% 9.50/3.35  tff(c_4467, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_282])).
% 9.50/3.35  tff(c_4493, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_4') | '#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_225])).
% 9.50/3.35  tff(c_4494, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_4493])).
% 9.50/3.35  tff(c_4873, plain, (![C_449, B_450, A_451]: (v5_relat_1(C_449, B_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.50/3.35  tff(c_4890, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_4873])).
% 9.50/3.35  tff(c_4466, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_265])).
% 9.50/3.35  tff(c_4483, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4466])).
% 9.50/3.35  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.50/3.35  tff(c_4487, plain, (![A_8]: (r1_tarski('#skF_4', A_8) | ~v5_relat_1('#skF_4', A_8) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4483, c_16])).
% 9.50/3.35  tff(c_4491, plain, (![A_8]: (r1_tarski('#skF_4', A_8) | ~v5_relat_1('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_4487])).
% 9.50/3.35  tff(c_4897, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4890, c_4491])).
% 9.50/3.35  tff(c_4899, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_4897, c_2])).
% 9.50/3.35  tff(c_4902, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4494, c_4899])).
% 9.50/3.35  tff(c_5803, plain, (![D_519, C_520, A_521, B_522]: (D_519=C_520 | ~r2_relset_1(A_521, B_522, C_520, D_519) | ~m1_subset_1(D_519, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.50/3.35  tff(c_5817, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_5803])).
% 9.50/3.35  tff(c_5840, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_5817])).
% 9.50/3.35  tff(c_5905, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5840])).
% 9.50/3.35  tff(c_6673, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_5905])).
% 9.50/3.35  tff(c_6677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_6673])).
% 9.50/3.36  tff(c_6678, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5840])).
% 9.50/3.36  tff(c_7155, plain, (![E_616, F_614, B_613, D_615, C_617, A_612]: (k1_partfun1(A_612, B_613, C_617, D_615, E_616, F_614)=k5_relat_1(E_616, F_614) | ~m1_subset_1(F_614, k1_zfmisc_1(k2_zfmisc_1(C_617, D_615))) | ~v1_funct_1(F_614) | ~m1_subset_1(E_616, k1_zfmisc_1(k2_zfmisc_1(A_612, B_613))) | ~v1_funct_1(E_616))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.36  tff(c_7163, plain, (![A_612, B_613, E_616]: (k1_partfun1(A_612, B_613, '#skF_2', '#skF_1', E_616, '#skF_4')=k5_relat_1(E_616, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_616, k1_zfmisc_1(k2_zfmisc_1(A_612, B_613))) | ~v1_funct_1(E_616))), inference(resolution, [status(thm)], [c_68, c_7155])).
% 9.50/3.36  tff(c_7494, plain, (![A_641, B_642, E_643]: (k1_partfun1(A_641, B_642, '#skF_2', '#skF_1', E_643, '#skF_4')=k5_relat_1(E_643, '#skF_4') | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~v1_funct_1(E_643))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7163])).
% 9.50/3.36  tff(c_7506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_7494])).
% 9.50/3.36  tff(c_7517, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6678, c_7506])).
% 9.50/3.36  tff(c_5632, plain, (![A_501, B_502]: (r1_tarski(k2_relat_1(k5_relat_1(A_501, B_502)), k2_relat_1(B_502)) | ~v1_relat_1(B_502) | ~v1_relat_1(A_501))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.50/3.36  tff(c_5647, plain, (![A_501]: (r1_tarski(k2_relat_1(k5_relat_1(A_501, '#skF_4')), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_501))), inference(superposition, [status(thm), theory('equality')], [c_4483, c_5632])).
% 9.50/3.36  tff(c_5657, plain, (![A_501]: (r1_tarski(k2_relat_1(k5_relat_1(A_501, '#skF_4')), '#skF_4') | ~v1_relat_1(A_501))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_5647])).
% 9.50/3.36  tff(c_7530, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), '#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7517, c_5657])).
% 9.50/3.36  tff(c_7544, plain, (r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_82, c_7530])).
% 9.50/3.36  tff(c_7546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4902, c_7544])).
% 9.50/3.36  tff(c_7548, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_4493])).
% 9.50/3.36  tff(c_7550, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_74])).
% 9.50/3.36  tff(c_40, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.50/3.36  tff(c_7672, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7550, c_40])).
% 9.50/3.36  tff(c_117, plain, (![A_57]: (k1_relat_1(k6_partfun1(A_57))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 9.50/3.36  tff(c_126, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_117])).
% 9.50/3.36  tff(c_4474, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_126])).
% 9.50/3.36  tff(c_4469, plain, (![A_20]: (A_20!='#skF_4' | k6_partfun1(A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_170])).
% 9.50/3.36  tff(c_7699, plain, (![B_654, A_655]: (v5_relat_1(B_654, A_655) | ~r1_tarski(k2_relat_1(B_654), A_655) | ~v1_relat_1(B_654))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.50/3.36  tff(c_7708, plain, (![A_19, A_655]: (v5_relat_1(k6_partfun1(A_19), A_655) | ~r1_tarski(A_19, A_655) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_7699])).
% 9.50/3.36  tff(c_7717, plain, (![A_19, A_655]: (v5_relat_1(k6_partfun1(A_19), A_655) | ~r1_tarski(A_19, A_655))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_7708])).
% 9.50/3.36  tff(c_7898, plain, (![B_677]: (v2_funct_2(B_677, k2_relat_1(B_677)) | ~v5_relat_1(B_677, k2_relat_1(B_677)) | ~v1_relat_1(B_677))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.50/3.36  tff(c_7902, plain, (![A_19]: (v2_funct_2(k6_partfun1(A_19), k2_relat_1(k6_partfun1(A_19))) | ~v1_relat_1(k6_partfun1(A_19)) | ~r1_tarski(A_19, k2_relat_1(k6_partfun1(A_19))))), inference(resolution, [status(thm)], [c_7717, c_7898])).
% 9.50/3.36  tff(c_7936, plain, (![A_678]: (v2_funct_2(k6_partfun1(A_678), A_678))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82, c_81, c_82, c_7902])).
% 9.50/3.36  tff(c_7959, plain, (v2_funct_2('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4469, c_7936])).
% 9.50/3.36  tff(c_7551, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_68])).
% 9.50/3.36  tff(c_8595, plain, (![A_741, C_746, E_745, D_744, F_743, B_742]: (k1_partfun1(A_741, B_742, C_746, D_744, E_745, F_743)=k5_relat_1(E_745, F_743) | ~m1_subset_1(F_743, k1_zfmisc_1(k2_zfmisc_1(C_746, D_744))) | ~v1_funct_1(F_743) | ~m1_subset_1(E_745, k1_zfmisc_1(k2_zfmisc_1(A_741, B_742))) | ~v1_funct_1(E_745))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.36  tff(c_8599, plain, (![A_741, B_742, E_745]: (k1_partfun1(A_741, B_742, '#skF_2', '#skF_4', E_745, '#skF_4')=k5_relat_1(E_745, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_745, k1_zfmisc_1(k2_zfmisc_1(A_741, B_742))) | ~v1_funct_1(E_745))), inference(resolution, [status(thm)], [c_7551, c_8595])).
% 9.50/3.36  tff(c_8800, plain, (![A_770, B_771, E_772]: (k1_partfun1(A_770, B_771, '#skF_2', '#skF_4', E_772, '#skF_4')=k5_relat_1(E_772, '#skF_4') | ~m1_subset_1(E_772, k1_zfmisc_1(k2_zfmisc_1(A_770, B_771))) | ~v1_funct_1(E_772))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8599])).
% 9.50/3.36  tff(c_8812, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7550, c_8800])).
% 9.50/3.36  tff(c_8825, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8812])).
% 9.50/3.36  tff(c_8910, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8825, c_52])).
% 9.50/3.36  tff(c_8914, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7550, c_72, c_7551, c_8910])).
% 9.50/3.36  tff(c_8032, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_196])).
% 9.50/3.36  tff(c_4551, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_170])).
% 9.50/3.36  tff(c_7549, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_7548, c_7548, c_7548, c_7548, c_66])).
% 9.50/3.36  tff(c_7746, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4551, c_7549])).
% 9.50/3.36  tff(c_8906, plain, (r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8825, c_7746])).
% 9.50/3.36  tff(c_8917, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_8906, c_44])).
% 9.50/3.36  tff(c_8920, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8032, c_8917])).
% 9.50/3.36  tff(c_10181, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8914, c_8920])).
% 9.50/3.36  tff(c_8944, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_8914, c_8])).
% 9.50/3.36  tff(c_8965, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8944])).
% 9.50/3.36  tff(c_4470, plain, (![A_18]: (k2_relat_1(A_18)!='#skF_4' | A_18='#skF_4' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_24])).
% 9.50/3.36  tff(c_8972, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4' | k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8965, c_4470])).
% 9.50/3.36  tff(c_9035, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8972])).
% 9.50/3.36  tff(c_8961, plain, (v5_relat_1(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8914, c_38])).
% 9.50/3.36  tff(c_8984, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8961, c_50])).
% 9.50/3.36  tff(c_8987, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8965, c_8984])).
% 9.50/3.36  tff(c_9721, plain, (~v2_funct_2(k5_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_9035, c_8987])).
% 9.50/3.36  tff(c_10182, plain, (~v2_funct_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_9721])).
% 9.50/3.36  tff(c_10197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7959, c_10182])).
% 9.50/3.36  tff(c_10198, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_8972])).
% 9.50/3.36  tff(c_4471, plain, (![A_18]: (k1_relat_1(A_18)!='#skF_4' | A_18='#skF_4' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_4465, c_26])).
% 9.50/3.36  tff(c_8973, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4' | k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8965, c_4471])).
% 9.50/3.36  tff(c_9033, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8973])).
% 9.50/3.36  tff(c_10219, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10198, c_9033])).
% 9.50/3.36  tff(c_10230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4474, c_10219])).
% 9.50/3.36  tff(c_10231, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_8973])).
% 9.50/3.36  tff(c_20, plain, (![A_12, B_14]: (r1_tarski(k1_relat_1(k5_relat_1(A_12, B_14)), k1_relat_1(A_12)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.50/3.36  tff(c_10260, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10231, c_20])).
% 9.50/3.36  tff(c_10270, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_250, c_4474, c_10260])).
% 9.50/3.36  tff(c_7765, plain, (![B_662, A_663]: (r1_tarski(k1_relat_1(B_662), A_663) | ~v4_relat_1(B_662, A_663) | ~v1_relat_1(B_662))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.50/3.36  tff(c_10301, plain, (![B_844, A_845]: (k1_relat_1(B_844)=A_845 | ~r1_tarski(A_845, k1_relat_1(B_844)) | ~v4_relat_1(B_844, A_845) | ~v1_relat_1(B_844))), inference(resolution, [status(thm)], [c_7765, c_2])).
% 9.50/3.36  tff(c_10304, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10270, c_10301])).
% 9.50/3.36  tff(c_10352, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_7672, c_10304])).
% 9.50/3.36  tff(c_10354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4467, c_10352])).
% 9.50/3.36  tff(c_10355, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_258])).
% 9.50/3.36  tff(c_112, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_80])).
% 9.50/3.36  tff(c_10364, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10355, c_112])).
% 9.50/3.36  tff(c_10368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_10364])).
% 9.50/3.36  tff(c_10369, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 9.50/3.36  tff(c_10444, plain, (![B_852, A_853]: (v1_relat_1(B_852) | ~m1_subset_1(B_852, k1_zfmisc_1(A_853)) | ~v1_relat_1(A_853))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.50/3.36  tff(c_10456, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_10444])).
% 9.50/3.36  tff(c_10468, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10456])).
% 9.50/3.36  tff(c_10701, plain, (![C_884, B_885, A_886]: (v5_relat_1(C_884, B_885) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_886, B_885))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.50/3.36  tff(c_10719, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_10701])).
% 9.50/3.36  tff(c_10453, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_10444])).
% 9.50/3.36  tff(c_10465, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10453])).
% 9.50/3.36  tff(c_11259, plain, (![E_950, C_951, D_949, F_948, B_947, A_946]: (k1_partfun1(A_946, B_947, C_951, D_949, E_950, F_948)=k5_relat_1(E_950, F_948) | ~m1_subset_1(F_948, k1_zfmisc_1(k2_zfmisc_1(C_951, D_949))) | ~v1_funct_1(F_948) | ~m1_subset_1(E_950, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))) | ~v1_funct_1(E_950))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.36  tff(c_11267, plain, (![A_946, B_947, E_950]: (k1_partfun1(A_946, B_947, '#skF_2', '#skF_1', E_950, '#skF_4')=k5_relat_1(E_950, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_950, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))) | ~v1_funct_1(E_950))), inference(resolution, [status(thm)], [c_68, c_11259])).
% 9.50/3.36  tff(c_11655, plain, (![A_989, B_990, E_991]: (k1_partfun1(A_989, B_990, '#skF_2', '#skF_1', E_991, '#skF_4')=k5_relat_1(E_991, '#skF_4') | ~m1_subset_1(E_991, k1_zfmisc_1(k2_zfmisc_1(A_989, B_990))) | ~v1_funct_1(E_991))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11267])).
% 9.50/3.36  tff(c_11673, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_11655])).
% 9.50/3.36  tff(c_11688, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11673])).
% 9.50/3.36  tff(c_12039, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11688, c_52])).
% 9.50/3.36  tff(c_12046, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_12039])).
% 9.50/3.36  tff(c_10994, plain, (![D_914, C_915, A_916, B_917]: (D_914=C_915 | ~r2_relset_1(A_916, B_917, C_915, D_914) | ~m1_subset_1(D_914, k1_zfmisc_1(k2_zfmisc_1(A_916, B_917))) | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1(A_916, B_917))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.50/3.36  tff(c_11008, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_10994])).
% 9.50/3.36  tff(c_11031, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_11008])).
% 9.50/3.36  tff(c_11091, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11031])).
% 9.50/3.36  tff(c_12122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12046, c_11688, c_11091])).
% 9.50/3.36  tff(c_12123, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_11031])).
% 9.50/3.36  tff(c_12355, plain, (![E_1034, C_1035, D_1033, B_1031, F_1032, A_1030]: (k1_partfun1(A_1030, B_1031, C_1035, D_1033, E_1034, F_1032)=k5_relat_1(E_1034, F_1032) | ~m1_subset_1(F_1032, k1_zfmisc_1(k2_zfmisc_1(C_1035, D_1033))) | ~v1_funct_1(F_1032) | ~m1_subset_1(E_1034, k1_zfmisc_1(k2_zfmisc_1(A_1030, B_1031))) | ~v1_funct_1(E_1034))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.50/3.36  tff(c_12363, plain, (![A_1030, B_1031, E_1034]: (k1_partfun1(A_1030, B_1031, '#skF_2', '#skF_1', E_1034, '#skF_4')=k5_relat_1(E_1034, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1034, k1_zfmisc_1(k2_zfmisc_1(A_1030, B_1031))) | ~v1_funct_1(E_1034))), inference(resolution, [status(thm)], [c_68, c_12355])).
% 9.50/3.36  tff(c_12757, plain, (![A_1075, B_1076, E_1077]: (k1_partfun1(A_1075, B_1076, '#skF_2', '#skF_1', E_1077, '#skF_4')=k5_relat_1(E_1077, '#skF_4') | ~m1_subset_1(E_1077, k1_zfmisc_1(k2_zfmisc_1(A_1075, B_1076))) | ~v1_funct_1(E_1077))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12363])).
% 9.50/3.36  tff(c_12775, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_12757])).
% 9.50/3.36  tff(c_12790, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12123, c_12775])).
% 9.50/3.36  tff(c_12800, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12790, c_22])).
% 9.50/3.36  tff(c_12806, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10465, c_10468, c_82, c_12800])).
% 9.50/3.36  tff(c_12825, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_12806, c_2])).
% 9.50/3.36  tff(c_12916, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_12825])).
% 9.50/3.36  tff(c_12922, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_12916])).
% 9.50/3.36  tff(c_12927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10468, c_10719, c_12922])).
% 9.50/3.36  tff(c_12928, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12825])).
% 9.50/3.36  tff(c_10490, plain, (![B_854, A_855]: (v5_relat_1(B_854, A_855) | ~r1_tarski(k2_relat_1(B_854), A_855) | ~v1_relat_1(B_854))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.50/3.36  tff(c_10505, plain, (![B_854]: (v5_relat_1(B_854, k2_relat_1(B_854)) | ~v1_relat_1(B_854))), inference(resolution, [status(thm)], [c_6, c_10490])).
% 9.50/3.36  tff(c_10734, plain, (![B_889]: (v2_funct_2(B_889, k2_relat_1(B_889)) | ~v5_relat_1(B_889, k2_relat_1(B_889)) | ~v1_relat_1(B_889))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.50/3.36  tff(c_10765, plain, (![B_854]: (v2_funct_2(B_854, k2_relat_1(B_854)) | ~v1_relat_1(B_854))), inference(resolution, [status(thm)], [c_10505, c_10734])).
% 9.50/3.36  tff(c_13002, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12928, c_10765])).
% 9.50/3.36  tff(c_13018, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10468, c_13002])).
% 9.50/3.36  tff(c_13020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10369, c_13018])).
% 9.50/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.50/3.36  
% 9.50/3.36  Inference rules
% 9.50/3.36  ----------------------
% 9.50/3.36  #Ref     : 6
% 9.50/3.36  #Sup     : 2647
% 9.50/3.36  #Fact    : 0
% 9.50/3.36  #Define  : 0
% 9.50/3.36  #Split   : 63
% 9.50/3.36  #Chain   : 0
% 9.50/3.36  #Close   : 0
% 9.50/3.36  
% 9.50/3.36  Ordering : KBO
% 9.50/3.36  
% 9.50/3.36  Simplification rules
% 9.50/3.36  ----------------------
% 9.50/3.36  #Subsume      : 667
% 9.50/3.36  #Demod        : 2376
% 9.50/3.36  #Tautology    : 746
% 9.50/3.36  #SimpNegUnit  : 75
% 9.50/3.36  #BackRed      : 144
% 9.50/3.36  
% 9.50/3.36  #Partial instantiations: 0
% 9.50/3.36  #Strategies tried      : 1
% 9.50/3.36  
% 9.50/3.36  Timing (in seconds)
% 9.50/3.36  ----------------------
% 9.50/3.36  Preprocessing        : 0.35
% 9.50/3.36  Parsing              : 0.18
% 9.50/3.36  CNF conversion       : 0.03
% 9.50/3.36  Main loop            : 2.18
% 9.50/3.36  Inferencing          : 0.69
% 9.50/3.36  Reduction            : 0.85
% 9.50/3.36  Demodulation         : 0.61
% 9.50/3.36  BG Simplification    : 0.06
% 9.50/3.36  Subsumption          : 0.42
% 9.50/3.36  Abstraction          : 0.09
% 9.50/3.36  MUC search           : 0.00
% 9.50/3.36  Cooper               : 0.00
% 9.50/3.36  Total                : 2.63
% 9.50/3.36  Index Insertion      : 0.00
% 9.50/3.36  Index Deletion       : 0.00
% 9.50/3.36  Index Matching       : 0.00
% 9.50/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
