%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.25s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 421 expanded)
%              Number of leaves         :   52 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 (1249 expanded)
%              Number of equality atoms :   61 ( 142 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_153,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_103,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_151,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_141,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_175,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_101,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_149,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [B_81,A_82] :
      ( ~ r1_xboole_0(B_81,A_82)
      | ~ r1_tarski(B_81,A_82)
      | v1_xboole_0(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,(
    ! [A_85] :
      ( ~ r1_tarski(A_85,k1_xboole_0)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_10,c_205])).

tff(c_236,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( v1_xboole_0(k2_zfmisc_1(A_11,B_12))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_210,plain,(
    ! [B_83,A_84] :
      ( v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_225,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_210])).

tff(c_242,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_250,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_242])).

tff(c_66,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    ! [A_28] : v2_funct_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_87,plain,(
    ! [A_28] : v2_funct_1(k6_partfun1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1239,plain,(
    ! [D_162,C_163,E_164,A_161,F_165,B_160] :
      ( k1_partfun1(A_161,B_160,C_163,D_162,E_164,F_165) = k5_relat_1(E_164,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_163,D_162)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_1(E_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1249,plain,(
    ! [A_161,B_160,E_164] :
      ( k1_partfun1(A_161,B_160,'#skF_2','#skF_1',E_164,'#skF_4') = k5_relat_1(E_164,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_1(E_164) ) ),
    inference(resolution,[status(thm)],[c_76,c_1239])).

tff(c_4099,plain,(
    ! [A_277,B_278,E_279] :
      ( k1_partfun1(A_277,B_278,'#skF_2','#skF_1',E_279,'#skF_4') = k5_relat_1(E_279,'#skF_4')
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ v1_funct_1(E_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1249])).

tff(c_4129,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4099])).

tff(c_4140,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4129])).

tff(c_56,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4615,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4140,c_56])).

tff(c_4622,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_4615])).

tff(c_62,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_851,plain,(
    ! [D_131,C_132,A_133,B_134] :
      ( D_131 = C_132
      | ~ r2_relset_1(A_133,B_134,C_132,D_131)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_857,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_851])).

tff(c_868,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_857])).

tff(c_4739,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4622,c_4140,c_4140,c_868])).

tff(c_38,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_88,plain,(
    ! [A_27] : k2_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_28,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_266,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_272,plain,(
    ! [A_44] :
      ( v1_relat_1(k6_partfun1(A_44))
      | ~ v1_relat_1(k2_zfmisc_1(A_44,A_44)) ) ),
    inference(resolution,[status(thm)],[c_62,c_266])).

tff(c_329,plain,(
    ! [A_89] : v1_relat_1(k6_partfun1(A_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_272])).

tff(c_32,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_332,plain,(
    ! [A_89] :
      ( k2_relat_1(k6_partfun1(A_89)) != k1_xboole_0
      | k6_partfun1(A_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_329,c_32])).

tff(c_371,plain,(
    ! [A_94] :
      ( k1_xboole_0 != A_94
      | k6_partfun1(A_94) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_332])).

tff(c_382,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_74])).

tff(c_436,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_70,plain,(
    ! [D_55,B_53,E_57,A_52,C_54] :
      ( k1_xboole_0 = C_54
      | v2_funct_1(D_55)
      | ~ v2_funct_1(k1_partfun1(A_52,B_53,B_53,C_54,D_55,E_57))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ v1_funct_2(E_57,B_53,C_54)
      | ~ v1_funct_1(E_57)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(D_55,A_52,B_53)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4612,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4140,c_70])).

tff(c_4619,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_4612])).

tff(c_4620,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_436,c_4619])).

tff(c_4745,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4739,c_4620])).

tff(c_4755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_4745])).

tff(c_4757,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_4767,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_236])).

tff(c_4780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_4767])).

tff(c_4781,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(B_8)
      | B_8 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4789,plain,(
    ! [A_295] :
      ( A_295 = '#skF_3'
      | ~ v1_xboole_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_4781,c_14])).

tff(c_4808,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_236,c_4789])).

tff(c_119,plain,(
    ! [A_68] : k6_relat_1(A_68) = k6_partfun1(A_68) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_125,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_40])).

tff(c_145,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_87])).

tff(c_4820,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4808,c_145])).

tff(c_4827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_4820])).

tff(c_4828,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4932,plain,(
    ! [B_311,A_312] :
      ( v1_relat_1(B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(A_312))
      | ~ v1_relat_1(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4944,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_4932])).

tff(c_4956,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4944])).

tff(c_5083,plain,(
    ! [C_322,B_323,A_324] :
      ( v5_relat_1(C_322,B_323)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_324,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5099,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_5083])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4941,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_4932])).

tff(c_4953,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4941])).

tff(c_5883,plain,(
    ! [C_391,E_392,D_390,A_389,F_393,B_388] :
      ( k1_partfun1(A_389,B_388,C_391,D_390,E_392,F_393) = k5_relat_1(E_392,F_393)
      | ~ m1_subset_1(F_393,k1_zfmisc_1(k2_zfmisc_1(C_391,D_390)))
      | ~ v1_funct_1(F_393)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388)))
      | ~ v1_funct_1(E_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_5893,plain,(
    ! [A_389,B_388,E_392] :
      ( k1_partfun1(A_389,B_388,'#skF_2','#skF_1',E_392,'#skF_4') = k5_relat_1(E_392,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388)))
      | ~ v1_funct_1(E_392) ) ),
    inference(resolution,[status(thm)],[c_76,c_5883])).

tff(c_7508,plain,(
    ! [A_480,B_481,E_482] :
      ( k1_partfun1(A_480,B_481,'#skF_2','#skF_1',E_482,'#skF_4') = k5_relat_1(E_482,'#skF_4')
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481)))
      | ~ v1_funct_1(E_482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5893])).

tff(c_7535,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_7508])).

tff(c_7543,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_7535])).

tff(c_8629,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7543,c_56])).

tff(c_8636,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_8629])).

tff(c_5458,plain,(
    ! [D_357,C_358,A_359,B_360] :
      ( D_357 = C_358
      | ~ r2_relset_1(A_359,B_360,C_358,D_357)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360)))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5464,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_5458])).

tff(c_5475,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5464])).

tff(c_5542,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5475])).

tff(c_9210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8636,c_7543,c_5542])).

tff(c_9211,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5475])).

tff(c_9676,plain,(
    ! [B_541,F_546,C_544,D_543,E_545,A_542] :
      ( k1_partfun1(A_542,B_541,C_544,D_543,E_545,F_546) = k5_relat_1(E_545,F_546)
      | ~ m1_subset_1(F_546,k1_zfmisc_1(k2_zfmisc_1(C_544,D_543)))
      | ~ v1_funct_1(F_546)
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(A_542,B_541)))
      | ~ v1_funct_1(E_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_9686,plain,(
    ! [A_542,B_541,E_545] :
      ( k1_partfun1(A_542,B_541,'#skF_2','#skF_1',E_545,'#skF_4') = k5_relat_1(E_545,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(A_542,B_541)))
      | ~ v1_funct_1(E_545) ) ),
    inference(resolution,[status(thm)],[c_76,c_9676])).

tff(c_12494,plain,(
    ! [A_658,B_659,E_660] :
      ( k1_partfun1(A_658,B_659,'#skF_2','#skF_1',E_660,'#skF_4') = k5_relat_1(E_660,'#skF_4')
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659)))
      | ~ v1_funct_1(E_660) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9686])).

tff(c_12527,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_12494])).

tff(c_12541,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9211,c_12527])).

tff(c_30,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_23,B_25)),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12548,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12541,c_30])).

tff(c_12552,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4953,c_4956,c_88,c_12548])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12560,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12552,c_2])).

tff(c_12567,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12560])).

tff(c_12574,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_12567])).

tff(c_12579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_5099,c_12574])).

tff(c_12580,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12560])).

tff(c_5108,plain,(
    ! [B_327,A_328] :
      ( v5_relat_1(B_327,A_328)
      | ~ r1_tarski(k2_relat_1(B_327),A_328)
      | ~ v1_relat_1(B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5123,plain,(
    ! [B_327] :
      ( v5_relat_1(B_327,k2_relat_1(B_327))
      | ~ v1_relat_1(B_327) ) ),
    inference(resolution,[status(thm)],[c_6,c_5108])).

tff(c_5223,plain,(
    ! [B_337] :
      ( v2_funct_2(B_337,k2_relat_1(B_337))
      | ~ v5_relat_1(B_337,k2_relat_1(B_337))
      | ~ v1_relat_1(B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5237,plain,(
    ! [B_327] :
      ( v2_funct_2(B_327,k2_relat_1(B_327))
      | ~ v1_relat_1(B_327) ) ),
    inference(resolution,[status(thm)],[c_5123,c_5223])).

tff(c_12594,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12580,c_5237])).

tff(c_12612,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_12594])).

tff(c_12614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4828,c_12612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.40  
% 10.17/3.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.40  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.17/3.40  
% 10.17/3.40  %Foreground sorts:
% 10.17/3.40  
% 10.17/3.40  
% 10.17/3.40  %Background operators:
% 10.17/3.40  
% 10.17/3.40  
% 10.17/3.40  %Foreground operators:
% 10.17/3.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.17/3.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.17/3.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.17/3.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.17/3.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.17/3.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.17/3.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.17/3.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.17/3.40  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.17/3.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.17/3.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.17/3.40  tff('#skF_2', type, '#skF_2': $i).
% 10.17/3.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.17/3.40  tff('#skF_3', type, '#skF_3': $i).
% 10.17/3.40  tff('#skF_1', type, '#skF_1': $i).
% 10.17/3.40  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.17/3.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.17/3.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.17/3.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.17/3.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.17/3.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.17/3.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.17/3.40  tff('#skF_4', type, '#skF_4': $i).
% 10.17/3.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.17/3.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.17/3.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.17/3.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.17/3.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.17/3.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.17/3.40  
% 10.25/3.42  tff(f_195, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 10.25/3.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.25/3.42  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.25/3.42  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 10.25/3.42  tff(f_59, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 10.25/3.42  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.25/3.42  tff(f_153, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.25/3.42  tff(f_103, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 10.25/3.42  tff(f_151, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.25/3.42  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.25/3.42  tff(f_141, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.25/3.42  tff(f_117, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.25/3.42  tff(f_100, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.25/3.42  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.25/3.42  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.25/3.42  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.25/3.42  tff(f_175, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 10.25/3.42  tff(f_51, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 10.25/3.42  tff(f_101, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 10.25/3.42  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.25/3.42  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.25/3.42  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 10.25/3.42  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.25/3.42  tff(c_72, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_149, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 10.25/3.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.25/3.42  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.25/3.42  tff(c_205, plain, (![B_81, A_82]: (~r1_xboole_0(B_81, A_82) | ~r1_tarski(B_81, A_82) | v1_xboole_0(B_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.25/3.42  tff(c_227, plain, (![A_85]: (~r1_tarski(A_85, k1_xboole_0) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_10, c_205])).
% 10.25/3.42  tff(c_236, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_227])).
% 10.25/3.42  tff(c_18, plain, (![A_11, B_12]: (v1_xboole_0(k2_zfmisc_1(A_11, B_12)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.25/3.42  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_210, plain, (![B_83, A_84]: (v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.25/3.42  tff(c_225, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_210])).
% 10.25/3.42  tff(c_242, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_225])).
% 10.25/3.42  tff(c_250, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_242])).
% 10.25/3.42  tff(c_66, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.25/3.42  tff(c_42, plain, (![A_28]: (v2_funct_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.25/3.42  tff(c_87, plain, (![A_28]: (v2_funct_1(k6_partfun1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42])).
% 10.25/3.42  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_1239, plain, (![D_162, C_163, E_164, A_161, F_165, B_160]: (k1_partfun1(A_161, B_160, C_163, D_162, E_164, F_165)=k5_relat_1(E_164, F_165) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_163, D_162))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_1(E_164))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.25/3.42  tff(c_1249, plain, (![A_161, B_160, E_164]: (k1_partfun1(A_161, B_160, '#skF_2', '#skF_1', E_164, '#skF_4')=k5_relat_1(E_164, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_1(E_164))), inference(resolution, [status(thm)], [c_76, c_1239])).
% 10.25/3.42  tff(c_4099, plain, (![A_277, B_278, E_279]: (k1_partfun1(A_277, B_278, '#skF_2', '#skF_1', E_279, '#skF_4')=k5_relat_1(E_279, '#skF_4') | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~v1_funct_1(E_279))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1249])).
% 10.25/3.42  tff(c_4129, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4099])).
% 10.25/3.42  tff(c_4140, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4129])).
% 10.25/3.42  tff(c_56, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.25/3.42  tff(c_4615, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4140, c_56])).
% 10.25/3.42  tff(c_4622, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_4615])).
% 10.25/3.42  tff(c_62, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.25/3.42  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_851, plain, (![D_131, C_132, A_133, B_134]: (D_131=C_132 | ~r2_relset_1(A_133, B_134, C_132, D_131) | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.42  tff(c_857, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_851])).
% 10.25/3.42  tff(c_868, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_857])).
% 10.25/3.42  tff(c_4739, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4622, c_4140, c_4140, c_868])).
% 10.25/3.42  tff(c_38, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.25/3.42  tff(c_88, plain, (![A_27]: (k2_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 10.25/3.42  tff(c_28, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.25/3.42  tff(c_266, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.25/3.42  tff(c_272, plain, (![A_44]: (v1_relat_1(k6_partfun1(A_44)) | ~v1_relat_1(k2_zfmisc_1(A_44, A_44)))), inference(resolution, [status(thm)], [c_62, c_266])).
% 10.25/3.42  tff(c_329, plain, (![A_89]: (v1_relat_1(k6_partfun1(A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_272])).
% 10.25/3.42  tff(c_32, plain, (![A_26]: (k2_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.25/3.42  tff(c_332, plain, (![A_89]: (k2_relat_1(k6_partfun1(A_89))!=k1_xboole_0 | k6_partfun1(A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_329, c_32])).
% 10.25/3.42  tff(c_371, plain, (![A_94]: (k1_xboole_0!=A_94 | k6_partfun1(A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_332])).
% 10.25/3.42  tff(c_382, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_371, c_74])).
% 10.25/3.42  tff(c_436, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_382])).
% 10.25/3.42  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.25/3.42  tff(c_70, plain, (![D_55, B_53, E_57, A_52, C_54]: (k1_xboole_0=C_54 | v2_funct_1(D_55) | ~v2_funct_1(k1_partfun1(A_52, B_53, B_53, C_54, D_55, E_57)) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~v1_funct_2(E_57, B_53, C_54) | ~v1_funct_1(E_57) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_2(D_55, A_52, B_53) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.25/3.42  tff(c_4612, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4140, c_70])).
% 10.25/3.42  tff(c_4619, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_4612])).
% 10.25/3.42  tff(c_4620, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_149, c_436, c_4619])).
% 10.25/3.42  tff(c_4745, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4739, c_4620])).
% 10.25/3.42  tff(c_4755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_4745])).
% 10.25/3.42  tff(c_4757, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_382])).
% 10.25/3.42  tff(c_4767, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4757, c_236])).
% 10.25/3.42  tff(c_4780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_4767])).
% 10.25/3.42  tff(c_4781, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_225])).
% 10.25/3.42  tff(c_14, plain, (![B_8, A_7]: (~v1_xboole_0(B_8) | B_8=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.25/3.42  tff(c_4789, plain, (![A_295]: (A_295='#skF_3' | ~v1_xboole_0(A_295))), inference(resolution, [status(thm)], [c_4781, c_14])).
% 10.25/3.42  tff(c_4808, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_236, c_4789])).
% 10.25/3.42  tff(c_119, plain, (![A_68]: (k6_relat_1(A_68)=k6_partfun1(A_68))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.25/3.42  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.25/3.42  tff(c_125, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_119, c_40])).
% 10.25/3.42  tff(c_145, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_87])).
% 10.25/3.42  tff(c_4820, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4808, c_145])).
% 10.25/3.42  tff(c_4827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_4820])).
% 10.25/3.42  tff(c_4828, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 10.25/3.42  tff(c_4932, plain, (![B_311, A_312]: (v1_relat_1(B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(A_312)) | ~v1_relat_1(A_312))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.25/3.42  tff(c_4944, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_4932])).
% 10.25/3.42  tff(c_4956, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4944])).
% 10.25/3.42  tff(c_5083, plain, (![C_322, B_323, A_324]: (v5_relat_1(C_322, B_323) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_324, B_323))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.25/3.42  tff(c_5099, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_5083])).
% 10.25/3.42  tff(c_26, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.25/3.42  tff(c_4941, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_4932])).
% 10.25/3.42  tff(c_4953, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4941])).
% 10.25/3.42  tff(c_5883, plain, (![C_391, E_392, D_390, A_389, F_393, B_388]: (k1_partfun1(A_389, B_388, C_391, D_390, E_392, F_393)=k5_relat_1(E_392, F_393) | ~m1_subset_1(F_393, k1_zfmisc_1(k2_zfmisc_1(C_391, D_390))) | ~v1_funct_1(F_393) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))) | ~v1_funct_1(E_392))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.25/3.42  tff(c_5893, plain, (![A_389, B_388, E_392]: (k1_partfun1(A_389, B_388, '#skF_2', '#skF_1', E_392, '#skF_4')=k5_relat_1(E_392, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))) | ~v1_funct_1(E_392))), inference(resolution, [status(thm)], [c_76, c_5883])).
% 10.25/3.42  tff(c_7508, plain, (![A_480, B_481, E_482]: (k1_partfun1(A_480, B_481, '#skF_2', '#skF_1', E_482, '#skF_4')=k5_relat_1(E_482, '#skF_4') | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))) | ~v1_funct_1(E_482))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5893])).
% 10.25/3.42  tff(c_7535, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_7508])).
% 10.25/3.42  tff(c_7543, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_7535])).
% 10.25/3.42  tff(c_8629, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7543, c_56])).
% 10.25/3.42  tff(c_8636, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_8629])).
% 10.25/3.42  tff(c_5458, plain, (![D_357, C_358, A_359, B_360]: (D_357=C_358 | ~r2_relset_1(A_359, B_360, C_358, D_357) | ~m1_subset_1(D_357, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.42  tff(c_5464, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_5458])).
% 10.25/3.42  tff(c_5475, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5464])).
% 10.25/3.42  tff(c_5542, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5475])).
% 10.25/3.42  tff(c_9210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8636, c_7543, c_5542])).
% 10.25/3.42  tff(c_9211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5475])).
% 10.25/3.42  tff(c_9676, plain, (![B_541, F_546, C_544, D_543, E_545, A_542]: (k1_partfun1(A_542, B_541, C_544, D_543, E_545, F_546)=k5_relat_1(E_545, F_546) | ~m1_subset_1(F_546, k1_zfmisc_1(k2_zfmisc_1(C_544, D_543))) | ~v1_funct_1(F_546) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(A_542, B_541))) | ~v1_funct_1(E_545))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.25/3.42  tff(c_9686, plain, (![A_542, B_541, E_545]: (k1_partfun1(A_542, B_541, '#skF_2', '#skF_1', E_545, '#skF_4')=k5_relat_1(E_545, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(A_542, B_541))) | ~v1_funct_1(E_545))), inference(resolution, [status(thm)], [c_76, c_9676])).
% 10.25/3.42  tff(c_12494, plain, (![A_658, B_659, E_660]: (k1_partfun1(A_658, B_659, '#skF_2', '#skF_1', E_660, '#skF_4')=k5_relat_1(E_660, '#skF_4') | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))) | ~v1_funct_1(E_660))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9686])).
% 10.25/3.42  tff(c_12527, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_12494])).
% 10.25/3.42  tff(c_12541, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9211, c_12527])).
% 10.25/3.42  tff(c_30, plain, (![A_23, B_25]: (r1_tarski(k2_relat_1(k5_relat_1(A_23, B_25)), k2_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.25/3.42  tff(c_12548, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12541, c_30])).
% 10.25/3.42  tff(c_12552, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4953, c_4956, c_88, c_12548])).
% 10.25/3.42  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.25/3.42  tff(c_12560, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_12552, c_2])).
% 10.25/3.42  tff(c_12567, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_12560])).
% 10.25/3.42  tff(c_12574, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_12567])).
% 10.25/3.42  tff(c_12579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4956, c_5099, c_12574])).
% 10.25/3.42  tff(c_12580, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12560])).
% 10.25/3.42  tff(c_5108, plain, (![B_327, A_328]: (v5_relat_1(B_327, A_328) | ~r1_tarski(k2_relat_1(B_327), A_328) | ~v1_relat_1(B_327))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.25/3.42  tff(c_5123, plain, (![B_327]: (v5_relat_1(B_327, k2_relat_1(B_327)) | ~v1_relat_1(B_327))), inference(resolution, [status(thm)], [c_6, c_5108])).
% 10.25/3.42  tff(c_5223, plain, (![B_337]: (v2_funct_2(B_337, k2_relat_1(B_337)) | ~v5_relat_1(B_337, k2_relat_1(B_337)) | ~v1_relat_1(B_337))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.25/3.42  tff(c_5237, plain, (![B_327]: (v2_funct_2(B_327, k2_relat_1(B_327)) | ~v1_relat_1(B_327))), inference(resolution, [status(thm)], [c_5123, c_5223])).
% 10.25/3.42  tff(c_12594, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12580, c_5237])).
% 10.25/3.42  tff(c_12612, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_12594])).
% 10.25/3.42  tff(c_12614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4828, c_12612])).
% 10.25/3.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.42  
% 10.25/3.42  Inference rules
% 10.25/3.42  ----------------------
% 10.25/3.42  #Ref     : 6
% 10.25/3.42  #Sup     : 3031
% 10.25/3.42  #Fact    : 0
% 10.25/3.42  #Define  : 0
% 10.25/3.42  #Split   : 24
% 10.25/3.42  #Chain   : 0
% 10.25/3.42  #Close   : 0
% 10.25/3.42  
% 10.25/3.42  Ordering : KBO
% 10.25/3.42  
% 10.25/3.42  Simplification rules
% 10.25/3.42  ----------------------
% 10.25/3.42  #Subsume      : 360
% 10.25/3.42  #Demod        : 2074
% 10.25/3.42  #Tautology    : 1590
% 10.25/3.42  #SimpNegUnit  : 10
% 10.25/3.42  #BackRed      : 59
% 10.25/3.42  
% 10.25/3.42  #Partial instantiations: 0
% 10.25/3.42  #Strategies tried      : 1
% 10.25/3.42  
% 10.25/3.42  Timing (in seconds)
% 10.25/3.42  ----------------------
% 10.25/3.43  Preprocessing        : 0.39
% 10.25/3.43  Parsing              : 0.22
% 10.25/3.43  CNF conversion       : 0.03
% 10.25/3.43  Main loop            : 2.20
% 10.25/3.43  Inferencing          : 0.62
% 10.38/3.43  Reduction            : 0.86
% 10.38/3.43  Demodulation         : 0.63
% 10.38/3.43  BG Simplification    : 0.07
% 10.38/3.43  Subsumption          : 0.49
% 10.38/3.43  Abstraction          : 0.09
% 10.38/3.43  MUC search           : 0.00
% 10.38/3.43  Cooper               : 0.00
% 10.38/3.43  Total                : 2.64
% 10.38/3.43  Index Insertion      : 0.00
% 10.38/3.43  Index Deletion       : 0.00
% 10.38/3.43  Index Matching       : 0.00
% 10.38/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
