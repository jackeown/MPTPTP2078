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
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  258 (2054 expanded)
%              Number of leaves         :   47 ( 698 expanded)
%              Depth                    :   19
%              Number of atoms          :  508 (5189 expanded)
%              Number of equality atoms :  138 (1478 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

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

tff(f_155,axiom,(
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

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_154,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_237,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_246,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_237])).

tff(c_258,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_246])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_249,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_237])).

tff(c_261,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_249])).

tff(c_1956,plain,(
    ! [C_215,B_216,A_217] :
      ( v5_relat_1(C_215,B_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1968,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1956])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_995,plain,(
    ! [C_158,D_156,F_155,E_157,A_153,B_154] :
      ( k1_partfun1(A_153,B_154,C_158,D_156,E_157,F_155) = k5_relat_1(E_157,F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_158,D_156)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(E_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1003,plain,(
    ! [A_153,B_154,E_157] :
      ( k1_partfun1(A_153,B_154,'#skF_2','#skF_1',E_157,'#skF_4') = k5_relat_1(E_157,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(E_157) ) ),
    inference(resolution,[status(thm)],[c_70,c_995])).

tff(c_1392,plain,(
    ! [A_198,B_199,E_200] :
      ( k1_partfun1(A_198,B_199,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1003])).

tff(c_1410,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1392])).

tff(c_1425,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1410])).

tff(c_50,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( m1_subset_1(k1_partfun1(A_30,B_31,C_32,D_33,E_34,F_35),k1_zfmisc_1(k2_zfmisc_1(A_30,D_33)))
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1748,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_50])).

tff(c_1755,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1748])).

tff(c_56,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_774,plain,(
    ! [D_127,C_128,A_129,B_130] :
      ( D_127 = C_128
      | ~ r2_relset_1(A_129,B_130,C_128,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_784,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_774])).

tff(c_801,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_784])).

tff(c_1852,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_1425,c_1425,c_801])).

tff(c_30,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_34,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_82,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_155,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_164,plain,(
    ! [A_20] :
      ( k2_relat_1(k6_partfun1(A_20)) != k1_xboole_0
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_82,c_155])).

tff(c_171,plain,(
    ! [A_20] :
      ( k1_xboole_0 != A_20
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_164])).

tff(c_212,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_68])).

tff(c_296,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    ! [C_46,A_44,B_45,D_47,E_49] :
      ( k1_xboole_0 = C_46
      | v2_funct_1(D_47)
      | ~ v2_funct_1(k1_partfun1(A_44,B_45,B_45,C_46,D_47,E_49))
      | ~ m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ v1_funct_2(E_49,B_45,C_46)
      | ~ v1_funct_1(E_49)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1745,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_64])).

tff(c_1752,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_1745])).

tff(c_1753,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_296,c_1752])).

tff(c_1859,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_1753])).

tff(c_1870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1859])).

tff(c_1872,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_24,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_261,c_24])).

tff(c_1973,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1872,c_277])).

tff(c_1974,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1973])).

tff(c_103,plain,(
    ! [A_57] : k6_relat_1(A_57) = k6_partfun1(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_32])).

tff(c_130,plain,(
    ! [A_58] : k2_relat_1(k6_partfun1(A_58)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_139,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_130])).

tff(c_1879,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1872,c_139])).

tff(c_2616,plain,(
    ! [A_289,C_294,B_290,E_293,F_291,D_292] :
      ( k1_partfun1(A_289,B_290,C_294,D_292,E_293,F_291) = k5_relat_1(E_293,F_291)
      | ~ m1_subset_1(F_291,k1_zfmisc_1(k2_zfmisc_1(C_294,D_292)))
      | ~ v1_funct_1(F_291)
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2624,plain,(
    ! [A_289,B_290,E_293] :
      ( k1_partfun1(A_289,B_290,'#skF_2','#skF_1',E_293,'#skF_4') = k5_relat_1(E_293,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_293) ) ),
    inference(resolution,[status(thm)],[c_70,c_2616])).

tff(c_2825,plain,(
    ! [A_316,B_317,E_318] :
      ( k1_partfun1(A_316,B_317,'#skF_2','#skF_1',E_318,'#skF_4') = k5_relat_1(E_318,'#skF_4')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(E_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2624])).

tff(c_2837,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2825])).

tff(c_2846,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2837])).

tff(c_2950,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2846,c_50])).

tff(c_2954,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2950])).

tff(c_172,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_175,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_172])).

tff(c_1875,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1872,c_1872,c_175])).

tff(c_1871,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_1926,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1871])).

tff(c_2342,plain,(
    ! [D_258,C_259,A_260,B_261] :
      ( D_258 = C_259
      | ~ r2_relset_1(A_260,B_261,C_259,D_258)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2352,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1926,c_2342])).

tff(c_2371,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = '#skF_1'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_2352])).

tff(c_2430,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2371])).

tff(c_4387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2954,c_2846,c_2430])).

tff(c_4388,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2371])).

tff(c_4591,plain,(
    ! [E_446,C_447,D_445,F_444,A_442,B_443] :
      ( k1_partfun1(A_442,B_443,C_447,D_445,E_446,F_444) = k5_relat_1(E_446,F_444)
      | ~ m1_subset_1(F_444,k1_zfmisc_1(k2_zfmisc_1(C_447,D_445)))
      | ~ v1_funct_1(F_444)
      | ~ m1_subset_1(E_446,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_1(E_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4599,plain,(
    ! [A_442,B_443,E_446] :
      ( k1_partfun1(A_442,B_443,'#skF_2','#skF_1',E_446,'#skF_4') = k5_relat_1(E_446,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_446,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_1(E_446) ) ),
    inference(resolution,[status(thm)],[c_70,c_4591])).

tff(c_4789,plain,(
    ! [A_469,B_470,E_471] :
      ( k1_partfun1(A_469,B_470,'#skF_2','#skF_1',E_471,'#skF_4') = k5_relat_1(E_471,'#skF_4')
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470)))
      | ~ v1_funct_1(E_471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4599])).

tff(c_4801,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4789])).

tff(c_4812,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4388,c_4801])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,B_17)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4819,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4812,c_22])).

tff(c_4826,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_261,c_1879,c_4819])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4837,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4826,c_2])).

tff(c_4843,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1974,c_4837])).

tff(c_4914,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4843])).

tff(c_4920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_1968,c_4914])).

tff(c_4921,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1973])).

tff(c_28,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_121,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_84])).

tff(c_1880,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1872,c_121])).

tff(c_4931,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4921,c_4921,c_1880])).

tff(c_26,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_276,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_261,c_26])).

tff(c_295,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_1888,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_295])).

tff(c_4932,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4921,c_1888])).

tff(c_4985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4931,c_4932])).

tff(c_4986,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_4988,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_5005,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_4988])).

tff(c_5724,plain,(
    ! [E_554,C_555,B_551,F_552,A_550,D_553] :
      ( k1_partfun1(A_550,B_551,C_555,D_553,E_554,F_552) = k5_relat_1(E_554,F_552)
      | ~ m1_subset_1(F_552,k1_zfmisc_1(k2_zfmisc_1(C_555,D_553)))
      | ~ v1_funct_1(F_552)
      | ~ m1_subset_1(E_554,k1_zfmisc_1(k2_zfmisc_1(A_550,B_551)))
      | ~ v1_funct_1(E_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5732,plain,(
    ! [A_550,B_551,E_554] :
      ( k1_partfun1(A_550,B_551,'#skF_2','#skF_1',E_554,'#skF_4') = k5_relat_1(E_554,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_554,k1_zfmisc_1(k2_zfmisc_1(A_550,B_551)))
      | ~ v1_funct_1(E_554) ) ),
    inference(resolution,[status(thm)],[c_70,c_5724])).

tff(c_6330,plain,(
    ! [A_597,B_598,E_599] :
      ( k1_partfun1(A_597,B_598,'#skF_2','#skF_1',E_599,'#skF_4') = k5_relat_1(E_599,'#skF_4')
      | ~ m1_subset_1(E_599,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598)))
      | ~ v1_funct_1(E_599) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5732])).

tff(c_6348,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_6330])).

tff(c_6365,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6348])).

tff(c_6711,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6365,c_50])).

tff(c_6718,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_6711])).

tff(c_5422,plain,(
    ! [D_519,C_520,A_521,B_522] :
      ( D_519 = C_520
      | ~ r2_relset_1(A_521,B_522,C_520,D_519)
      | ~ m1_subset_1(D_519,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522)))
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5430,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_5422])).

tff(c_5445,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5430])).

tff(c_5489,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5445])).

tff(c_6895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6718,c_6365,c_5489])).

tff(c_6896,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5445])).

tff(c_7539,plain,(
    ! [C_46,A_44,B_45,D_47,E_49] :
      ( C_46 = '#skF_4'
      | v2_funct_1(D_47)
      | ~ v2_funct_1(k1_partfun1(A_44,B_45,B_45,C_46,D_47,E_49))
      | ~ m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ v1_funct_2(E_49,B_45,C_46)
      | ~ v1_funct_1(E_49)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_64])).

tff(c_7857,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6896,c_7539])).

tff(c_7864,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_7857])).

tff(c_7866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_5005,c_7864])).

tff(c_7868,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_7885,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_7868])).

tff(c_7887,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_76])).

tff(c_40,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8017,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7887,c_40])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_268,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_258,c_26])).

tff(c_294,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_7869,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_294])).

tff(c_4987,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_7895,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_4987])).

tff(c_7888,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_70])).

tff(c_9228,plain,(
    ! [F_823,E_825,B_822,A_821,C_826,D_824] :
      ( k1_partfun1(A_821,B_822,C_826,D_824,E_825,F_823) = k5_relat_1(E_825,F_823)
      | ~ m1_subset_1(F_823,k1_zfmisc_1(k2_zfmisc_1(C_826,D_824)))
      | ~ v1_funct_1(F_823)
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(A_821,B_822)))
      | ~ v1_funct_1(E_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9232,plain,(
    ! [A_821,B_822,E_825] :
      ( k1_partfun1(A_821,B_822,'#skF_2','#skF_4',E_825,'#skF_4') = k5_relat_1(E_825,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(A_821,B_822)))
      | ~ v1_funct_1(E_825) ) ),
    inference(resolution,[status(thm)],[c_7888,c_9228])).

tff(c_9614,plain,(
    ! [A_851,B_852,E_853] :
      ( k1_partfun1(A_851,B_852,'#skF_2','#skF_4',E_853,'#skF_4') = k5_relat_1(E_853,'#skF_4')
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852)))
      | ~ v1_funct_1(E_853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9232])).

tff(c_9626,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7887,c_9614])).

tff(c_9639,plain,(
    k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9626])).

tff(c_9745,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9639,c_50])).

tff(c_9749,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7887,c_74,c_7888,c_9745])).

tff(c_178,plain,(
    ! [A_62] :
      ( k1_xboole_0 != A_62
      | k6_partfun1(A_62) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_164])).

tff(c_184,plain,(
    ! [A_62] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_62,A_62)))
      | k1_xboole_0 != A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_56])).

tff(c_8272,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_4986,c_184])).

tff(c_7974,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_4986,c_171])).

tff(c_7886,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7885,c_7885,c_7885,c_7885,c_7885,c_68])).

tff(c_8139,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7974,c_7886])).

tff(c_8880,plain,(
    ! [D_783,C_784,A_785,B_786] :
      ( D_783 = C_784
      | ~ r2_relset_1(A_785,B_786,C_784,D_783)
      | ~ m1_subset_1(D_783,k1_zfmisc_1(k2_zfmisc_1(A_785,B_786)))
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_zfmisc_1(A_785,B_786))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8894,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8139,c_8880])).

tff(c_8917,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8272,c_8894])).

tff(c_8978,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_8917])).

tff(c_10414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9749,c_9639,c_8978])).

tff(c_10415,plain,(
    k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8917])).

tff(c_10551,plain,(
    ! [C_909,E_908,D_907,B_905,A_904,F_906] :
      ( k1_partfun1(A_904,B_905,C_909,D_907,E_908,F_906) = k5_relat_1(E_908,F_906)
      | ~ m1_subset_1(F_906,k1_zfmisc_1(k2_zfmisc_1(C_909,D_907)))
      | ~ v1_funct_1(F_906)
      | ~ m1_subset_1(E_908,k1_zfmisc_1(k2_zfmisc_1(A_904,B_905)))
      | ~ v1_funct_1(E_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10555,plain,(
    ! [A_904,B_905,E_908] :
      ( k1_partfun1(A_904,B_905,'#skF_2','#skF_4',E_908,'#skF_4') = k5_relat_1(E_908,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_908,k1_zfmisc_1(k2_zfmisc_1(A_904,B_905)))
      | ~ v1_funct_1(E_908) ) ),
    inference(resolution,[status(thm)],[c_7888,c_10551])).

tff(c_10860,plain,(
    ! [A_937,B_938,E_939] :
      ( k1_partfun1(A_937,B_938,'#skF_2','#skF_4',E_939,'#skF_4') = k5_relat_1(E_939,'#skF_4')
      | ~ m1_subset_1(E_939,k1_zfmisc_1(k2_zfmisc_1(A_937,B_938)))
      | ~ v1_funct_1(E_939) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10555])).

tff(c_10872,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7887,c_10860])).

tff(c_10885,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10415,c_10872])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_12,B_14)),k1_relat_1(A_12))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10902,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10885,c_20])).

tff(c_10914,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_261,c_7895,c_10902])).

tff(c_10923,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10914,c_2])).

tff(c_10929,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7869,c_10923])).

tff(c_10982,plain,
    ( ~ v4_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_10929])).

tff(c_10988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_8017,c_10982])).

tff(c_10989,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_125,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_81])).

tff(c_11016,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10989,c_125])).

tff(c_11020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_11016])).

tff(c_11021,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_11105,plain,(
    ! [B_949,A_950] :
      ( v1_relat_1(B_949)
      | ~ m1_subset_1(B_949,k1_zfmisc_1(A_950))
      | ~ v1_relat_1(A_950) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11117,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_11105])).

tff(c_11129,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11117])).

tff(c_11165,plain,(
    ! [C_953,B_954,A_955] :
      ( v5_relat_1(C_953,B_954)
      | ~ m1_subset_1(C_953,k1_zfmisc_1(k2_zfmisc_1(A_955,B_954))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11181,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_11165])).

tff(c_11114,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_11105])).

tff(c_11126,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11114])).

tff(c_11905,plain,(
    ! [F_1045,B_1044,E_1047,D_1046,A_1043,C_1048] :
      ( k1_partfun1(A_1043,B_1044,C_1048,D_1046,E_1047,F_1045) = k5_relat_1(E_1047,F_1045)
      | ~ m1_subset_1(F_1045,k1_zfmisc_1(k2_zfmisc_1(C_1048,D_1046)))
      | ~ v1_funct_1(F_1045)
      | ~ m1_subset_1(E_1047,k1_zfmisc_1(k2_zfmisc_1(A_1043,B_1044)))
      | ~ v1_funct_1(E_1047) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_11913,plain,(
    ! [A_1043,B_1044,E_1047] :
      ( k1_partfun1(A_1043,B_1044,'#skF_2','#skF_1',E_1047,'#skF_4') = k5_relat_1(E_1047,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1047,k1_zfmisc_1(k2_zfmisc_1(A_1043,B_1044)))
      | ~ v1_funct_1(E_1047) ) ),
    inference(resolution,[status(thm)],[c_70,c_11905])).

tff(c_12305,plain,(
    ! [A_1088,B_1089,E_1090] :
      ( k1_partfun1(A_1088,B_1089,'#skF_2','#skF_1',E_1090,'#skF_4') = k5_relat_1(E_1090,'#skF_4')
      | ~ m1_subset_1(E_1090,k1_zfmisc_1(k2_zfmisc_1(A_1088,B_1089)))
      | ~ v1_funct_1(E_1090) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_11913])).

tff(c_12323,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_12305])).

tff(c_12338,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12323])).

tff(c_12689,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12338,c_50])).

tff(c_12696,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_12689])).

tff(c_11626,plain,(
    ! [D_1009,C_1010,A_1011,B_1012] :
      ( D_1009 = C_1010
      | ~ r2_relset_1(A_1011,B_1012,C_1010,D_1009)
      | ~ m1_subset_1(D_1009,k1_zfmisc_1(k2_zfmisc_1(A_1011,B_1012)))
      | ~ m1_subset_1(C_1010,k1_zfmisc_1(k2_zfmisc_1(A_1011,B_1012))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11640,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_11626])).

tff(c_11663,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11640])).

tff(c_11721,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11663])).

tff(c_12766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12696,c_12338,c_11721])).

tff(c_12767,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11663])).

tff(c_13030,plain,(
    ! [A_1132,E_1136,D_1135,F_1134,C_1137,B_1133] :
      ( k1_partfun1(A_1132,B_1133,C_1137,D_1135,E_1136,F_1134) = k5_relat_1(E_1136,F_1134)
      | ~ m1_subset_1(F_1134,k1_zfmisc_1(k2_zfmisc_1(C_1137,D_1135)))
      | ~ v1_funct_1(F_1134)
      | ~ m1_subset_1(E_1136,k1_zfmisc_1(k2_zfmisc_1(A_1132,B_1133)))
      | ~ v1_funct_1(E_1136) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13038,plain,(
    ! [A_1132,B_1133,E_1136] :
      ( k1_partfun1(A_1132,B_1133,'#skF_2','#skF_1',E_1136,'#skF_4') = k5_relat_1(E_1136,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1136,k1_zfmisc_1(k2_zfmisc_1(A_1132,B_1133)))
      | ~ v1_funct_1(E_1136) ) ),
    inference(resolution,[status(thm)],[c_70,c_13030])).

tff(c_13280,plain,(
    ! [A_1165,B_1166,E_1167] :
      ( k1_partfun1(A_1165,B_1166,'#skF_2','#skF_1',E_1167,'#skF_4') = k5_relat_1(E_1167,'#skF_4')
      | ~ m1_subset_1(E_1167,k1_zfmisc_1(k2_zfmisc_1(A_1165,B_1166)))
      | ~ v1_funct_1(E_1167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13038])).

tff(c_13292,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_13280])).

tff(c_13301,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12767,c_13292])).

tff(c_13311,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13301,c_22])).

tff(c_13317,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11126,c_11129,c_83,c_13311])).

tff(c_13336,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13317,c_2])).

tff(c_13427,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13336])).

tff(c_13433,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_13427])).

tff(c_13438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11129,c_11181,c_13433])).

tff(c_13439,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13336])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11258,plain,(
    ! [B_967,A_968] :
      ( v5_relat_1(B_967,A_968)
      | ~ r1_tarski(k2_relat_1(B_967),A_968)
      | ~ v1_relat_1(B_967) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11277,plain,(
    ! [B_967] :
      ( v5_relat_1(B_967,k2_relat_1(B_967))
      | ~ v1_relat_1(B_967) ) ),
    inference(resolution,[status(thm)],[c_6,c_11258])).

tff(c_11354,plain,(
    ! [B_980] :
      ( v2_funct_2(B_980,k2_relat_1(B_980))
      | ~ v5_relat_1(B_980,k2_relat_1(B_980))
      | ~ v1_relat_1(B_980) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11375,plain,(
    ! [B_967] :
      ( v2_funct_2(B_967,k2_relat_1(B_967))
      | ~ v1_relat_1(B_967) ) ),
    inference(resolution,[status(thm)],[c_11277,c_11354])).

tff(c_13450,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13439,c_11375])).

tff(c_13465,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11129,c_13450])).

tff(c_13467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11021,c_13465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.14/3.23  
% 9.14/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.14/3.23  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.14/3.23  
% 9.14/3.23  %Foreground sorts:
% 9.14/3.23  
% 9.14/3.23  
% 9.14/3.23  %Background operators:
% 9.14/3.23  
% 9.14/3.23  
% 9.14/3.23  %Foreground operators:
% 9.14/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.14/3.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.14/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.14/3.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.14/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.14/3.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.14/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.14/3.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.14/3.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.14/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.14/3.23  tff('#skF_2', type, '#skF_2': $i).
% 9.14/3.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.14/3.23  tff('#skF_3', type, '#skF_3': $i).
% 9.14/3.23  tff('#skF_1', type, '#skF_1': $i).
% 9.14/3.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.14/3.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.14/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.14/3.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.14/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.14/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.14/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.14/3.23  tff('#skF_4', type, '#skF_4': $i).
% 9.14/3.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.14/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.14/3.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.14/3.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.14/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.14/3.23  
% 9.14/3.27  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 9.14/3.27  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.14/3.27  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.14/3.27  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.14/3.27  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.14/3.27  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.14/3.27  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.14/3.27  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.14/3.27  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.14/3.27  tff(f_121, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.14/3.27  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.14/3.27  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.14/3.27  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.14/3.27  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 9.14/3.27  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 9.14/3.27  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.14/3.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.14/3.27  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.14/3.27  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.14/3.27  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.14/3.27  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_154, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 9.14/3.27  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.14/3.27  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_237, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.14/3.27  tff(c_246, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_237])).
% 9.14/3.27  tff(c_258, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_246])).
% 9.14/3.27  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_249, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_237])).
% 9.14/3.27  tff(c_261, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_249])).
% 9.14/3.27  tff(c_1956, plain, (![C_215, B_216, A_217]: (v5_relat_1(C_215, B_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.14/3.27  tff(c_1968, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_1956])).
% 9.14/3.27  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.14/3.27  tff(c_60, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.14/3.27  tff(c_36, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.14/3.27  tff(c_81, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 9.14/3.27  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_995, plain, (![C_158, D_156, F_155, E_157, A_153, B_154]: (k1_partfun1(A_153, B_154, C_158, D_156, E_157, F_155)=k5_relat_1(E_157, F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_158, D_156))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(E_157))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_1003, plain, (![A_153, B_154, E_157]: (k1_partfun1(A_153, B_154, '#skF_2', '#skF_1', E_157, '#skF_4')=k5_relat_1(E_157, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(E_157))), inference(resolution, [status(thm)], [c_70, c_995])).
% 9.14/3.27  tff(c_1392, plain, (![A_198, B_199, E_200]: (k1_partfun1(A_198, B_199, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(E_200))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1003])).
% 9.14/3.27  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1392])).
% 9.14/3.27  tff(c_1425, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1410])).
% 9.14/3.27  tff(c_50, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (m1_subset_1(k1_partfun1(A_30, B_31, C_32, D_33, E_34, F_35), k1_zfmisc_1(k2_zfmisc_1(A_30, D_33))) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(E_34))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.27  tff(c_1748, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1425, c_50])).
% 9.14/3.27  tff(c_1755, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1748])).
% 9.14/3.27  tff(c_56, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.14/3.27  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_774, plain, (![D_127, C_128, A_129, B_130]: (D_127=C_128 | ~r2_relset_1(A_129, B_130, C_128, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.27  tff(c_784, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_774])).
% 9.14/3.27  tff(c_801, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_784])).
% 9.14/3.27  tff(c_1852, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_1425, c_1425, c_801])).
% 9.14/3.27  tff(c_30, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.14/3.27  tff(c_83, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30])).
% 9.14/3.27  tff(c_34, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.14/3.27  tff(c_82, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 9.14/3.27  tff(c_155, plain, (![A_60]: (k2_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.14/3.27  tff(c_164, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))!=k1_xboole_0 | k6_partfun1(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_155])).
% 9.14/3.27  tff(c_171, plain, (![A_20]: (k1_xboole_0!=A_20 | k6_partfun1(A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_164])).
% 9.14/3.27  tff(c_212, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_171, c_68])).
% 9.14/3.27  tff(c_296, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_212])).
% 9.14/3.27  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.14/3.27  tff(c_64, plain, (![C_46, A_44, B_45, D_47, E_49]: (k1_xboole_0=C_46 | v2_funct_1(D_47) | ~v2_funct_1(k1_partfun1(A_44, B_45, B_45, C_46, D_47, E_49)) | ~m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~v1_funct_2(E_49, B_45, C_46) | ~v1_funct_1(E_49) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.14/3.27  tff(c_1745, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1425, c_64])).
% 9.14/3.27  tff(c_1752, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_1745])).
% 9.14/3.27  tff(c_1753, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_154, c_296, c_1752])).
% 9.14/3.27  tff(c_1859, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_1753])).
% 9.14/3.27  tff(c_1870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_1859])).
% 9.14/3.27  tff(c_1872, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_212])).
% 9.14/3.27  tff(c_24, plain, (![A_18]: (k2_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.14/3.27  tff(c_277, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_261, c_24])).
% 9.14/3.27  tff(c_1973, plain, (k2_relat_1('#skF_4')!='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1872, c_277])).
% 9.14/3.27  tff(c_1974, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1973])).
% 9.14/3.27  tff(c_103, plain, (![A_57]: (k6_relat_1(A_57)=k6_partfun1(A_57))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.14/3.27  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.14/3.27  tff(c_109, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_103, c_32])).
% 9.14/3.27  tff(c_130, plain, (![A_58]: (k2_relat_1(k6_partfun1(A_58))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30])).
% 9.14/3.27  tff(c_139, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_109, c_130])).
% 9.14/3.27  tff(c_1879, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1872, c_139])).
% 9.14/3.27  tff(c_2616, plain, (![A_289, C_294, B_290, E_293, F_291, D_292]: (k1_partfun1(A_289, B_290, C_294, D_292, E_293, F_291)=k5_relat_1(E_293, F_291) | ~m1_subset_1(F_291, k1_zfmisc_1(k2_zfmisc_1(C_294, D_292))) | ~v1_funct_1(F_291) | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_293))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_2624, plain, (![A_289, B_290, E_293]: (k1_partfun1(A_289, B_290, '#skF_2', '#skF_1', E_293, '#skF_4')=k5_relat_1(E_293, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_293))), inference(resolution, [status(thm)], [c_70, c_2616])).
% 9.14/3.27  tff(c_2825, plain, (![A_316, B_317, E_318]: (k1_partfun1(A_316, B_317, '#skF_2', '#skF_1', E_318, '#skF_4')=k5_relat_1(E_318, '#skF_4') | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_1(E_318))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2624])).
% 9.14/3.27  tff(c_2837, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2825])).
% 9.14/3.27  tff(c_2846, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2837])).
% 9.14/3.27  tff(c_2950, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2846, c_50])).
% 9.14/3.27  tff(c_2954, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2950])).
% 9.14/3.27  tff(c_172, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.14/3.27  tff(c_175, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_172])).
% 9.14/3.27  tff(c_1875, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1872, c_1872, c_175])).
% 9.14/3.27  tff(c_1871, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_212])).
% 9.14/3.27  tff(c_1926, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1871])).
% 9.14/3.27  tff(c_2342, plain, (![D_258, C_259, A_260, B_261]: (D_258=C_259 | ~r2_relset_1(A_260, B_261, C_259, D_258) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.27  tff(c_2352, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_1926, c_2342])).
% 9.14/3.27  tff(c_2371, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')='#skF_1' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_2352])).
% 9.14/3.27  tff(c_2430, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2371])).
% 9.14/3.27  tff(c_4387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2954, c_2846, c_2430])).
% 9.14/3.27  tff(c_4388, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2371])).
% 9.14/3.27  tff(c_4591, plain, (![E_446, C_447, D_445, F_444, A_442, B_443]: (k1_partfun1(A_442, B_443, C_447, D_445, E_446, F_444)=k5_relat_1(E_446, F_444) | ~m1_subset_1(F_444, k1_zfmisc_1(k2_zfmisc_1(C_447, D_445))) | ~v1_funct_1(F_444) | ~m1_subset_1(E_446, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_1(E_446))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_4599, plain, (![A_442, B_443, E_446]: (k1_partfun1(A_442, B_443, '#skF_2', '#skF_1', E_446, '#skF_4')=k5_relat_1(E_446, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_446, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_1(E_446))), inference(resolution, [status(thm)], [c_70, c_4591])).
% 9.14/3.27  tff(c_4789, plain, (![A_469, B_470, E_471]: (k1_partfun1(A_469, B_470, '#skF_2', '#skF_1', E_471, '#skF_4')=k5_relat_1(E_471, '#skF_4') | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))) | ~v1_funct_1(E_471))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4599])).
% 9.14/3.27  tff(c_4801, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4789])).
% 9.14/3.27  tff(c_4812, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4388, c_4801])).
% 9.14/3.27  tff(c_22, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, B_17)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.14/3.27  tff(c_4819, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4812, c_22])).
% 9.14/3.27  tff(c_4826, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_261, c_1879, c_4819])).
% 9.14/3.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.14/3.27  tff(c_4837, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_4826, c_2])).
% 9.14/3.27  tff(c_4843, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1974, c_4837])).
% 9.14/3.27  tff(c_4914, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_4843])).
% 9.14/3.27  tff(c_4920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_1968, c_4914])).
% 9.14/3.27  tff(c_4921, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1973])).
% 9.14/3.27  tff(c_28, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.14/3.27  tff(c_84, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28])).
% 9.14/3.27  tff(c_121, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_109, c_84])).
% 9.14/3.27  tff(c_1880, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1872, c_121])).
% 9.14/3.27  tff(c_4931, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4921, c_4921, c_1880])).
% 9.14/3.27  tff(c_26, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.14/3.27  tff(c_276, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_261, c_26])).
% 9.14/3.27  tff(c_295, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_276])).
% 9.14/3.27  tff(c_1888, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_295])).
% 9.14/3.27  tff(c_4932, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4921, c_1888])).
% 9.14/3.27  tff(c_4985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4931, c_4932])).
% 9.14/3.27  tff(c_4986, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_276])).
% 9.14/3.27  tff(c_4988, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_212])).
% 9.14/3.27  tff(c_5005, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_4988])).
% 9.14/3.27  tff(c_5724, plain, (![E_554, C_555, B_551, F_552, A_550, D_553]: (k1_partfun1(A_550, B_551, C_555, D_553, E_554, F_552)=k5_relat_1(E_554, F_552) | ~m1_subset_1(F_552, k1_zfmisc_1(k2_zfmisc_1(C_555, D_553))) | ~v1_funct_1(F_552) | ~m1_subset_1(E_554, k1_zfmisc_1(k2_zfmisc_1(A_550, B_551))) | ~v1_funct_1(E_554))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_5732, plain, (![A_550, B_551, E_554]: (k1_partfun1(A_550, B_551, '#skF_2', '#skF_1', E_554, '#skF_4')=k5_relat_1(E_554, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_554, k1_zfmisc_1(k2_zfmisc_1(A_550, B_551))) | ~v1_funct_1(E_554))), inference(resolution, [status(thm)], [c_70, c_5724])).
% 9.14/3.27  tff(c_6330, plain, (![A_597, B_598, E_599]: (k1_partfun1(A_597, B_598, '#skF_2', '#skF_1', E_599, '#skF_4')=k5_relat_1(E_599, '#skF_4') | ~m1_subset_1(E_599, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))) | ~v1_funct_1(E_599))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5732])).
% 9.14/3.27  tff(c_6348, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_6330])).
% 9.14/3.27  tff(c_6365, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6348])).
% 9.14/3.27  tff(c_6711, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6365, c_50])).
% 9.14/3.27  tff(c_6718, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_6711])).
% 9.14/3.27  tff(c_5422, plain, (![D_519, C_520, A_521, B_522]: (D_519=C_520 | ~r2_relset_1(A_521, B_522, C_520, D_519) | ~m1_subset_1(D_519, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.27  tff(c_5430, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_5422])).
% 9.14/3.27  tff(c_5445, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5430])).
% 9.14/3.27  tff(c_5489, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5445])).
% 9.14/3.27  tff(c_6895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6718, c_6365, c_5489])).
% 9.14/3.27  tff(c_6896, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5445])).
% 9.14/3.27  tff(c_7539, plain, (![C_46, A_44, B_45, D_47, E_49]: (C_46='#skF_4' | v2_funct_1(D_47) | ~v2_funct_1(k1_partfun1(A_44, B_45, B_45, C_46, D_47, E_49)) | ~m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~v1_funct_2(E_49, B_45, C_46) | ~v1_funct_1(E_49) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47))), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_64])).
% 9.14/3.27  tff(c_7857, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6896, c_7539])).
% 9.14/3.27  tff(c_7864, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_7857])).
% 9.14/3.27  tff(c_7866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_5005, c_7864])).
% 9.14/3.27  tff(c_7868, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_212])).
% 9.14/3.27  tff(c_7885, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_7868])).
% 9.14/3.27  tff(c_7887, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7885, c_76])).
% 9.14/3.27  tff(c_40, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.14/3.27  tff(c_8017, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7887, c_40])).
% 9.14/3.27  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.14/3.27  tff(c_268, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_258, c_26])).
% 9.14/3.27  tff(c_294, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_268])).
% 9.14/3.27  tff(c_7869, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_294])).
% 9.14/3.27  tff(c_4987, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_276])).
% 9.14/3.27  tff(c_7895, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_4987])).
% 9.14/3.27  tff(c_7888, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7885, c_70])).
% 9.14/3.27  tff(c_9228, plain, (![F_823, E_825, B_822, A_821, C_826, D_824]: (k1_partfun1(A_821, B_822, C_826, D_824, E_825, F_823)=k5_relat_1(E_825, F_823) | ~m1_subset_1(F_823, k1_zfmisc_1(k2_zfmisc_1(C_826, D_824))) | ~v1_funct_1(F_823) | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(A_821, B_822))) | ~v1_funct_1(E_825))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_9232, plain, (![A_821, B_822, E_825]: (k1_partfun1(A_821, B_822, '#skF_2', '#skF_4', E_825, '#skF_4')=k5_relat_1(E_825, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(A_821, B_822))) | ~v1_funct_1(E_825))), inference(resolution, [status(thm)], [c_7888, c_9228])).
% 9.14/3.27  tff(c_9614, plain, (![A_851, B_852, E_853]: (k1_partfun1(A_851, B_852, '#skF_2', '#skF_4', E_853, '#skF_4')=k5_relat_1(E_853, '#skF_4') | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))) | ~v1_funct_1(E_853))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9232])).
% 9.14/3.27  tff(c_9626, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7887, c_9614])).
% 9.14/3.27  tff(c_9639, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9626])).
% 9.14/3.27  tff(c_9745, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9639, c_50])).
% 9.14/3.27  tff(c_9749, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7887, c_74, c_7888, c_9745])).
% 9.14/3.27  tff(c_178, plain, (![A_62]: (k1_xboole_0!=A_62 | k6_partfun1(A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_164])).
% 9.14/3.27  tff(c_184, plain, (![A_62]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))) | k1_xboole_0!=A_62)), inference(superposition, [status(thm), theory('equality')], [c_178, c_56])).
% 9.14/3.27  tff(c_8272, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_4986, c_184])).
% 9.14/3.27  tff(c_7974, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4986, c_4986, c_171])).
% 9.14/3.27  tff(c_7886, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7885, c_7885, c_7885, c_7885, c_7885, c_68])).
% 9.14/3.27  tff(c_8139, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7974, c_7886])).
% 9.14/3.27  tff(c_8880, plain, (![D_783, C_784, A_785, B_786]: (D_783=C_784 | ~r2_relset_1(A_785, B_786, C_784, D_783) | ~m1_subset_1(D_783, k1_zfmisc_1(k2_zfmisc_1(A_785, B_786))) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_zfmisc_1(A_785, B_786))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.27  tff(c_8894, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_8139, c_8880])).
% 9.14/3.27  tff(c_8917, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8272, c_8894])).
% 9.14/3.27  tff(c_8978, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_8917])).
% 9.14/3.27  tff(c_10414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9749, c_9639, c_8978])).
% 9.14/3.27  tff(c_10415, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_8917])).
% 9.14/3.27  tff(c_10551, plain, (![C_909, E_908, D_907, B_905, A_904, F_906]: (k1_partfun1(A_904, B_905, C_909, D_907, E_908, F_906)=k5_relat_1(E_908, F_906) | ~m1_subset_1(F_906, k1_zfmisc_1(k2_zfmisc_1(C_909, D_907))) | ~v1_funct_1(F_906) | ~m1_subset_1(E_908, k1_zfmisc_1(k2_zfmisc_1(A_904, B_905))) | ~v1_funct_1(E_908))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_10555, plain, (![A_904, B_905, E_908]: (k1_partfun1(A_904, B_905, '#skF_2', '#skF_4', E_908, '#skF_4')=k5_relat_1(E_908, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_908, k1_zfmisc_1(k2_zfmisc_1(A_904, B_905))) | ~v1_funct_1(E_908))), inference(resolution, [status(thm)], [c_7888, c_10551])).
% 9.14/3.27  tff(c_10860, plain, (![A_937, B_938, E_939]: (k1_partfun1(A_937, B_938, '#skF_2', '#skF_4', E_939, '#skF_4')=k5_relat_1(E_939, '#skF_4') | ~m1_subset_1(E_939, k1_zfmisc_1(k2_zfmisc_1(A_937, B_938))) | ~v1_funct_1(E_939))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10555])).
% 9.14/3.27  tff(c_10872, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7887, c_10860])).
% 9.14/3.27  tff(c_10885, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10415, c_10872])).
% 9.14/3.27  tff(c_20, plain, (![A_12, B_14]: (r1_tarski(k1_relat_1(k5_relat_1(A_12, B_14)), k1_relat_1(A_12)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.14/3.27  tff(c_10902, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10885, c_20])).
% 9.14/3.27  tff(c_10914, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_261, c_7895, c_10902])).
% 9.14/3.27  tff(c_10923, plain, (k1_relat_1('#skF_3')='#skF_4' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_10914, c_2])).
% 9.14/3.27  tff(c_10929, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_7869, c_10923])).
% 9.14/3.27  tff(c_10982, plain, (~v4_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_10929])).
% 9.14/3.27  tff(c_10988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_8017, c_10982])).
% 9.14/3.27  tff(c_10989, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_268])).
% 9.14/3.27  tff(c_125, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_81])).
% 9.14/3.27  tff(c_11016, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10989, c_125])).
% 9.14/3.27  tff(c_11020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_11016])).
% 9.14/3.27  tff(c_11021, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 9.14/3.27  tff(c_11105, plain, (![B_949, A_950]: (v1_relat_1(B_949) | ~m1_subset_1(B_949, k1_zfmisc_1(A_950)) | ~v1_relat_1(A_950))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.14/3.27  tff(c_11117, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_11105])).
% 9.14/3.27  tff(c_11129, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11117])).
% 9.14/3.27  tff(c_11165, plain, (![C_953, B_954, A_955]: (v5_relat_1(C_953, B_954) | ~m1_subset_1(C_953, k1_zfmisc_1(k2_zfmisc_1(A_955, B_954))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.14/3.27  tff(c_11181, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_11165])).
% 9.14/3.27  tff(c_11114, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_11105])).
% 9.14/3.27  tff(c_11126, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11114])).
% 9.14/3.27  tff(c_11905, plain, (![F_1045, B_1044, E_1047, D_1046, A_1043, C_1048]: (k1_partfun1(A_1043, B_1044, C_1048, D_1046, E_1047, F_1045)=k5_relat_1(E_1047, F_1045) | ~m1_subset_1(F_1045, k1_zfmisc_1(k2_zfmisc_1(C_1048, D_1046))) | ~v1_funct_1(F_1045) | ~m1_subset_1(E_1047, k1_zfmisc_1(k2_zfmisc_1(A_1043, B_1044))) | ~v1_funct_1(E_1047))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_11913, plain, (![A_1043, B_1044, E_1047]: (k1_partfun1(A_1043, B_1044, '#skF_2', '#skF_1', E_1047, '#skF_4')=k5_relat_1(E_1047, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1047, k1_zfmisc_1(k2_zfmisc_1(A_1043, B_1044))) | ~v1_funct_1(E_1047))), inference(resolution, [status(thm)], [c_70, c_11905])).
% 9.14/3.27  tff(c_12305, plain, (![A_1088, B_1089, E_1090]: (k1_partfun1(A_1088, B_1089, '#skF_2', '#skF_1', E_1090, '#skF_4')=k5_relat_1(E_1090, '#skF_4') | ~m1_subset_1(E_1090, k1_zfmisc_1(k2_zfmisc_1(A_1088, B_1089))) | ~v1_funct_1(E_1090))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_11913])).
% 9.14/3.27  tff(c_12323, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_12305])).
% 9.14/3.27  tff(c_12338, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12323])).
% 9.14/3.27  tff(c_12689, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12338, c_50])).
% 9.14/3.27  tff(c_12696, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_12689])).
% 9.14/3.27  tff(c_11626, plain, (![D_1009, C_1010, A_1011, B_1012]: (D_1009=C_1010 | ~r2_relset_1(A_1011, B_1012, C_1010, D_1009) | ~m1_subset_1(D_1009, k1_zfmisc_1(k2_zfmisc_1(A_1011, B_1012))) | ~m1_subset_1(C_1010, k1_zfmisc_1(k2_zfmisc_1(A_1011, B_1012))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.27  tff(c_11640, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_11626])).
% 9.14/3.27  tff(c_11663, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11640])).
% 9.14/3.27  tff(c_11721, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11663])).
% 9.14/3.27  tff(c_12766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12696, c_12338, c_11721])).
% 9.14/3.27  tff(c_12767, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_11663])).
% 9.14/3.27  tff(c_13030, plain, (![A_1132, E_1136, D_1135, F_1134, C_1137, B_1133]: (k1_partfun1(A_1132, B_1133, C_1137, D_1135, E_1136, F_1134)=k5_relat_1(E_1136, F_1134) | ~m1_subset_1(F_1134, k1_zfmisc_1(k2_zfmisc_1(C_1137, D_1135))) | ~v1_funct_1(F_1134) | ~m1_subset_1(E_1136, k1_zfmisc_1(k2_zfmisc_1(A_1132, B_1133))) | ~v1_funct_1(E_1136))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.27  tff(c_13038, plain, (![A_1132, B_1133, E_1136]: (k1_partfun1(A_1132, B_1133, '#skF_2', '#skF_1', E_1136, '#skF_4')=k5_relat_1(E_1136, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1136, k1_zfmisc_1(k2_zfmisc_1(A_1132, B_1133))) | ~v1_funct_1(E_1136))), inference(resolution, [status(thm)], [c_70, c_13030])).
% 9.14/3.27  tff(c_13280, plain, (![A_1165, B_1166, E_1167]: (k1_partfun1(A_1165, B_1166, '#skF_2', '#skF_1', E_1167, '#skF_4')=k5_relat_1(E_1167, '#skF_4') | ~m1_subset_1(E_1167, k1_zfmisc_1(k2_zfmisc_1(A_1165, B_1166))) | ~v1_funct_1(E_1167))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_13038])).
% 9.14/3.27  tff(c_13292, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_13280])).
% 9.14/3.27  tff(c_13301, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12767, c_13292])).
% 9.14/3.27  tff(c_13311, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13301, c_22])).
% 9.14/3.27  tff(c_13317, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11126, c_11129, c_83, c_13311])).
% 9.14/3.27  tff(c_13336, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_13317, c_2])).
% 9.14/3.27  tff(c_13427, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_13336])).
% 9.14/3.27  tff(c_13433, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_13427])).
% 9.14/3.27  tff(c_13438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11129, c_11181, c_13433])).
% 9.14/3.27  tff(c_13439, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_13336])).
% 9.14/3.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.14/3.27  tff(c_11258, plain, (![B_967, A_968]: (v5_relat_1(B_967, A_968) | ~r1_tarski(k2_relat_1(B_967), A_968) | ~v1_relat_1(B_967))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.14/3.27  tff(c_11277, plain, (![B_967]: (v5_relat_1(B_967, k2_relat_1(B_967)) | ~v1_relat_1(B_967))), inference(resolution, [status(thm)], [c_6, c_11258])).
% 9.14/3.27  tff(c_11354, plain, (![B_980]: (v2_funct_2(B_980, k2_relat_1(B_980)) | ~v5_relat_1(B_980, k2_relat_1(B_980)) | ~v1_relat_1(B_980))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.14/3.27  tff(c_11375, plain, (![B_967]: (v2_funct_2(B_967, k2_relat_1(B_967)) | ~v1_relat_1(B_967))), inference(resolution, [status(thm)], [c_11277, c_11354])).
% 9.14/3.27  tff(c_13450, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13439, c_11375])).
% 9.14/3.27  tff(c_13465, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11129, c_13450])).
% 9.14/3.27  tff(c_13467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11021, c_13465])).
% 9.14/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.14/3.27  
% 9.14/3.27  Inference rules
% 9.14/3.27  ----------------------
% 9.14/3.27  #Ref     : 5
% 9.14/3.27  #Sup     : 2756
% 9.14/3.27  #Fact    : 0
% 9.14/3.27  #Define  : 0
% 9.14/3.27  #Split   : 67
% 9.14/3.27  #Chain   : 0
% 9.14/3.27  #Close   : 0
% 9.14/3.27  
% 9.14/3.27  Ordering : KBO
% 9.14/3.27  
% 9.14/3.27  Simplification rules
% 9.14/3.27  ----------------------
% 9.14/3.27  #Subsume      : 704
% 9.14/3.27  #Demod        : 2364
% 9.14/3.27  #Tautology    : 766
% 9.14/3.27  #SimpNegUnit  : 81
% 9.14/3.27  #BackRed      : 133
% 9.14/3.27  
% 9.14/3.27  #Partial instantiations: 0
% 9.14/3.27  #Strategies tried      : 1
% 9.14/3.27  
% 9.14/3.27  Timing (in seconds)
% 9.14/3.27  ----------------------
% 9.14/3.27  Preprocessing        : 0.35
% 9.14/3.27  Parsing              : 0.19
% 9.14/3.27  CNF conversion       : 0.02
% 9.14/3.27  Main loop            : 2.11
% 9.14/3.27  Inferencing          : 0.66
% 9.14/3.27  Reduction            : 0.82
% 9.14/3.27  Demodulation         : 0.60
% 9.14/3.27  BG Simplification    : 0.06
% 9.14/3.27  Subsumption          : 0.40
% 9.14/3.27  Abstraction          : 0.08
% 9.14/3.27  MUC search           : 0.00
% 9.14/3.27  Cooper               : 0.00
% 9.14/3.27  Total                : 2.53
% 9.14/3.27  Index Insertion      : 0.00
% 9.14/3.27  Index Deletion       : 0.00
% 9.14/3.27  Index Matching       : 0.00
% 9.14/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
